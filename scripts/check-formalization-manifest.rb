#!/usr/bin/env ruby
# Validate formalization.yaml against the repository.
#
# Metadata checks (no Lean):
# * project.lean_toolchain, comparator toolchain and every workspace's lean-toolchain equal the
#   root lean-toolchain; project.mathlib and the comparator mathlib equal the Mathlib inputRev
#   locked in lake-manifest.json, and every workspace manifest locks the root's git revisions;
# * every target's lean_file exists and declares the target's lean_name;
# * the challenge inventory (comparator.external_challenges.entries) equals
#   challenges/*/config.json; each workspace is complete, its Statement.lean imports only Mathlib,
#   its Challenge.lean only Statement, and its Solution.lean only Statement,
#   AleksandrovDifferentiability and Mathlib modules; config theorem names and permitted axioms agree;
# * the pinned Comparator tool revisions agree with scripts/release-comparator.sh.
#
# Lean checks (after `lake build`): every target and API smoke-test name resolves, and each target
# depends on exactly axioms.expected.
#
# Usage: ruby scripts/check-formalization-manifest.rb [--metadata-only]
require 'yaml'
require 'json'
require 'open3'
require 'tempfile'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
LEAN_NAME = /\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/
DECL_PREFIX = /^(?:@\[[^\]]*\]\s*)?(?:(?:public|protected|private|noncomputable) )*(?:theorem|lemma|def|abbrev|structure) /
metadata_only = ARGV == ['--metadata-only']
abort 'usage: check-formalization-manifest.rb [--metadata-only]' unless ARGV.empty? || metadata_only
Dir.chdir(ROOT)
failures = []

manifest = YAML.safe_load_file('formalization.yaml')
abort 'formalization.yaml must be a mapping' unless manifest.is_a?(Hash)
expected_axioms = manifest.fetch('axioms').fetch('expected')
abort 'axioms.expected must be a nonempty list' unless expected_axioms.is_a?(Array) && !expected_axioms.empty?
targets = manifest.fetch('targets')
abort 'targets must be a nonempty list' unless targets.is_a?(Array) && !targets.empty?
abort 'duplicate target id' unless targets.map { |t| t.fetch('id') }.uniq.length == targets.length

# Toolchain and Mathlib agree with lean-toolchain and lake-manifest.json.
root_toolchain = File.read('lean-toolchain').strip
git_packages = lambda do |file|
  JSON.parse(File.read(file)).fetch('packages').select { |p| p['type'] == 'git' }
      .to_h { |p| [p['name'], [p['rev'], p['inputRev']]] }
end
locked = git_packages.call('lake-manifest.json')
mathlib_input = locked.fetch('mathlib')[1]
project = manifest.fetch('project')
failures << 'project.lean_toolchain differs from lean-toolchain' unless project['lean_toolchain'] == root_toolchain
failures << "project.mathlib differs from the locked Mathlib inputRev #{mathlib_input.inspect}" \
  unless project['mathlib'] == mathlib_input

# Targets.
targets.each do |t|
  id = t.fetch('id')
  name = t['lean_name'].to_s
  failures << "#{id}: invalid Lean name #{name.inspect}" unless name.match?(LEAN_NAME)
  file = t['lean_file'].to_s
  if !File.file?(file)
    failures << "#{id}: lean_file #{file.inspect} does not exist"
  else
    short = name.sub(/\AAleksandrovDifferentiability\./, '')
    failures << "#{id}: #{file} does not declare #{name}" \
      unless File.read(file).match?(/#{DECL_PREFIX}#{Regexp.escape(short)}(?=[\s:({\[]|\z)/)
  end
end

# External challenge inventory.
external = manifest.fetch('comparator').fetch('external_challenges')
entries = external.fetch('entries')
allowed = external.fetch('permitted_axioms')
abort 'comparator.external_challenges.entries must be a nonempty list' unless entries.is_a?(Array) && !entries.empty?
abort 'duplicate challenge id' unless entries.map { |e| e.fetch('id') }.uniq.length == entries.length
failures << 'comparator permitted_axioms differ from axioms.expected' unless allowed.sort == expected_axioms.sort
failures << "external_challenges.toolchain #{external['toolchain'].inspect} differs from lean-toolchain" \
  unless external['toolchain'] == root_toolchain
failures << "external_challenges.mathlib #{external['mathlib'].inspect} differs from the locked Mathlib inputRev" \
  unless external['mathlib'] == mathlib_input

listed = entries.map { |e| e.fetch('path') }.sort
on_disk = Dir.glob("#{external.fetch('directory')}/*/config.json").map { |c| File.dirname(c) }.sort
unless listed == on_disk
  failures << "challenge inventory differs from formalization.yaml: " \
              "#{(on_disk - listed).inspect} unlisted, #{(listed - on_disk).inspect} missing"
end
targets.each do |t|
  next unless t['challenge']
  failures << "#{t['id']}: challenge #{t['challenge']} is not an external challenge entry" \
    unless listed.include?(t['challenge'])
end

imports = ->(f) { File.file?(f) ? File.read(f).scan(/^\s*import\s+(\S+)/).flatten : [] }
mathlib = ->(m) { m == 'Mathlib' || m.start_with?('Mathlib.') }
library = ->(m) { m == 'AleksandrovDifferentiability' || m.start_with?('AleksandrovDifferentiability.') }

entries.each do |entry|
  path = entry.fetch('path')
  next unless File.directory?(path)
  %w[Statement.lean Challenge.lean Solution.lean config.json lakefile.toml lake-manifest.json lean-toolchain].each do |f|
    failures << "#{path}: missing #{f}" unless File.file?(File.join(path, f))
  end
  toolchain = File.join(path, 'lean-toolchain')
  failures << "#{path}: lean-toolchain differs from the root lean-toolchain" \
    if File.file?(toolchain) && File.read(toolchain).strip != root_toolchain
  workspace_manifest = File.join(path, 'lake-manifest.json')
  failures << "#{path}: lake-manifest.json locks different git revisions from the root" \
    if File.file?(workspace_manifest) && git_packages.call(workspace_manifest) != locked
  bad = imports.call(File.join(path, 'Statement.lean')).reject(&mathlib)
  failures << "#{path}/Statement.lean: imports outside Mathlib: #{bad.inspect}" unless bad.empty?
  bad = imports.call(File.join(path, 'Challenge.lean')) - ['Statement']
  failures << "#{path}/Challenge.lean: imports other than Statement: #{bad.inspect}" unless bad.empty?
  bad = imports.call(File.join(path, 'Solution.lean')).reject { |m| m == 'Statement' || library.call(m) || mathlib.call(m) }
  failures << "#{path}/Solution.lean: imports outside Statement, the library and Mathlib: #{bad.inspect}" unless bad.empty?
  lakefile = File.join(path, 'lakefile.toml')
  if File.file?(lakefile)
    defaults = File.read(lakefile)[/^defaultTargets\s*=\s*\[([^\]]*)\]/, 1].to_s
    failures << "#{path}: Solution must not be a default target" if defaults.include?('Solution')
  end
  config_path = File.join(path, 'config.json')
  next unless File.file?(config_path)
  config = JSON.parse(File.read(config_path))
  failures << "#{path}: theorem_names differ from formalization.yaml" \
    unless config.fetch('theorem_names') == [entry.fetch('theorem_name')]
  failures << "#{path}: permitted_axioms differ from formalization.yaml" \
    unless config.fetch('permitted_axioms').sort == allowed.sort
  failures << "#{path}: unexpected challenge module" unless config.fetch('challenge_module') == 'Challenge'
  failures << "#{path}: unexpected solution module" unless config.fetch('solution_module') == 'Solution'
end

driver = File.read('scripts/release-comparator.sh')
{ 'comparator_revision' => 'COMPARATOR_REV',
  'lean4export_revision' => 'LEAN4EXPORT_REV',
  'landrun_revision' => 'LANDRUN_REV' }.each do |key, var|
  pinned = driver[/^#{var}=(\h+)$/, 1]
  failures << "#{key} #{external[key].inspect} differs from #{var} in scripts/release-comparator.sh" \
    unless pinned && external[key] == pinned
end

abort failures.join("\n") unless failures.empty?
if metadata_only
  puts "Validated #{targets.length} targets and #{entries.length} challenge workspaces (metadata only)"
  exit 0
end

# Lean: one invocation resolves every name and prints the axioms of every target.
target_names = targets.map { |t| t.fetch('lean_name') }
smoke = manifest.fetch('comparator').fetch('api_smoke_challenges', {}).fetch('challenges', [])
smoke_names = smoke.map { |c| c.fetch('lean_name') }
Tempfile.create(['manifest-check-', '.lean']) do |file|
  file.puts 'import AleksandrovDifferentiability'
  file.puts 'import AleksandrovDifferentiability.Comparator'
  (target_names + smoke_names).uniq.each { |n| file.puts "#check @#{n}" }
  target_names.each_with_index do |n, i|
    file.puts %Q(#eval IO.println "AXIOMS_BEGIN_#{i}")
    file.puts "#print axioms #{n}"
    file.puts %Q(#eval IO.println "AXIOMS_END_#{i}")
  end
  file.flush
  output, status = Open3.capture2e('lake', 'env', 'lean', file.path)
  output.force_encoding(Encoding::UTF_8)
  unless status.success?
    warn output
    abort 'Lean name resolution or axiom check failed'
  end
  target_names.each_with_index do |name, i|
    section = output[/AXIOMS_BEGIN_#{i}(.*?)AXIOMS_END_#{i}/m, 1]
    abort "missing #print axioms output for #{name}" unless section
    actual = if section.include?('does not depend on any axioms')
               []
             else
               block = section[/depends on axioms: \[([^\]]*)\]/, 1]
               abort "unrecognized #print axioms output for #{name}: #{section}" unless block
               block.split(',').map(&:strip).uniq
             end
    # Statement-level definitions may use no axioms at all.
    failures << "#{name}: axioms #{actual.sort.inspect}, expected #{expected_axioms.sort.inspect} (or none)" \
      unless actual.empty? || actual.sort == expected_axioms.sort
  end
end
abort failures.join("\n") unless failures.empty?
puts "Validated #{targets.length} targets (axioms exactly #{expected_axioms.sort.inspect} or none), " \
     "#{smoke_names.length} API smoke-test names, and #{entries.length} challenge workspaces"
