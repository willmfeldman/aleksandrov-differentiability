#!/usr/bin/env ruby
# Validate the Comparator challenge inventory against formalization.yaml:
# the listed entries are exactly the challenge workspaces on disk, each
# workspace is complete and on the root toolchain, each config.json names the
# listed theorem with the permitted-axiom policy, and the pinned tool
# revisions agree with scripts/release-comparator.sh.  Metadata only; this
# never runs Lean.
require 'yaml'
require 'json'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
Dir.chdir(ROOT)
failures = []

manifest = YAML.safe_load_file('formalization.yaml')
external = manifest.fetch('comparator').fetch('external_challenges')
entries = external.fetch('entries')
allowed = external.fetch('permitted_axioms')
abort 'comparator.external_challenges.entries must be a nonempty list' unless entries.is_a?(Array) && !entries.empty?
abort 'duplicate challenge id' unless entries.map { |e| e.fetch('id') }.uniq.length == entries.length
unless allowed.sort == manifest.fetch('axioms').fetch('expected').sort
  failures << 'comparator permitted_axioms differ from axioms.expected'
end

listed = entries.map { |e| e.fetch('path') }.sort
on_disk = Dir.glob('challenges/*/config.json').map { |c| File.dirname(c) }.sort
unless listed == on_disk
  failures << "challenge inventory differs from formalization.yaml: " \
              "#{(on_disk - listed).inspect} unlisted, #{(listed - on_disk).inspect} missing"
end

root_toolchain = File.read('lean-toolchain').strip
failures << "external_challenges.toolchain #{external['toolchain'].inspect} differs from lean-toolchain" \
  unless external['toolchain'] == root_toolchain

entries.each do |entry|
  path = entry.fetch('path')
  next unless File.directory?(path)
  %w[Statement.lean Challenge.lean Solution.lean config.json lakefile.toml lake-manifest.json lean-toolchain].each do |f|
    failures << "#{path}: missing #{f}" unless File.file?(File.join(path, f))
  end
  toolchain = File.join(path, 'lean-toolchain')
  if File.file?(toolchain) && File.read(toolchain).strip != root_toolchain
    failures << "#{path}: lean-toolchain differs from the root lean-toolchain"
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
puts "Validated #{entries.length} Comparator challenge workspaces"
