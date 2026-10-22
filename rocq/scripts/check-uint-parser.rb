# Run inside the pinned opam switch, after the predicative build. This tests
# the real source Numeric.Uint, not an independently reconstructed parser.
require 'fileutils'
require 'open3'

root = File.expand_path('../..', __dir__)
build = File.expand_path(ARGV.fetch(0))
directory = File.join(root, '_build', 'uint-parser-differential')
FileUtils.mkdir_p(directory)

def run!(*command, directory:)
  out, err, status = Open3.capture3(*command, chdir: directory)
  raise "#{command.join(' ')}\n#{out}\n#{err}" unless status.success?
  out
end

inputs = ['', '+', '-', '-+', '_1', '0x_f', '0b2', '0o8', '0u42', ' 1', '1 ',
          '1__', '0Xf__f', '-+0xF', '0x', '+0b11', '-0o77', '--1', '++1']
[-(2**300), -123, -1, 0, 1, 123, 2**300].each do |n|
  inputs << n.to_s
  %w[+ - -+].each { |sign| inputs << sign + n.abs.to_s }
  [[2, 'b'], [8, 'o'], [16, 'x']].each do |base, prefix|
    ['', '+', '-', '-+'].each do |sign|
      inputs << "#{sign}0#{prefix}#{n.abs.to_s(base)}"
    end
  end
end
inputs.uniq!
output = run!('dune', 'exec', '--root', root, '--pkg=disabled',
              'rocq/tests/native/uint_parser.exe', '--', *inputs, directory: root)
expected = output.lines.map(&:strip)
raise 'oracle result count mismatch' unless inputs.length == expected.length

proofs = inputs.zip(expected).each_with_index.map do |(input, result), i|
  # Invalid native inputs exercise the existing explicit N fallback. This is
  # not a claim to model exception handlers in Gallina.
  value = result == 'Error' ? 987654321 : Integer(result)
  "Example parse_#{i} : UintN.of_string \"#{input}\" = #{value}%N.\n" \
    "Proof. vm_compute. reflexivity. Qed.\n"
end
File.write(File.join(directory, 'Check.v'), <<~COQ + proofs.join("\n"))
  Require Import RocqOfOCaml.RocqOfOCaml MonadVM.Support.UintN.
  Open Scope string_scope.
  #[local] Instance fallback_z : Unreachable Z := {| unreachable := 123456789%Z |}.
  #[local] Instance fallback_n : Unreachable N := {| unreachable := 987654321%N |}.
COQ
run!('rocq', 'c', '-Q', File.join(build, 'runtime/proofs'), 'RocqOfOCaml',
     '-Q', File.join(build, 'generated'), 'MonadVM',
     '-Q', File.join(build, 'support'), 'MonadVM.Support',
     '-Q', File.join(build, 'project-proofs'), 'MonadExecutionSpecs',
     'Check.v', directory: directory)
puts "Uint parser differential tests: #{inputs.length} native/model results agree."
