
import "../src/lib" / [nifreader, niftree]

const
  ExpectedOutput = """
(stmts
 (comment
 (import
 (import
 (when
 (importExcept
 (from
 (from
 (from
 (const
 (when
 (proc
 (proc
 (when
 (template
 (proc
 (when
 (proc
 (template
 (template
 (template
 (template
 (template
 (template
 (template
 (proc
 (proc
 (include
 (template
 (template
 (proc
 (template
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (template
 (proc
 (proc
 (type
 (proc
 (proc
 (proc
 (proc
 (template
 (proc
 (proc
 (const
 (const
 (const
 (const
 (const
 (const
 (template
 (template
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (include
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (proc
 (iterator
 (const
 (proc
"""

proc outline*(n: NifTree): string =
  result = $n.tok & "\n"
  var it = n.down
  while it != nil:
    result.add " " & $it.tok & "\n"
    it = it.next

proc test*(filename: string) =
  var r = nifreader.open(filename)
  let res = processDirectives(r)
  assert res == Success
  let firstTok = next(r)
  let t = parse(r, firstTok)
  assert outline(t) == ExpectedOutput
  r.close()

test "tests/data/vm.nif"
