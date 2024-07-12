
import "../src/lib" / [nifreader, nif_linkedtree]

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
  let t = parse(r)
  assert outline(t) == ExpectedOutput
  r.close()

const
  SubsResult = """
(stmts
 (call
  Symbol:echo.1.sys StringLit:Hello World!\0A) (call
  Symbol:echo.1.sys StringLit:different string))"""

proc subsTest(filename: string): string =
  var r = nifreader.open(filename)
  let res = processDirectives(r)
  assert res == Success
  let t = parse(r)
  result = $t
  r.close()

test "tests/data/vm.nif"

let st = subsTest("tests/data/tsubs.nif")
assert st == SubsResult
