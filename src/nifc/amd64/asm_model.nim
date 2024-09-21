# GENERATED BY NifGram. DO NOT EDIT!
# ORIGINAL FILE: src/nifc/amd64/asm_grammar.nif
import nifstreams

const
  GlobalT* = TagId(3)
  TextT* = TagId(4)
  ExternT* = TagId(5)
  TimesT* = TagId(6)
  DbT* = TagId(7)
  DwT* = TagId(8)
  DdT* = TagId(9)
  DqT* = TagId(10)
  DataT* = TagId(11)
  RodataT* = TagId(12)
  StmtsT* = TagId(13)
  RaxT* = TagId(14)
  RbxT* = TagId(15)
  RcxT* = TagId(16)
  RdxT* = TagId(17)
  RsiT* = TagId(18)
  RdiT* = TagId(19)
  RbpT* = TagId(20)
  RspT* = TagId(21)
  R8T* = TagId(22)
  R9T* = TagId(23)
  R10T* = TagId(24)
  R11T* = TagId(25)
  R12T* = TagId(26)
  R13T* = TagId(27)
  R14T* = TagId(28)
  R15T* = TagId(29)
  Xmm0T* = TagId(30)
  Xmm1T* = TagId(31)
  Xmm2T* = TagId(32)
  Xmm3T* = TagId(33)
  Xmm4T* = TagId(34)
  Xmm6T* = TagId(35)
  Xmm7T* = TagId(36)
  Xmm8T* = TagId(37)
  Xmm9T* = TagId(38)
  Xmm10T* = TagId(39)
  Xmm11T* = TagId(40)
  Xmm12T* = TagId(41)
  Xmm13T* = TagId(42)
  Xmm14T* = TagId(43)
  Xmm15T* = TagId(44)
  RelT* = TagId(45)
  FsT* = TagId(46)
  Mem1T* = TagId(47)
  Mem2T* = TagId(48)
  Mem3T* = TagId(49)
  ByteatT* = TagId(50)
  WordatT* = TagId(51)
  MovT* = TagId(52)
  MovapdT* = TagId(53)
  MovsdT* = TagId(54)
  LeaT* = TagId(55)
  AddT* = TagId(56)
  SubT* = TagId(57)
  MulT* = TagId(58)
  ImulT* = TagId(59)
  DivT* = TagId(60)
  IdivT* = TagId(61)
  XorT* = TagId(62)
  AddsdT* = TagId(63)
  SubsdT* = TagId(64)
  MulsdT* = TagId(65)
  DivsdT* = TagId(66)
  PushT* = TagId(67)
  PopT* = TagId(68)
  IncT* = TagId(69)
  DecT* = TagId(70)
  NegT* = TagId(71)
  CmpT* = TagId(72)
  TestT* = TagId(73)
  CallT* = TagId(74)
  LabT* = TagId(75)
  JmpT* = TagId(76)
  JeT* = TagId(77)
  JneT* = TagId(78)
  JzT* = TagId(79)
  JnzT* = TagId(80)
  JgT* = TagId(81)
  JgeT* = TagId(82)
  JaT* = TagId(83)
  JaeT* = TagId(84)
  NopT* = TagId(85)
  RetT* = TagId(86)
  SyscallT* = TagId(87)
  CommentT* = TagId(88)

proc registerTags*() =
  registerTag "global", GlobalT
  registerTag "text", TextT
  registerTag "extern", ExternT
  registerTag "times", TimesT
  registerTag "db", DbT
  registerTag "dw", DwT
  registerTag "dd", DdT
  registerTag "dq", DqT
  registerTag "data", DataT
  registerTag "rodata", RodataT
  registerTag "stmts", StmtsT
  registerTag "rax", RaxT
  registerTag "rbx", RbxT
  registerTag "rcx", RcxT
  registerTag "rdx", RdxT
  registerTag "rsi", RsiT
  registerTag "rdi", RdiT
  registerTag "rbp", RbpT
  registerTag "rsp", RspT
  registerTag "r8", R8T
  registerTag "r9", R9T
  registerTag "r10", R10T
  registerTag "r11", R11T
  registerTag "r12", R12T
  registerTag "r13", R13T
  registerTag "r14", R14T
  registerTag "r15", R15T
  registerTag "xmm0", Xmm0T
  registerTag "xmm1", Xmm1T
  registerTag "xmm2", Xmm2T
  registerTag "xmm3", Xmm3T
  registerTag "xmm4", Xmm4T
  registerTag "xmm6", Xmm6T
  registerTag "xmm7", Xmm7T
  registerTag "xmm8", Xmm8T
  registerTag "xmm9", Xmm9T
  registerTag "xmm10", Xmm10T
  registerTag "xmm11", Xmm11T
  registerTag "xmm12", Xmm12T
  registerTag "xmm13", Xmm13T
  registerTag "xmm14", Xmm14T
  registerTag "xmm15", Xmm15T
  registerTag "rel", RelT
  registerTag "fs", FsT
  registerTag "mem1", Mem1T
  registerTag "mem2", Mem2T
  registerTag "mem3", Mem3T
  registerTag "byteat", ByteatT
  registerTag "wordat", WordatT
  registerTag "mov", MovT
  registerTag "movapd", MovapdT
  registerTag "movsd", MovsdT
  registerTag "lea", LeaT
  registerTag "add", AddT
  registerTag "sub", SubT
  registerTag "mul", MulT
  registerTag "imul", ImulT
  registerTag "div", DivT
  registerTag "idiv", IdivT
  registerTag "xor", XorT
  registerTag "addsd", AddsdT
  registerTag "subsd", SubsdT
  registerTag "mulsd", MulsdT
  registerTag "divsd", DivsdT
  registerTag "push", PushT
  registerTag "pop", PopT
  registerTag "inc", IncT
  registerTag "dec", DecT
  registerTag "neg", NegT
  registerTag "cmp", CmpT
  registerTag "test", TestT
  registerTag "call", CallT
  registerTag "lab", LabT
  registerTag "jmp", JmpT
  registerTag "je", JeT
  registerTag "jne", JneT
  registerTag "jz", JzT
  registerTag "jnz", JnzT
  registerTag "jg", JgT
  registerTag "jge", JgeT
  registerTag "ja", JaT
  registerTag "jae", JaeT
  registerTag "nop", NopT
  registerTag "ret", RetT
  registerTag "syscall", SyscallT
  registerTag "comment", CommentT