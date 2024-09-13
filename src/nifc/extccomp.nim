import std/strutils
import noptions

type
  InfoCCProp* = enum         # properties of the C compiler:
    hasSwitchRange,           # CC allows ranges in switch statements (GNU C)
    hasComputedGoto,          # CC has computed goto (GNU C extension)
    hasCpp,                   # CC is/contains a C++ compiler
    hasAssume,                # CC has __assume (Visual C extension)
    hasGcGuard,               # CC supports GC_GUARD to keep stack roots
    hasGnuAsm,                # CC's asm uses the absurd GNU assembler syntax
    hasDeclspec,              # CC has __declspec(X)
    hasAttribute,             # CC has __attribute__((X))
    hasBuiltinUnreachable     # CC has __builtin_unreachable
  InfoCCProps* = set[InfoCCProp]
  InfoCC* = tuple[
    name: string,        # the short name of the compiler
    objExt: string,      # the compiler's object file extension
    optSpeed: string,    # the options for optimization for speed
    optSize: string,     # the options for optimization for size
    compilerExe: string, # the compiler's executable
    cppCompiler: string, # name of the C++ compiler's executable (if supported)
    compileTmpl: string, # the compile command template
    buildGui: string,    # command to build a GUI application
    buildDll: string,    # command to build a shared library
    buildLib: string,    # command to build a static library
    linkerExe: string,   # the linker's executable (if not matching compiler's)
    linkTmpl: string,    # command to link files to produce an exe
    includeCmd: string,  # command to add an include dir
    linkDirCmd: string,  # command to add a lib dir
    linkLibCmd: string,  # command to link an external library
    debug: string,       # flags for debug build
    pic: string,         # command for position independent code
                         # used on some platforms
    asmStmtFrmt: string, # format of ASM statement
    structStmtFmt: string, # Format for struct statement
    produceAsm: string,  # Format how to produce assembler listings
    cppXsupport: string, # what to do to enable C++X support
    props: InfoCCProps] # properties of the C compiler


# Configuration settings for various compilers.
# When adding new compilers, the cmake sources could be a good reference:
# http://cmake.org/gitweb?p=cmake.git;a=tree;f=Modules/Platform;

template compiler(name, settings: untyped): untyped =
  proc name: InfoCC {.compileTime.} = settings

const
  gnuAsmListing = "-Wa,-acdl=$asmfile -g -fverbose-asm -masm=intel"

# GNU C and C++ Compiler
compiler gcc:
  result = (
    name: "gcc",
    objExt: "o",
    optSpeed: " -O3 -fno-ident",
    optSize: " -Os -fno-ident",
    compilerExe: "gcc",
    cppCompiler: "g++",
    compileTmpl: "-c $options $include -o $objfile $file",
    buildGui: " -mwindows",
    buildDll: " -shared",
    buildLib: "ar rcs $libfile $objfiles",
    linkerExe: "",
    linkTmpl: "$buildgui $builddll -o $exefile $objfiles $options",
    includeCmd: " -I",
    linkDirCmd: " -L",
    linkLibCmd: " -l$1",
    debug: "",
    pic: "-fPIC",
    asmStmtFrmt: "__asm__($1);$n",
    structStmtFmt: "$1 $3 $2 ", # struct|union [packed] $name
    produceAsm: gnuAsmListing,
    cppXsupport: "-std=gnu++17 -funsigned-char",
    props: {hasSwitchRange, hasComputedGoto, hasCpp, hasGcGuard, hasGnuAsm,
            hasAttribute, hasBuiltinUnreachable})

# GNU C and C++ Compiler
compiler nintendoSwitchGCC:
  result = (
    name: "switch_gcc",
    objExt: "o",
    optSpeed: " -O3 ",
    optSize: " -Os ",
    compilerExe: "aarch64-none-elf-gcc",
    cppCompiler: "aarch64-none-elf-g++",
    compileTmpl: "-w -MMD -MP -MF $dfile -c $options $include -o $objfile $file",
    buildGui: " -mwindows",
    buildDll: " -shared",
    buildLib: "aarch64-none-elf-gcc-ar rcs $libfile $objfiles",
    linkerExe: "aarch64-none-elf-gcc",
    linkTmpl: "$buildgui $builddll -Wl,-Map,$mapfile -o $exefile $objfiles $options",
    includeCmd: " -I",
    linkDirCmd: " -L",
    linkLibCmd: " -l$1",
    debug: "",
    pic: "-fPIE",
    asmStmtFrmt: "asm($1);$n",
    structStmtFmt: "$1 $3 $2 ", # struct|union [packed] $name
    produceAsm: gnuAsmListing,
    cppXsupport: "-std=gnu++17 -funsigned-char",
    props: {hasSwitchRange, hasComputedGoto, hasCpp, hasGcGuard, hasGnuAsm,
            hasAttribute, hasBuiltinUnreachable})

# LLVM Frontend for GCC/G++
compiler llvmGcc:
  result = gcc() # Uses settings from GCC

  result.name = "llvm_gcc"
  result.compilerExe = "llvm-gcc"
  result.cppCompiler = "llvm-g++"
  when defined(macosx) or defined(openbsd):
    # `llvm-ar` not available
    result.buildLib = "ar rcs $libfile $objfiles"
  else:
    result.buildLib = "llvm-ar rcs $libfile $objfiles"

# Clang (LLVM) C/C++ Compiler
compiler clang:
  result = llvmGcc() # Uses settings from llvmGcc

  result.name = "clang"
  result.compilerExe = "clang"
  result.cppCompiler = "clang++"

# Microsoft Visual C/C++ Compiler
compiler vcc:
  result = (
    name: "vcc",
    objExt: "obj",
    optSpeed: " /Ogityb2 ",
    optSize: " /O1 ",
    compilerExe: "cl",
    cppCompiler: "cl",
    compileTmpl: "/c$vccplatform $options $include /nologo /Fo$objfile $file",
    buildGui: " /SUBSYSTEM:WINDOWS user32.lib ",
    buildDll: " /LD",
    buildLib: "vccexe --command:lib$vccplatform /nologo /OUT:$libfile $objfiles",
    linkerExe: "cl",
    linkTmpl: "$builddll$vccplatform /Fe$exefile $objfiles $buildgui /nologo $options",
    includeCmd: " /I",
    linkDirCmd: " /LIBPATH:",
    linkLibCmd: " $1.lib",
    debug: " /RTC1 /Z7 ",
    pic: "",
    asmStmtFrmt: "__asm{$n$1$n}$n",
    structStmtFmt: "$3$n$1 $2",
    produceAsm: "/Fa$asmfile",
    cppXsupport: "",
    props: {hasCpp, hasAssume, hasDeclspec})

# Nvidia CUDA NVCC Compiler
compiler nvcc:
  result = gcc()
  result.name = "nvcc"
  result.compilerExe = "nvcc"
  result.cppCompiler = "nvcc"
  result.compileTmpl = "-c -x cu -Xcompiler=\"$options\" $include -o $objfile $file"
  result.linkTmpl = "$buildgui $builddll -o $exefile $objfiles -Xcompiler=\"$options\""

# AMD HIPCC Compiler (rocm/cuda)
compiler hipcc:
  result = clang()
  result.name = "hipcc"
  result.compilerExe = "hipcc"
  result.cppCompiler = "hipcc"

compiler clangcl:
  result = vcc()
  result.name = "clang_cl"
  result.compilerExe = "clang-cl"
  result.cppCompiler = "clang-cl"
  result.linkerExe = "clang-cl"
  result.linkTmpl = "-fuse-ld=lld " & result.linkTmpl

# Intel C/C++ Compiler
compiler icl:
  result = vcc()
  result.name = "icl"
  result.compilerExe = "icl"
  result.linkerExe = "icl"

# Intel compilers try to imitate the native ones (gcc and msvc)
compiler icc:
  result = gcc()
  result.name = "icc"
  result.compilerExe = "icc"
  result.linkerExe = "icc"

# Borland C Compiler
compiler bcc:
  result = (
    name: "bcc",
    objExt: "obj",
    optSpeed: " -O3 -6 ",
    optSize: " -O1 -6 ",
    compilerExe: "bcc32c",
    cppCompiler: "cpp32c",
    compileTmpl: "-c $options $include -o$objfile $file",
    buildGui: " -tW",
    buildDll: " -tWD",
    buildLib: "", # XXX: not supported yet
    linkerExe: "bcc32",
    linkTmpl: "$options $buildgui $builddll -e$exefile $objfiles",
    includeCmd: " -I",
    linkDirCmd: "", # XXX: not supported yet
    linkLibCmd: "", # XXX: not supported yet
    debug: "",
    pic: "",
    asmStmtFrmt: "__asm{$n$1$n}$n",
    structStmtFmt: "$1 $2",
    produceAsm: "",
    cppXsupport: "",
    props: {hasSwitchRange, hasComputedGoto, hasCpp, hasGcGuard,
            hasAttribute})

# Tiny C Compiler
compiler tcc:
  result = (
    name: "tcc",
    objExt: "o",
    optSpeed: "",
    optSize: "",
    compilerExe: "tcc",
    cppCompiler: "",
    compileTmpl: "-c $options $include -o $objfile $file",
    buildGui: "-Wl,-subsystem=gui",
    buildDll: " -shared",
    buildLib: "", # XXX: not supported yet
    linkerExe: "tcc",
    linkTmpl: "-o $exefile $options $buildgui $builddll $objfiles",
    includeCmd: " -I",
    linkDirCmd: "", # XXX: not supported yet
    linkLibCmd: "", # XXX: not supported yet
    debug: " -g ",
    pic: "",
    asmStmtFrmt: "asm($1);$n",
    structStmtFmt: "$1 $2",
    produceAsm: gnuAsmListing,
    cppXsupport: "",
    props: {hasSwitchRange, hasComputedGoto, hasGnuAsm})

# Your C Compiler
compiler envcc:
  result = (
    name: "env",
    objExt: "o",
    optSpeed: " -O3 ",
    optSize: " -O1 ",
    compilerExe: "",
    cppCompiler: "",
    compileTmpl: "-c $ccenvflags $options $include -o $objfile $file",
    buildGui: "",
    buildDll: " -shared ",
    buildLib: "", # XXX: not supported yet
    linkerExe: "",
    linkTmpl: "-o $exefile $buildgui $builddll $objfiles $options",
    includeCmd: " -I",
    linkDirCmd: "", # XXX: not supported yet
    linkLibCmd: "", # XXX: not supported yet
    debug: "",
    pic: "",
    asmStmtFrmt: "__asm{$n$1$n}$n",
    structStmtFmt: "$1 $2",
    produceAsm: "",
    cppXsupport: "",
    props: {hasGnuAsm})

const
  CC*: array[succ(low(SystemCC))..high(SystemCC), InfoCC] = [
    gcc(),
    nintendoSwitchGCC(),
    llvmGcc(),
    clang(),
    bcc(),
    vcc(),
    tcc(),
    envcc(),
    icl(),
    icc(),
    clangcl(),
    hipcc(),
    nvcc()]

proc nameToCC*(name: string): SystemCC =
  ## Returns the kind of compiler referred to by `name`, or ccNone
  ## if the name doesn't refer to any known compiler.
  for i in succ(ccNone)..high(SystemCC):
    if cmpIgnoreStyle(name, CC[i].name) == 0:
      return i
  result = ccNone

proc listCCnames(): string =
  result = ""
  for i in succ(ccNone)..high(SystemCC):
    if i > succ(ccNone): result.add ", "
    result.add CC[i].name

proc setCC*(conf: ConfigRef; ccname: string) =
  conf.cCompiler = nameToCC(ccname)
  if conf.cCompiler == ccNone:
    quit "unknown C compiler: '$1'. Available options are: $2" % [ccname, listCCnames()]

proc getCompilerExe*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].compilerExe

proc getCppCompiler*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].cppCompiler

proc getOptSpeed*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].optSpeed

proc getOptSize*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].optSize

