
const
  Prelude* = """
/* GENERATED CODE. DO NOT EDIT. */

#ifdef __cplusplus
#  if __cplusplus >= 201103L
#    /* nullptr is more type safe (less implicit conversions than 0) */
#    define NIM_NIL nullptr
#  else
#    // both `((void*)0)` and `NULL` would cause codegen to emit
#    // error: assigning to 'Foo *' from incompatible type 'void *'
#    // but codegen could be fixed if need. See also potential caveat regarding
#    // NULL.
#    // However, `0` causes other issues, see #13798
#    define NIM_NIL 0
#  endif
#else
#  include <stdbool.h>
#  define NIM_NIL NULL
#endif

#ifdef __cplusplus
#define NB8 bool
#elif (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901)
// see #13798: to avoid conflicts for code emitting `#include <stdbool.h>`
#define NB8 _Bool
#else
typedef unsigned char NB8; // best effort
#endif

typedef unsigned char NC8;

typedef float NF32;
typedef double NF64;
#if defined(__BORLANDC__) || defined(_MSC_VER)
typedef signed char NI8;
typedef signed short int NI16;
typedef signed int NI32;
typedef __int64 NI64;
/* XXX: Float128? */
typedef unsigned char NU8;
typedef unsigned short int NU16;
typedef unsigned int NU32;
typedef unsigned __int64 NU64;
#elif defined(HAVE_STDINT_H)
#ifndef USE_NIM_NAMESPACE
#  include <stdint.h>
#endif
typedef int8_t NI8;
typedef int16_t NI16;
typedef int32_t NI32;
typedef int64_t NI64;
typedef uint8_t NU8;
typedef uint16_t NU16;
typedef uint32_t NU32;
typedef uint64_t NU64;
#elif defined(HAVE_CSTDINT)
#ifndef USE_NIM_NAMESPACE
#  include <cstdint>
#endif
typedef std::int8_t NI8;
typedef std::int16_t NI16;
typedef std::int32_t NI32;
typedef std::int64_t NI64;
typedef std::uint8_t NU8;
typedef std::uint16_t NU16;
typedef std::uint32_t NU32;
typedef std::uint64_t NU64;
#else
/* Unknown compiler/version, do our best */
#ifdef __INT8_TYPE__
typedef __INT8_TYPE__ NI8;
#else
typedef signed char NI8;
#endif
#ifdef __INT16_TYPE__
typedef __INT16_TYPE__ NI16;
#else
typedef signed short int NI16;
#endif
#ifdef __INT32_TYPE__
typedef __INT32_TYPE__ NI32;
#else
typedef signed int NI32;
#endif
#ifdef __INT64_TYPE__
typedef __INT64_TYPE__ NI64;
#else
typedef long long int NI64;
#endif
/* XXX: Float128? */
#ifdef __UINT8_TYPE__
typedef __UINT8_TYPE__ NU8;
#else
typedef unsigned char NU8;
#endif
#ifdef __UINT16_TYPE__
typedef __UINT16_TYPE__ NU16;
#else
typedef unsigned short int NU16;
#endif
#ifdef __UINT32_TYPE__
typedef __UINT32_TYPE__ NU32;
#else
typedef unsigned int NU32;
#endif
#ifdef __UINT64_TYPE__
typedef __UINT64_TYPE__ NU64;
#else
typedef unsigned long long int NU64;
#endif
#endif

#ifdef NIM_INTBITS
#  if NIM_INTBITS == 64
typedef NI64 NI;
typedef NU64 NU;
#  elif NIM_INTBITS == 32
typedef NI32 NI;
typedef NU32 NU;
#  elif NIM_INTBITS == 16
typedef NI16 NI;
typedef NU16 NU;
#  elif NIM_INTBITS == 8
typedef NI8 NI;
typedef NU8 NU;
#  else
#    error "invalid bit width for int"
#  endif
#endif

#define NIM_TRUE true
#define NIM_FALSE false

"""

