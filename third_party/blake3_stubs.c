#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <stdint.h>
#include <string.h>
#include "blake3.h"

CAMLprim value caml_blake3(value v_input)
{
    CAMLparam1(v_input);
    CAMLlocal1(result);
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    blake3_hasher_update(&hasher, String_val(v_input), caml_string_length(v_input));
    result = caml_alloc_string(BLAKE3_OUT_LEN);
    blake3_hasher_finalize(&hasher, (uint8_t *)Bytes_val(result), BLAKE3_OUT_LEN);
    CAMLreturn(result);
}
