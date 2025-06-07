#include <lean/lean.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef lean_obj_res OBJRES;
typedef lean_obj_arg OWNED_ARG;
typedef b_lean_obj_arg BORROWED_ARG;

LEAN_EXPORT OBJRES lean_string_repeat(uint32_t c, BORROWED_ARG /* Nat */ n) {
  uint32_t nn = lean_uint32_of_nat(n);
  char* str = (char*)calloc(nn + 1, sizeof(uint32_t));
  memset(str, c, nn * sizeof(uint32_t));
  return lean_mk_string(str);
}

LEAN_EXPORT OBJRES lean_disable_stdout_buffer(uint8_t i) {
  if (i == 0) {
    setbuf(stdout, NULL);
  }
  return lean_io_result_mk_ok(lean_box(0));  // runtime Unit repr
}
