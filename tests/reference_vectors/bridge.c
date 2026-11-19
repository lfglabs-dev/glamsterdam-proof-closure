#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_tests_reference__vectors_PaymentVectors(uint8_t builtin);
extern lean_object *glamsterdam_replay_payment_window(lean_object *input);

int initialize_vectors(void) {
    lean_initialize_runtime_module();
    lean_object *result = initialize_tests_reference__vectors_PaymentVectors(1);
    int failed = lean_io_result_is_error(result);
    if (failed) lean_io_result_show_error(result);
    lean_dec(result);
    lean_io_mark_end_initialization();
    return failed;
}

char *replay_vectors(const char *input) {
    lean_object *result = glamsterdam_replay_payment_window(lean_mk_string(input));
    char *output = strdup(lean_string_cstr(result));
    lean_dec(result);
    return output;
}

void release_output(char *output) { free(output); }
