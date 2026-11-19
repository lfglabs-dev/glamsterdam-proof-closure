#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern lean_object *initialize_tests_reference__vectors_Ssz(uint8_t);
extern lean_object *gloas_run_ssz(lean_object *, lean_object *);

int initialize_ssz_vectors(void) {
    lean_object *result = initialize_tests_reference__vectors_Ssz(1);
    int failed = lean_io_result_is_error(result);
    if (failed) lean_io_result_show_error(result);
    lean_dec(result);
    return failed;
}

char *ssz_vector_root(const char *schema, const unsigned char *data, size_t length) {
    lean_object *bytes = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(bytes), data, length);
    lean_object *result = gloas_run_ssz(lean_mk_string(schema), bytes);
    char *text = strdup(lean_string_cstr(result));
    lean_dec(result);
    return text;
}
