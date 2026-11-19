#include <lean/lean.h>
#include <openssl/sha.h>
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

lean_object *gloas_ssz_sha_pair(b_lean_obj_arg left, b_lean_obj_arg right) {
    unsigned char input[64];
    if (lean_sarray_size(left) != 32 || lean_sarray_size(right) != 32)
        lean_internal_panic("invalid SSZ hash block");
    memcpy(input, lean_sarray_cptr(left), 32);
    memcpy(input + 32, lean_sarray_cptr(right), 32);
    lean_object *root = lean_alloc_sarray(1, 32, 32);
    SHA256(input, sizeof(input), lean_sarray_cptr(root));
    return root;
}

char *ssz_vector_root(const char *schema, const unsigned char *data, size_t length) {
    lean_object *bytes = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(bytes), data, length);
    lean_object *result = gloas_run_ssz(lean_mk_string(schema), bytes);
    char *text = strdup(lean_string_cstr(result));
    lean_dec(result);
    return text;
}
