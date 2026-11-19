#include <lean/lean.h>
#include <blst.h>
#include <string.h>

extern lean_object *gloas_builder_signing_root(lean_object *, lean_object *);
extern lean_object *gloas_ptc_signing_root(lean_object *, lean_object *, lean_object *);

static lean_object *copy_bytes(const unsigned char *src, size_t length) {
    lean_object *result = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(result), src, length);
    return result;
}

static int fast_verify(const unsigned char *keys, size_t count, const unsigned char *sig,
                       b_lean_obj_arg root) {
    if (lean_sarray_size(root) != 32 || !count) return -1;
    blst_p1 aggregate;
    blst_p1_affine key;
    blst_p2_affine signature;
    for (size_t i = 0; i < count; ++i) {
        if (blst_p1_uncompress(&key, keys + 48*i) != BLST_SUCCESS ||
            !blst_p1_affine_in_g1(&key) || blst_p1_affine_is_inf(&key)) return 0;
        if (i == 0) blst_p1_from_affine(&aggregate, &key);
        else blst_p1_add_or_double_affine(&aggregate, &aggregate, &key);
    }
    blst_p1_to_affine(&key, &aggregate);
    if (blst_p2_uncompress(&signature, sig) != BLST_SUCCESS ||
        !blst_p2_affine_in_g2(&signature) || blst_p2_affine_is_inf(&signature)) return 0;
    static const unsigned char dst[] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
    return blst_core_verify_pk_in_g1(&key, &signature, true, lean_sarray_cptr(root), 32,
                                     dst, sizeof(dst) - 1, NULL, 0) == BLST_SUCCESS;
}

int verify_builder_signature(const unsigned char *request, size_t length,
                             const unsigned char *version, size_t version_len) {
    if (length != 184 || version_len != 4) return -1;
    lean_object *root = gloas_builder_signing_root(copy_bytes(request, 88), copy_bytes(version, 4));
    int result = fast_verify(request, 1, request + 88, root);
    lean_dec(root);
    return result;
}

int verify_ptc_signature(const unsigned char *keys, size_t keys_len,
                         const unsigned char *message, size_t msg_len,
                         const unsigned char *sig, size_t sig_len,
                         const unsigned char *version, size_t version_len,
                         const unsigned char *genesis, size_t genesis_len) {
    if (!keys_len || keys_len % 48 || msg_len != 42 || sig_len != 96 ||
        version_len != 4 || genesis_len != 32) return -1;
    lean_object *root = gloas_ptc_signing_root(copy_bytes(message, msg_len),
        copy_bytes(version, version_len), copy_bytes(genesis, genesis_len));
    int result = fast_verify(keys, keys_len/48, sig, root);
    lean_dec(root);
    return result;
}
