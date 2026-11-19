#include <lean/lean.h>
#include <blst.h>
#include <string.h>

extern lean_object *gloas_builder_signing_root(lean_object *, lean_object *);

static lean_object *copy_bytes(const unsigned char *src, size_t length) {
    lean_object *result = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(result), src, length);
    return result;
}

/* BuilderDepositRequest has four fixed-width fields: 48, 32, 8, and 96 bytes.
 * Lean supplies the domain-separated signing root. blst only verifies the
 * BLS12-381 signature, including encoding, subgroup and infinity checks. */
int verify_builder_signature(const unsigned char *request, size_t length,
                             const unsigned char *version, size_t version_len) {
    if (length != 184 || version_len != 4) return -1;
    blst_p1_affine key;
    blst_p2_affine signature;
    if (blst_p1_uncompress(&key, request) != BLST_SUCCESS ||
        !blst_p1_affine_in_g1(&key) || blst_p1_affine_is_inf(&key) ||
        blst_p2_uncompress(&signature, request + 88) != BLST_SUCCESS ||
        !blst_p2_affine_in_g2(&signature) || blst_p2_affine_is_inf(&signature))
        return 0;
    lean_object *root = gloas_builder_signing_root(copy_bytes(request, 88), copy_bytes(version, 4));
    static const unsigned char dst[] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
    int result = -1;
    if (lean_sarray_size(root) == 32)
        result = blst_core_verify_pk_in_g1(&key, &signature, true,
            lean_sarray_cptr(root), 32, dst, sizeof(dst) - 1, NULL, 0) == BLST_SUCCESS;
    lean_dec(root);
    return result;
}
