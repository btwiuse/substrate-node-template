//! Cipher Suites supported by Secure Transport

use security_framework_sys::cipher_suite::*;

macro_rules! make_suites {
    ($($suite:ident),+) => {
        /// TLS cipher suites.
        #[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
        pub struct CipherSuite(SSLCipherSuite);

        #[allow(missing_docs)]
        impl CipherSuite {
            $(
                pub const $suite: Self = Self($suite);
            )+

            pub fn from_raw(raw: SSLCipherSuite) -> Self {
                Self(raw)
            }

            pub fn to_raw(&self) -> SSLCipherSuite {
                self.0
            }
        }
    }
}

make_suites! {
    // The commented out ones up here are aliases of the matching TLS suites
    SSL_NULL_WITH_NULL_NULL,
    SSL_RSA_WITH_NULL_MD5,
    SSL_RSA_WITH_NULL_SHA,
    SSL_RSA_EXPORT_WITH_RC4_40_MD5,
    SSL_RSA_WITH_RC4_128_MD5,
    SSL_RSA_WITH_RC4_128_SHA,
    SSL_RSA_EXPORT_WITH_RC2_CBC_40_MD5,
    SSL_RSA_WITH_IDEA_CBC_SHA,
    SSL_RSA_EXPORT_WITH_DES40_CBC_SHA,
    SSL_RSA_WITH_DES_CBC_SHA,
    //SSL_RSA_WITH_3DES_EDE_CBC_SHA,
    SSL_DH_DSS_EXPORT_WITH_DES40_CBC_SHA,
    SSL_DH_DSS_WITH_DES_CBC_SHA,
    //SSL_DH_DSS_WITH_3DES_EDE_CBC_SHA,
    SSL_DH_RSA_EXPORT_WITH_DES40_CBC_SHA,
    SSL_DH_RSA_WITH_DES_CBC_SHA,
    //SSL_DH_RSA_WITH_3DES_EDE_CBC_SHA,
    SSL_DHE_DSS_EXPORT_WITH_DES40_CBC_SHA,
    SSL_DHE_DSS_WITH_DES_CBC_SHA,
    //SSL_DHE_DSS_WITH_3DES_EDE_CBC_SHA,
    SSL_DHE_RSA_EXPORT_WITH_DES40_CBC_SHA,
    SSL_DHE_RSA_WITH_DES_CBC_SHA,
    //SSL_DHE_RSA_WITH_3DES_EDE_CBC_SHA,
    SSL_DH_anon_EXPORT_WITH_RC4_40_MD5,
    //SSL_DH_anon_WITH_RC4_128_MD5,
    SSL_DH_anon_EXPORT_WITH_DES40_CBC_SHA,
    SSL_DH_anon_WITH_DES_CBC_SHA,
    //SSL_DH_anon_WITH_3DES_EDE_CBC_SHA,
    SSL_FORTEZZA_DMS_WITH_NULL_SHA,
    SSL_FORTEZZA_DMS_WITH_FORTEZZA_CBC_SHA,

    /* TLS addenda using AES, per RFC 3268 */
    TLS_RSA_WITH_AES_128_CBC_SHA,
    TLS_DH_DSS_WITH_AES_128_CBC_SHA,
    TLS_DH_RSA_WITH_AES_128_CBC_SHA,
    TLS_DHE_DSS_WITH_AES_128_CBC_SHA,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA,
    TLS_DH_anon_WITH_AES_128_CBC_SHA,
    TLS_RSA_WITH_AES_256_CBC_SHA,
    TLS_DH_DSS_WITH_AES_256_CBC_SHA,
    TLS_DH_RSA_WITH_AES_256_CBC_SHA,
    TLS_DHE_DSS_WITH_AES_256_CBC_SHA,
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA,
    TLS_DH_anon_WITH_AES_256_CBC_SHA,

    /* ECDSA addenda, RFC 4492 */
    TLS_ECDH_ECDSA_WITH_NULL_SHA,
    TLS_ECDH_ECDSA_WITH_RC4_128_SHA,
    TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA,
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA,
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA,
    TLS_ECDHE_ECDSA_WITH_NULL_SHA,
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA,
    TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA,
    TLS_ECDH_RSA_WITH_NULL_SHA,
    TLS_ECDH_RSA_WITH_RC4_128_SHA,
    TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA,
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA,
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA,
    TLS_ECDHE_RSA_WITH_NULL_SHA,
    TLS_ECDHE_RSA_WITH_RC4_128_SHA,
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA,
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA,
    TLS_ECDH_anon_WITH_NULL_SHA,
    TLS_ECDH_anon_WITH_RC4_128_SHA,
    TLS_ECDH_anon_WITH_3DES_EDE_CBC_SHA,
    TLS_ECDH_anon_WITH_AES_128_CBC_SHA,
    TLS_ECDH_anon_WITH_AES_256_CBC_SHA,

    /* TLS 1.2 addenda, RFC 5246 */

    /* Initial state. */
    TLS_NULL_WITH_NULL_NULL,

    /* Server provided RSA certificate for key exchange. */
    TLS_RSA_WITH_NULL_MD5,
    TLS_RSA_WITH_NULL_SHA,
    TLS_RSA_WITH_RC4_128_MD5,
    TLS_RSA_WITH_RC4_128_SHA,
    TLS_RSA_WITH_3DES_EDE_CBC_SHA,
    //TLS_RSA_WITH_AES_128_CBC_SHA,
    //TLS_RSA_WITH_AES_256_CBC_SHA,
    TLS_RSA_WITH_NULL_SHA256,
    TLS_RSA_WITH_AES_128_CBC_SHA256,
    TLS_RSA_WITH_AES_256_CBC_SHA256,

    /* Server-authenticated (and optionally client-authenticated) Diffie-Hellman. */
    TLS_DH_DSS_WITH_3DES_EDE_CBC_SHA,
    TLS_DH_RSA_WITH_3DES_EDE_CBC_SHA,
    TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA,
    TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA,
    //TLS_DH_DSS_WITH_AES_128_CBC_SHA,
    //TLS_DH_RSA_WITH_AES_128_CBC_SHA,
    //TLS_DHE_DSS_WITH_AES_128_CBC_SHA,
    //TLS_DHE_RSA_WITH_AES_128_CBC_SHA,
    //TLS_DH_DSS_WITH_AES_256_CBC_SHA,
    //TLS_DH_RSA_WITH_AES_256_CBC_SHA,
    //TLS_DHE_DSS_WITH_AES_256_CBC_SHA,
    //TLS_DHE_RSA_WITH_AES_256_CBC_SHA,
    TLS_DH_DSS_WITH_AES_128_CBC_SHA256,
    TLS_DH_RSA_WITH_AES_128_CBC_SHA256,
    TLS_DHE_DSS_WITH_AES_128_CBC_SHA256,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA256,
    TLS_DH_DSS_WITH_AES_256_CBC_SHA256,
    TLS_DH_RSA_WITH_AES_256_CBC_SHA256,
    TLS_DHE_DSS_WITH_AES_256_CBC_SHA256,
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA256,

    /* Completely anonymous Diffie-Hellman */
    TLS_DH_anon_WITH_RC4_128_MD5,
    TLS_DH_anon_WITH_3DES_EDE_CBC_SHA,
    //TLS_DH_anon_WITH_AES_128_CBC_SHA,
    //TLS_DH_anon_WITH_AES_256_CBC_SHA,
    TLS_DH_anon_WITH_AES_128_CBC_SHA256,
    TLS_DH_anon_WITH_AES_256_CBC_SHA256,

    /* Addendum from RFC 4279, TLS PSK */

    TLS_PSK_WITH_RC4_128_SHA,
    TLS_PSK_WITH_3DES_EDE_CBC_SHA,
    TLS_PSK_WITH_AES_128_CBC_SHA,
    TLS_PSK_WITH_AES_256_CBC_SHA,
    TLS_DHE_PSK_WITH_RC4_128_SHA,
    TLS_DHE_PSK_WITH_3DES_EDE_CBC_SHA,
    TLS_DHE_PSK_WITH_AES_128_CBC_SHA,
    TLS_DHE_PSK_WITH_AES_256_CBC_SHA,
    TLS_RSA_PSK_WITH_RC4_128_SHA,
    TLS_RSA_PSK_WITH_3DES_EDE_CBC_SHA,
    TLS_RSA_PSK_WITH_AES_128_CBC_SHA,
    TLS_RSA_PSK_WITH_AES_256_CBC_SHA,

    /* RFC 4785 - Pre-Shared Key (PSK) Ciphersuites with NULL Encryption */

    TLS_PSK_WITH_NULL_SHA,
    TLS_DHE_PSK_WITH_NULL_SHA,
    TLS_RSA_PSK_WITH_NULL_SHA,

    /* Addenda from rfc 5288 AES Galois Counter Mode (GCM) Cipher Suites
       for TLS. */
    TLS_RSA_WITH_AES_128_GCM_SHA256,
    TLS_RSA_WITH_AES_256_GCM_SHA384,
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256,
    TLS_DHE_RSA_WITH_AES_256_GCM_SHA384,
    TLS_DH_RSA_WITH_AES_128_GCM_SHA256,
    TLS_DH_RSA_WITH_AES_256_GCM_SHA384,
    TLS_DHE_DSS_WITH_AES_128_GCM_SHA256,
    TLS_DHE_DSS_WITH_AES_256_GCM_SHA384,
    TLS_DH_DSS_WITH_AES_128_GCM_SHA256,
    TLS_DH_DSS_WITH_AES_256_GCM_SHA384,
    TLS_DH_anon_WITH_AES_128_GCM_SHA256,
    TLS_DH_anon_WITH_AES_256_GCM_SHA384,

    /* RFC 5487 - PSK with SHA-256/384 and AES GCM */
    TLS_PSK_WITH_AES_128_GCM_SHA256,
    TLS_PSK_WITH_AES_256_GCM_SHA384,
    TLS_DHE_PSK_WITH_AES_128_GCM_SHA256,
    TLS_DHE_PSK_WITH_AES_256_GCM_SHA384,
    TLS_RSA_PSK_WITH_AES_128_GCM_SHA256,
    TLS_RSA_PSK_WITH_AES_256_GCM_SHA384,

    TLS_PSK_WITH_AES_128_CBC_SHA256,
    TLS_PSK_WITH_AES_256_CBC_SHA384,
    TLS_PSK_WITH_NULL_SHA256,
    TLS_PSK_WITH_NULL_SHA384,

    TLS_DHE_PSK_WITH_AES_128_CBC_SHA256,
    TLS_DHE_PSK_WITH_AES_256_CBC_SHA384,
    TLS_DHE_PSK_WITH_NULL_SHA256,
    TLS_DHE_PSK_WITH_NULL_SHA384,

    TLS_RSA_PSK_WITH_AES_128_CBC_SHA256,
    TLS_RSA_PSK_WITH_AES_256_CBC_SHA384,
    TLS_RSA_PSK_WITH_NULL_SHA256,
    TLS_RSA_PSK_WITH_NULL_SHA384,


    /* Addenda from rfc 5289  Elliptic Curve Cipher Suites with
       HMAC SHA-256/384. */
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384,
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256,
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256,
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384,
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256,
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384,

    /* Addenda from rfc 5289  Elliptic Curve Cipher Suites with
       SHA-256/384 and AES Galois Counter Mode (GCM) */
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
    TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384,
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
    TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384,

    /* RFC 5746 - Secure Renegotiation */
    TLS_EMPTY_RENEGOTIATION_INFO_SCSV,
    /*
     * Tags for SSL 2 cipher kinds which are not specified
     * for SSL 3.
     */
    SSL_RSA_WITH_RC2_CBC_MD5,
    SSL_RSA_WITH_IDEA_CBC_MD5,
    SSL_RSA_WITH_DES_CBC_MD5,
    SSL_RSA_WITH_3DES_EDE_CBC_MD5,
    SSL_NO_SUCH_CIPHERSUITE
}
