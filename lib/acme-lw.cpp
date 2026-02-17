/**
 * If you want to work through what the code is actually doing this has an excellent
 * description of the protocol being used.
 *
 * https://github.com/alexpeattie/letsencrypt-fromscratch
 */

#include "acme-lw.h"

#include "http.h"

// From here: https://github.com/nlohmann/json/blob/develop/single_include/nlohmann/json.hpp
// This should probably be a git submodule, but the repo is huge.
#include "json.hpp"

#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/x509v3.h>

#if OPENSSL_VERSION_MAJOR >= 3
#include <openssl/core_names.h>
#endif

#include <algorithm>
#include <atomic>
#include <chrono>
#include <ctype.h>
#include <sstream>
#include <stdio.h>
#include <thread>
#include <typeinfo>
#include <vector>

using namespace std;

using namespace acme_lw_internal;

namespace
{

const char * stagingDirectoryUrl = "https://acme-staging-v02.api.letsencrypt.org/directory";
const char * productionDirectoryUrl = "https://acme-v02.api.letsencrypt.org/directory";

// Smart pointers for OpenSSL types
template<typename TYPE, void (*FREE)(TYPE *)>
struct Ptr
{
    Ptr()
        : ptr_(nullptr)
    {
    }

    Ptr(TYPE * ptr)
        : ptr_(ptr)
    {
        if (!ptr_)
        {
            throw acme_lw::AcmeException("Failed to create "s + typeid(*this).name());
        }
    }

    ~Ptr()
    {
        if (ptr_)
        {
            FREE(ptr_);
        }
    }

    Ptr& operator = (Ptr&& ptr)
    {
        if (!ptr.ptr_)
        {
            throw acme_lw::AcmeException("Failed to create "s + typeid(*this).name());
        }

        if (ptr_)
        {
            FREE(ptr_);
        }

        ptr_ = move(ptr.ptr_);
        ptr.ptr_ = nullptr;

        return *this;
    }

    bool operator ! () const
    {
        return !ptr_;
    }

    TYPE * operator * () const
    {
        return ptr_;
    }

    void clear()
    {
        ptr_ = nullptr;
    }

private:
    TYPE * ptr_;
};

typedef Ptr<BIO, BIO_free_all>                                  BIOptr;
typedef Ptr<BIGNUM, BN_clear_free>                              BIGNUMptr;
typedef Ptr<EVP_MD_CTX, EVP_MD_CTX_free>                        EVP_MD_CTXptr;
typedef Ptr<EVP_PKEY, EVP_PKEY_free>                            EVP_PKEYptr;
typedef Ptr<EVP_PKEY_CTX, EVP_PKEY_CTX_free>                    EVP_PKEY_CTXptr;
typedef Ptr<X509, X509_free>                                    X509ptr;
typedef Ptr<X509_REQ, X509_REQ_free>                            X509_REQptr;

#if OPENSSL_VERSION_MAJOR < 3
typedef Ptr<RSA, RSA_free>                                      RSAptr;
typedef Ptr<EC_KEY, EC_KEY_free>                                EC_KEYptr;
#endif
typedef Ptr<BN_CTX, BN_CTX_free>                                BN_CTXptr;
typedef Ptr<ECDSA_SIG, ECDSA_SIG_free>                          ECDSA_SIGptr;

enum class AccountKeyAlgorithm { RS256, ES256 };

string urlSafeBase64Encode(const BIGNUM * bn);

AccountKeyAlgorithm getAccountKeyAlgorithm(EVP_PKEY * key)
{
    int type = EVP_PKEY_base_id(key);
    if (type == EVP_PKEY_RSA)
    {
        return AccountKeyAlgorithm::RS256;
    }
    if (type == EVP_PKEY_EC)
    {
        return AccountKeyAlgorithm::ES256;
    }

    throw acme_lw::AcmeException("Unsupported account key algorithm");
}

string makeAccountJwk(EVP_PKEY * key, AccountKeyAlgorithm algorithm)
{
    if (algorithm == AccountKeyAlgorithm::RS256)
    {
#if OPENSSL_VERSION_MAJOR < 3
        RSA * rsa = EVP_PKEY_get1_RSA(key);
        if (!rsa)
        {
            throw acme_lw::AcmeException("Unable to read RSA account private key");
        }

        const BIGNUM *n, *e, *d;
        RSA_get0_key(rsa, &n, &e, &d);
        RSA_free(rsa);
#else
        BIGNUMptr nptr(BN_new()), eptr(BN_new());
        const BIGNUM *n = *nptr;
        const BIGNUM *e = *eptr;
        if (EVP_PKEY_get_bn_param(key, OSSL_PKEY_PARAM_RSA_N, const_cast<BIGNUM **>(&n)) != 1 ||
            EVP_PKEY_get_bn_param(key, OSSL_PKEY_PARAM_RSA_E, const_cast<BIGNUM **>(&e)) != 1)
        {
            throw acme_lw::AcmeException("Unable to read RSA account key parameters");
        }
#endif

        return R"( {
                                    "e":")"s + urlSafeBase64Encode(e) + R"(",
                                    "kty": "RSA",
                                    "n":")"s + urlSafeBase64Encode(n) + R"("
                                })";
    }

#if OPENSSL_VERSION_MAJOR < 3
    EC_KEYptr ecKey(EVP_PKEY_get1_EC_KEY(key));
    const EC_GROUP * group = EC_KEY_get0_group(*ecKey);
    if (!group)
    {
        throw acme_lw::AcmeException("Unable to read ECDSA account key group");
    }

    if (EC_GROUP_get_curve_name(group) != NID_X9_62_prime256v1)
    {
        throw acme_lw::AcmeException("ECDSA account key must use curve prime256v1 (P-256)");
    }

    const EC_POINT * publicPoint = EC_KEY_get0_public_key(*ecKey);
    if (!publicPoint)
    {
        throw acme_lw::AcmeException("Unable to read ECDSA account public key");
    }

    BN_CTXptr bnContext(BN_CTX_new());
    BIGNUMptr x(BN_new()), y(BN_new());
    if (EC_POINT_get_affine_coordinates_GFp(group, publicPoint, *x, *y, *bnContext) != 1)
    {
        throw acme_lw::AcmeException("Unable to read ECDSA account key coordinates");
    }

    const BIGNUM *xCoordinate = *x;
    const BIGNUM *yCoordinate = *y;
#else
    char groupName[64];
    size_t groupNameLength = 0;
    if (EVP_PKEY_get_utf8_string_param(key, OSSL_PKEY_PARAM_GROUP_NAME, groupName, sizeof(groupName), &groupNameLength) != 1 ||
        string(groupName, groupNameLength) != "prime256v1")
    {
        throw acme_lw::AcmeException("ECDSA account key must use curve prime256v1 (P-256)");
    }

    BIGNUMptr xptr(BN_new()), yptr(BN_new());
    const BIGNUM *xCoordinate = *xptr;
    const BIGNUM *yCoordinate = *yptr;
    if (EVP_PKEY_get_bn_param(key, OSSL_PKEY_PARAM_EC_PUB_X, const_cast<BIGNUM **>(&xCoordinate)) != 1 ||
        EVP_PKEY_get_bn_param(key, OSSL_PKEY_PARAM_EC_PUB_Y, const_cast<BIGNUM **>(&yCoordinate)) != 1)
    {
        throw acme_lw::AcmeException("Unable to read ECDSA account key coordinates");
    }
#endif

    // Note json keys must be in lexographical order.
    return R"( {
                                    "crv":"P-256",
                                    "kty": "EC",
                                    "x":")"s + urlSafeBase64Encode(xCoordinate) + R"(",
                                    "y":")"s + urlSafeBase64Encode(yCoordinate) + R"("
                                })";
}

EVP_PKEYptr makeCertificateKey(acme_lw::AcmeClient::CertificateKeyType keyType)
{
    if (keyType == acme_lw::AcmeClient::CertificateKeyType::ECDSA)
    {
        EVP_PKEY_CTX* rawContext = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, nullptr);
        if (!rawContext)
        {
            throw acme_lw::AcmeException("Failure in EVP_PKEY_CTX_new_id for ECDSA");
        }

        EVP_PKEYptr key;
        EVP_PKEY_CTXptr context(rawContext);
        if (EVP_PKEY_keygen_init(*context) != 1 ||
            EVP_PKEY_CTX_set_ec_paramgen_curve_nid(*context, NID_X9_62_prime256v1) != 1)
        {
            throw acme_lw::AcmeException("Failure initializing ECDSA key generation");
        }

        EVP_PKEY* rawKey = nullptr;
        if (EVP_PKEY_keygen(*context, &rawKey) != 1)
        {
            throw acme_lw::AcmeException("Failure in EVP_PKEY_keygen for ECDSA");
        }

        return EVP_PKEYptr(rawKey);
    }

    // RSA default
    const int bits = 4096;

// OpenSSL 3 deprecates some functions and introduces new replacements
#if OPENSSL_VERSION_MAJOR < 3
    BIGNUMptr bn(BN_new());
    if (!BN_set_word(*bn, RSA_F4))
    {
        throw acme_lw::AcmeException("Failure in BN_set_word");
    }

    RSAptr rsa(RSA_new());

    if (!RSA_generate_key_ex(*rsa, bits, *bn, nullptr))
    {
        throw acme_lw::AcmeException("Failure in RSA_generate_key_ex");
    }

    EVP_PKEYptr key(EVP_PKEY_new());
    if (!EVP_PKEY_assign_RSA(*key, *rsa))
    {
        throw acme_lw::AcmeException("Failure in EVP_PKEY_assign_RSA");
    }
    rsa.clear();     // rsa will be freed when key is freed.
    return key;
#else
    return EVP_PKEYptr(EVP_RSA_gen(bits));
#endif
}

void freeStackOfExtensions(STACK_OF(X509_EXTENSION) * e)
{
    sk_X509_EXTENSION_pop_free(e, X509_EXTENSION_free);
}

typedef Ptr<STACK_OF(X509_EXTENSION), freeStackOfExtensions>    X509_EXTENSIONSptr;

template<typename T>
T toT(const vector<char>& v)
{
    return v;
}

template<>
string toT(const vector<char>& v)
{
    return string(&v.front(), v.size());
}

vector<char> toVector(BIO * bio)
{
    constexpr int buffSize = 1024;

    vector<char> buffer(buffSize);

    size_t pos = 0;
    int count = 0;
    do
    {
        count = BIO_read(bio, &buffer.front() + pos, buffSize);
        if (count > 0)
        {
            pos += count;
            buffer.resize(pos + buffSize);
        }
    }
    while (count > 0);

    buffer.resize(pos);

    return buffer;
}

string toString(BIO *bio)
{
    vector<char> v = toVector(bio);
    return string(&v.front(), v.size());
}

template<typename T>
string base64Encode(const T& t)
{
    if (!t.size())
    {
        return "";
    }
    // Use openssl to do this since we're already linking to it.

    // Don't need (or want) a BIOptr since BIO_push chains it to b64
    BIO * bio(BIO_new(BIO_s_mem()));
    BIOptr b64(BIO_new(BIO_f_base64()));

    // OpenSSL inserts new lines by default to make it look like PEM format.
    // Turn that off.
    BIO_set_flags(*b64, BIO_FLAGS_BASE64_NO_NL);

    BIO_push(*b64, bio);
    if (BIO_write(*b64, &t.front(), static_cast<int>(t.size())) <= 0 ||
        BIO_flush(*b64) < 0)
    {
        throw acme_lw::AcmeException("Failure in BIO_write / BIO_flush");
    }

    return toString(bio);
}

template<typename T>
string urlSafeBase64Encode(const T& t)
{
    string s = base64Encode(t);

    // We need url safe base64 encoding and openssl only gives us regular
    // base64, so we convert.
    size_t len = s.size();
    for (size_t i = 0; i < len; ++i)
    {
        if (s[i] == '+')
        {
            s[i] = '-';
        }
        else if (s[i] == '/')
        {
            s[i] = '_';
        }
        else if (s[i] == '=')
        {
            s.resize(i);
            break;
        }
    }

    return s;
}

string urlSafeBase64Encode(const BIGNUM * bn)
{
    int numBytes = BN_num_bytes(bn);
    vector<unsigned char> buffer(numBytes);
    BN_bn2bin(bn, &buffer.front());

    return urlSafeBase64Encode(buffer);
}

// returns pair<CSR, privateKey>
pair<string, string> makeCertificateSigningRequest(const std::list<std::string>& domainNames,
                                                   acme_lw::AcmeClient::CertificateKeyType keyType)
{
    EVP_PKEYptr key = makeCertificateKey(keyType);

    X509_REQptr req(X509_REQ_new());

    auto name = domainNames.begin();

    X509_NAME * cn = X509_REQ_get_subject_name(*req);
    if (!X509_NAME_add_entry_by_txt(cn,
                                    "CN",
                                    MBSTRING_ASC,
                                    reinterpret_cast<const unsigned char*>(name->c_str()),
                                    -1, -1, 0))
    {
        throw acme_lw::AcmeException("Failure in X509_Name_add_entry_by_txt");
    }

    if (++name != domainNames.end())
    {
        // We have one or more Subject Alternative Names
        X509_EXTENSIONSptr extensions(sk_X509_EXTENSION_new_null());

        string value;
        do
        {
            if (!value.empty())
            {
                value += ", ";
            }
            value += "DNS:" + *name;
        }
        while (++name != domainNames.end());

        if (!sk_X509_EXTENSION_push(*extensions, X509V3_EXT_conf_nid(nullptr, nullptr, NID_subject_alt_name, value.c_str())))
        {
            throw acme_lw::AcmeException("Unable to add Subject Alternative Name to extensions");
        }

        if (X509_REQ_add_extensions(*req, *extensions) != 1)
        {
            throw acme_lw::AcmeException("Unable to add Subject Alternative Names to CSR");
        }
    }


    BIOptr keyBio(BIO_new(BIO_s_mem()));
    if (PEM_write_bio_PrivateKey(*keyBio, *key, nullptr, nullptr, 0, nullptr, nullptr) != 1)
    {
        throw acme_lw::AcmeException("Failure in PEM_write_bio_PrivateKey");
    }

    string privateKey = toString(*keyBio);

    if (!X509_REQ_set_pubkey(*req, *key))
    {
        throw acme_lw::AcmeException("Failure in X509_REQ_set_pubkey");
    }

    if (!X509_REQ_sign(*req, *key, EVP_sha256()))
    {
        throw acme_lw::AcmeException("Failure in X509_REQ_sign");
    }

    BIOptr reqBio(BIO_new(BIO_s_mem()));
    if (i2d_X509_REQ_bio(*reqBio, *req) < 0)
    {
        throw acme_lw::AcmeException("Failure in i2d_X509_REQ_bio");
    }

    return make_pair(urlSafeBase64Encode(toVector(*reqBio)), privateKey);
}

string sha256(const string& s)
{
    EVP_MD_CTXptr ctx(EVP_MD_CTX_new());
    vector<unsigned char> hash(EVP_MAX_MD_SIZE);
    unsigned int hashLength = 0;
    if (!EVP_DigestInit_ex(*ctx, EVP_sha256(), nullptr) ||
        !EVP_DigestUpdate(*ctx, s.c_str(), s.size()) ||
        !EVP_DigestFinal_ex(*ctx, &hash.front(), &hashLength))
    {
        throw acme_lw::AcmeException("Error hashing a string");
    }
    hash.resize(hashLength);

    return urlSafeBase64Encode(hash);
}

// https://tools.ietf.org/html/rfc7638
string makeJwkThumbprint(const string& jwk)
{
    string strippedJwk = jwk;

    // strip whitespace
    strippedJwk.erase(remove_if(strippedJwk.begin(), strippedJwk.end(), ::isspace), strippedJwk.end());

    return sha256(strippedJwk);
}

template<typename T>
T extractExpiryData(const acme_lw::Certificate& certificate, const function<T (const ASN1_TIME *)>& extractor)
{
    BIOptr bio(BIO_new(BIO_s_mem()));
    if (BIO_write(*bio, &certificate.fullchain.front(), static_cast<int>(certificate.fullchain.size())) <= 0)
    {
        throw acme_lw::AcmeException("Failure in BIO_write");
    }
    X509ptr x509(PEM_read_bio_X509(*bio, nullptr, nullptr, nullptr));

    const ASN1_TIME * t = X509_get0_notAfter(*x509);

    return extractor(t);
}

void verifyRandomness()
{
    if (!RAND_status())
    {
        throw acme_lw::AcmeException("OpenSSL RAND_status failed");
    }
}

}

namespace acme_lw
{

string newAccountUrl;
string newOrderUrl;

struct AcmeClientImpl
{
    AcmeClientImpl(const string& accountPrivateKey)
    {
        // Create the private key and 'header suffix', used to sign LE certs.
        BIOptr bio(BIO_new_mem_buf(accountPrivateKey.c_str(), -1));
        privateKey_ = PEM_read_bio_PrivateKey(*bio, nullptr, nullptr, nullptr);

        if (!privateKey_)
        {
            throw AcmeException("Unable to read account private key");
        }

        accountAlgorithm_ = getAccountKeyAlgorithm(*privateKey_);

        string jwkValue = makeAccountJwk(*privateKey_, accountAlgorithm_);
        jwkThumbprint_ = makeJwkThumbprint(jwkValue);

        string jwsAlgorithm = (accountAlgorithm_ == AccountKeyAlgorithm::RS256 ? "RS256" : "ES256");

        // We use jwk for the first request, which allows us to get 
        // the account id. We use that thereafter.
        headerSuffix_ = R"(
                "alg": ")" + jwsAlgorithm + R"(",
                "jwk": )" + jwkValue + "}";

        pair<string, string> header = make_pair("location"s, ""s);
        sendRequest<string>(newAccountUrl, R"(
                                                {
                                                    "termsOfServiceAgreed": true,
                                                    "onlyReturnExisting": false
                                                }
                                                )", &header);
        headerSuffix_ = R"(
                "alg": ")" + jwsAlgorithm + R"(",
                "kid": ")" + header.second + "\"}";
    }

    string sign(const string& s)
    {
        // https://wiki.openssl.org/index.php/EVP_Signing_and_Verifying
        size_t signatureLength = 0;

        EVP_MD_CTXptr context(EVP_MD_CTX_create());
        const EVP_MD * sha256 = EVP_get_digestbyname("SHA256");
        if (!sha256 ||
            EVP_DigestInit_ex(*context, sha256, nullptr) != 1 ||
            EVP_DigestSignInit(*context, nullptr, sha256, nullptr, *privateKey_) != 1 ||
            EVP_DigestSignUpdate(*context, s.c_str(), s.size()) != 1 ||
            EVP_DigestSignFinal(*context, nullptr, &signatureLength) != 1)
        {
            throw AcmeException("Error creating SHA256 digest");
        }

        vector<unsigned char> signature(signatureLength);
        if (EVP_DigestSignFinal(*context, &signature.front(), &signatureLength) != 1)
        {
            throw AcmeException("Error creating SHA256 digest in final signature");
        }
        signature.resize(signatureLength);

        if (accountAlgorithm_ == AccountKeyAlgorithm::ES256)
        {
            const unsigned char* p = &signature.front();
            ECDSA_SIGptr ecdsaSignature(d2i_ECDSA_SIG(nullptr, &p, signature.size()));
            const BIGNUM *r, *sPart;
            ECDSA_SIG_get0(*ecdsaSignature, &r, &sPart);

            vector<unsigned char> rawSignature(64, 0);
            if (BN_bn2binpad(r, &rawSignature.front(), 32) != 32 ||
                BN_bn2binpad(sPart, &rawSignature.front() + 32, 32) != 32)
            {
                throw AcmeException("Error formatting ECDSA signature");
            }

            return urlSafeBase64Encode(rawSignature);
        }

        return urlSafeBase64Encode(signature);
    }

    template<typename T>
    T sendRequest(const string& url, const string& payload, pair<string, string> * header = nullptr)
    {
        string protectd = R"({"nonce": ")"s +
                                    getNonce() + "\"," +
                                    R"("url": ")" + url + "\"," +
                                    headerSuffix_;

        protectd = urlSafeBase64Encode(protectd);
        string payld = urlSafeBase64Encode(payload);

        string signature = sign(protectd + "." + payld);

        string body = "{"s +
                        R"("protected": ")" + protectd + "\"," +
                        R"("payload": ")" + payld + "\"," +
                        R"("signature": ")" + signature + "\"}";

        Response response = doPost(url, body, header ? header-> first.c_str() : nullptr);

        static atomic<short> badNonceCount = 0;
        if (response.badNonce_)
        {
            if (++badNonceCount > 10)
            {
                // Something's going wrong so let's break out of the
                // infinite recusion.
                throw AcmeException("Getting multiple bad nonces");
            }

            // Shouldn't happen much. Let's give things a chance to settle down.
            std::this_thread::sleep_for(chrono::seconds(1));

            return sendRequest<T>(url, payload, header);
        }

        badNonceCount = 0;

        if (header)
        {
            header->second = response.headerValue_;
        }

        return toT<T>(response.response_);
    }

    // https://tools.ietf.org/html/rfc8555#section-6.3
    string doPostAsGet(const string& url)
    {
        return sendRequest<string>(url, "");
    }

    nlohmann::json wait(const string& url, const char * errorText)
    {
        // Poll waiting for response to the url be 'status': 'valid'
        int counter = 0;
        constexpr int count = 10;
        do
        {
            std::this_thread::sleep_for(chrono::seconds(1));
            string response = doPostAsGet(url);
            auto json = nlohmann::json::parse(response);
            if (json.at("status") == "valid")
            {
                return json;
            }
        } while (counter++ < count);

        throw AcmeException(errorText);
    }

    // Throws if the challenge isn't accepted (or on timeout)
    void verifyChallengePassed(const nlohmann::json& challenge)
    {
        // Tell the CA we're prepared for the challenge.
        string verificationUrl = challenge.at("url");
        auto response = nlohmann::json::parse(sendRequest<string>(verificationUrl, "{}"));
        if (response.at("status") == "valid")
        {
            return;
        }
        
        string challengeStatusUrl = response.at("url");
        wait(challengeStatusUrl, "Failure / timeout verifying challenge passed");
    }

    Certificate issueCertificate(const list<string>& domainNames,
                                 AcmeClient::Callback callback,
                                 AcmeClient::Challenge chg,
                                 AcmeClient::CertificateKeyType keyType)
    {
        if (domainNames.empty())
        {
            throw AcmeException("There must be at least one domain name in a certificate");
        }

        // Create the order        
        string payload = R"({"identifiers": [)";
        bool first = true;
        for (const string& domain : domainNames)
        {
            /*
            Just check for a '"' in the domain name to make sure that we send 
            a validly formed json payload. The acme service should validate
            that the domain name is well formed.
            */
            if (domain.find('"') != string::npos)
            {
                throw AcmeException("Certificate requested for invalid domain name: "s + domain);
            }

            if (!first)
            {
                payload += ",";
            }
            first = false;

            payload += R"(
                            {
                                "type": "dns",
                                "value": ")"s + domain + R"("
                            }
                           )";
        }
        payload += "]}";

        pair<string, string> header = make_pair("location"s, ""s);
        string response = sendRequest<string>(newOrderUrl, payload, &header);
        string currentOrderUrl = header.second;

        // Pass the challenges
        auto json = nlohmann::json::parse(response);
        auto& authorizations = json.at("authorizations");
        for (const auto& authorization : authorizations)
        {
            auto authz = nlohmann::json::parse(doPostAsGet(authorization));
            /**
             * If you pass a challenge, that's good for 300 days. The cert is only good for 90.
             * This means for a while you can re-issue without passing another challenge, so we
             * check to see if we need to validate again.
             *
             * Note that this introduces a race since it possible for the status to not be valid
             * by the time the certificate is requested. The assumption is that client retries
             * will deal with this.
             */
            if (authz.at("status") != "valid")
            {
                auto& challenges = authz.at("challenges");
                for (const auto& challenge : challenges)
                {
                    auto& challenge_type = challenge.at("type");
                    if (chg == AcmeClient::Challenge::HTTP && challenge_type == "http-01")
                    {
                        string token = challenge.at("token");
                        string domain = authz.at("identifier").at("value");
                        string url = "http://"s + domain + "/.well-known/acme-challenge/" + token;
                        string keyAuthorization = token + "." + jwkThumbprint_;
                        callback(domain, url, keyAuthorization);

                        verifyChallengePassed(challenge);
                        break;
                    }
                    else if (chg == AcmeClient::Challenge::DNS && challenge_type == "dns-01")
                    {
                        string token = challenge.at("token");
                        string keyAuthorization = token + "." + jwkThumbprint_;
                        string domain = authz.at("identifier").at("value");
                        string txtName = "_acme-challenge." + domain;
                        string txtValue = sha256(keyAuthorization);
                        callback(domain, txtName, txtValue);

                        verifyChallengePassed(challenge);
                        break;
                    }
                }
            }
        }

        // Request the certificate
        auto r = makeCertificateSigningRequest(domainNames, keyType);
        string csr = r.first;
        string privateKey = r.second;
        sendRequest<vector<char>>(json.at("finalize"),
                                        R"({
                                            "csr": ")"s + csr + R"("
                                        })");

        // Wait for the certificate to be produced
        auto order = wait(currentOrderUrl, "Timeout / failure waiting for certificate to be produced");
        string certificateUrl = order.at("certificate");

        // Retreive the certificate
        Certificate cert;
        cert.fullchain = doPostAsGet(certificateUrl);
        cert.privkey = privateKey;
        return cert;
    }

private:
    string              headerSuffix_;
    EVP_PKEYptr          privateKey_;
    string              jwkThumbprint_;
    AccountKeyAlgorithm accountAlgorithm_;
};

AcmeClient::AcmeClient(const string& accountPrivateKey)
    : impl_(new AcmeClientImpl(accountPrivateKey))
{
    verifyRandomness();
}

AcmeClient::~AcmeClient() = default;

Certificate AcmeClient::issueCertificate(const std::list<std::string>& domainNames,
                                         Callback callback,
                                         Challenge chg,
                                         CertificateKeyType keyType)
{
    return impl_->issueCertificate(domainNames, callback, chg, keyType);
}

void AcmeClient::init(Environment env)
{
    const char * directoryUrl = (env == Environment::PRODUCTION ? productionDirectoryUrl : stagingDirectoryUrl);

    initHttp();

    verifyRandomness();

    try
    {
        string directory = toT<string>(doGet(directoryUrl));
        auto json = nlohmann::json::parse(directory);
        newAccountUrl = json.at("newAccount");
        newOrderUrl = json.at("newOrder");
        initNonce(json.at("newNonce"));
    }
    catch (const exception& e)
    {
        throw AcmeException("Unable to initialize endpoints from "s + directoryUrl + ": " + e.what());
    }
}

void AcmeClient::teardown()
{
    teardownHttp();
}

::time_t Certificate::getExpiry() const
{
    return extractExpiryData<::time_t>(*this, [](const ASN1_TIME * t)
        {
#ifdef OPENSSL_TO_TM
            // Prior to openssl 1.1.1 (or so?) ASN1_TIME_to_tm didn't exist so there was no
            // good way of converting to time_t. If it exists we use the built in function.

            ::tm out;
            if (!ASN1_TIME_to_tm(t, &out))
            {
                throw AcmeException("Failure in ASN1_TIME_to_tm");
            }

#ifdef _WIN32
            return _mkgmtime(&out);
#else
            return timegm(&out);
#endif            
#else
            // See this link for issues in converting from ASN1_TIME to epoch time.
            // https://stackoverflow.com/questions/10975542/asn1-time-to-time-t-conversion

            int days, seconds;
            if (!ASN1_TIME_diff(&days, &seconds, nullptr, t))
            {
                throw AcmeException("Failure in ASN1_TIME_diff");
            }

            // Hackery here, since the call to time(0) will not necessarily match
            // the equivilent call openssl just made in the 'diff' call above.
            // Nonetheless, it'll be close at worst.
            return ::time(0) + seconds + days * 3600 * 24;
#endif
        });
}

string Certificate::getExpiryDisplay() const
{
    return extractExpiryData<string>(*this, [](const ASN1_TIME * t)
        {
            BIOptr b(BIO_new(BIO_s_mem()));
            if (!ASN1_TIME_print(*b, t))
            {
                throw AcmeException("Failure in ASN1_TIME_print");
            }

            return toString(*b);
        });
}

}
