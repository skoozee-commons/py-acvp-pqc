#   fips205.py
#   2023-11-24  Markku-Juhani O. Saarinen < mjos@iki.fi>. See LICENSE

#   === FIPS 205 implementation https://doi.org/10.6028/NIST.FIPS.205
#   SLH-DSA / Stateless Hash-Based Digital Signature Standard

#   test_slhdsa is only used by the unit test in the end
import math

from test_slhdsa import test_slhdsa

#   hash functions
from Crypto.Hash import SHAKE128, SHAKE256
from Crypto.Hash import SHA224, SHA256, SHA384, SHA512
from Crypto.Hash import SHA3_224, SHA3_256, SHA3_384, SHA3_512

#   A class for handling Addresses (Section 4.2.)

class ADRS:
    #   type constants
    WOTS_HASH   = 0
    WOTS_PK     = 1
    TREE        = 2
    PORS_TREE   = 3
    FORS_ROOTS  = 4
    WOTS_PRF    = 5
    PORS_PRF    = 6 
    #Type constants reused for PORS, maybe new ones if implementation should be more modular?

    def __init__(self, a=32):
        """Initialize."""
        self.a = bytearray(a)

    def copy(self):
        """ Make a copy of self."""
        return ADRS(self.a)

    def set_layer_address(self, x):
        """ Set layer address."""
        self.a[ 0: 4] = x.to_bytes(4, byteorder='big')

    def set_tree_address(self, x):
        """ Set tree address."""
        self.a[ 4:16] = x.to_bytes(12, byteorder='big')

    def set_key_pair_address(self, x):
        """ Set key pair Address."""
        self.a[20:24] = x.to_bytes(4, byteorder='big')

    def get_key_pair_address(self):
        """ Get key pair Address."""
        return int.from_bytes(self.a[20:24], byteorder='big')

    def set_tree_height(self, x):
        """ Set FORS tree height."""
        self.a[24:28] = x.to_bytes(4, byteorder='big')

    def set_chain_address(self, x):
        """ Set WOTS+ chain address."""
        self.a[24:28] = x.to_bytes(4, byteorder='big')

    def set_tree_index(self, x):
        """ Set FORS tree index."""
        self.a[28:32] = x.to_bytes(4, byteorder='big')

    def get_tree_index(self):
        """ Get FORS tree index."""
        return int.from_bytes(self.a[28:32], byteorder='big')

    def set_hash_address(self, x):
        """ Set WOTS+ hash address."""
        self.a[28:32] = x.to_bytes(4, byteorder='big')

    def set_type_and_clear(self, t):
        """ The member function ADRS.setTypeAndClear(Y) for addresses sets
            the type of the ADRS to Y and sets the fnal 12 bytes of the ADRS
            to zero."""
        self.a[16:20] = t.to_bytes(4, byteorder='big')
        for i in range(12):
            self.a[20 + i] = 0

    def adrs(self):
        """ Return the ADRS as bytes."""
        return self.a

    def adrsc(self):
        """ Compressed address ADRDc used with SHA-2."""
        return self.a[3:4] + self.a[8 : 16] + self.a[19:20] + self.a[20:32]

#   Section 11: Table 2. SLH-DSA parameter sets

SLH_DSA_PARAM = {       #   ( hashname, n,  h,  d,  hp, t,  k, lg_w, m, mmax)
    # PORS parameter-sets, derived from https://eprint.iacr.org/2025/2069.pdf, Appendix B.1
    'PORS-FP-SHAKE-128s':   ( 'SHAKE',  16, 63, 7, 9, 57344, 14, 4, 25, 135 )
}

#   SLH-DSA Implementation

class SLH_DSA:

    #   initialize
    def __init__(self,  param='PORS-FP-SHAKE-128s'):

        #   set parameters
        if isinstance(param, str):
            if param not in SLH_DSA_PARAM:
                raise ValueError
            (self.hashname, self.n, self.h, self.d, self.hp,
                self.t_pors, self.k, self.lg_w, self.m, self.mmax) = SLH_DSA_PARAM[param]
        else:
            (self.hashname, self.n, self.h, self.d, self.hp,
                self.t_pors, self.k, self.lg_w, self.m, self.mmax) = param

        #   instantiate hash functions
        if self.hashname == 'SHAKE':
            self.h_msg      = self.shake_h_msg
            self.prf        = self.shake_prf
            self.prf_msg    = self.shake_prf_msg
            self.h_f        = self.shake_f
            self.h_h        = self.shake_f
            self.h_t        = self.shake_f
        elif self.hashname == 'SHA2' and self.n == 16:
            self.h_msg      = self.sha256_h_msg
            self.prf        = self.sha256_prf
            self.prf_msg    = self.sha256_prf_msg
            self.h_f        = self.sha256_f
            self.h_h        = self.sha256_f
            self.h_t        = self.sha256_f
        elif self.hashname == 'SHA2' and self.n > 16:
            self.h_msg      = self.sha512_h_msg
            self.prf        = self.sha256_prf
            self.prf_msg    = self.sha512_prf_msg
            self.h_f        = self.sha256_f
            self.h_h        = self.sha512_h
            self.h_t        = self.sha512_h


        #   equations 5.1 - 5.4
        self.w      = 2**self.lg_w
        self.len1   = (8 * self.n + (self.lg_w - 1)) // self.lg_w
        self.len2   = ((self.len1 *
                        (self.w - 1)).bit_length() - 1) // self.lg_w + 1
        self.len    = self.len1 + self.len2


        self.CTR_BYTES = 4
        #   external parameter sizes
        self.pk_sz  = 2 * self.n
        self.sk_sz  = 4 * self.n

        self.sig_sz = (1 + self.k + self.mmax + self.h + 
                       self.d * self.len) * self.n + self.CTR_BYTES #TODO: how large should the counter be?

        #   rbg
        #self.rbg   = rbg

    #   10.1.   SLH-DSA Using SHAKE
    def shake256(self, x, l):
        """SHAKE256(x, l): Internal hook."""
        return SHAKE256.new(x).read(l)

    def shake_h_msg(self, r, pk_seed, pk_root, m):
        return self.shake256(r + pk_seed + pk_root + m, self.m)

    def shake_prf(self, pk_seed, sk_seed, adrs):
        return self.shake256(pk_seed + adrs.adrs() + sk_seed, self.n)

    def shake_prf_msg(self, sk_prf, opt_rand, m):
        return self.shake256(sk_prf + opt_rand + m, self.n)

    def shake_f(self, pk_seed, adrs, m1):
        return self.shake256(pk_seed + adrs.adrs() + m1, self.n)

    #   Various constructions required for SHA-2 variants.

    def sha256(self, x, n=32):
        """Tranc_n(SHA2-256(x))."""
        return SHA256.new(x).digest()[0:n]

    def sha512(self, x, n=64):
        """Tranc_n(SHA2-512(x))."""
        return SHA512.new(x).digest()[0:n]

    def mgf(self, hash_f, hash_l, mgf_seed, mask_len):
        """NIST SP 800-56B REV. 2 / The Mask Generation Function (MGF)."""
        t = b''
        for c in range((mask_len + hash_l - 1) // hash_l):
            t += hash_f(mgf_seed + c.to_bytes(4, byteorder='big'))
        return t[0:mask_len]

    def mgf_sha256(self, mgf_seed, mask_len):
        """MGF1-SHA1-256(mgfSeed, maskLen)."""
        return self.mgf(self.sha256, 32, mgf_seed, mask_len)

    def mgf_sha512(self, mgf_seed, mask_len):
        """MGF1-SHA1-512(mgfSeed, maskLen)."""
        return self.mgf(self.sha512, 64, mgf_seed, mask_len)

    def hmac(self, hash_f, hash_l, hash_b, k, text):
        """FIPS PUB 198-1 HMAC."""
        if len(k) > hash_b:
            k = hash_f(k)
        ipad = bytearray(hash_b)
        ipad[0:len(k)] = k
        opad = bytearray(ipad)
        for i in range(hash_b):
            ipad[i] ^= 0x36
            opad[i] ^= 0x5C
        return hash_f(opad + hash_f(ipad + text))

    def hmac_sha256(self, k, text, n=32):
        """Trunc_n(HMAC-SHA-256(k, text)): Internal hook."""
        return self.hmac(self.sha256, 32, 64, k, text)[0:n]

    def hmac_sha512(self, k, text, n=64):
        """Trunc_n(HMAC-SHA-256(k, text)): Internal hook."""
        return self.hmac(self.sha512, 64, 128, k, text)[0:n]

    #   10.2    SLH-DSA Using SHA2 for Security Category 1

    def sha256_h_msg(self, r, pk_seed, pk_root, m):
        return self.mgf_sha256( r + pk_seed +
                self.sha256(r + pk_seed + pk_root + m), self.m)

    def sha256_prf(self, pk_seed, sk_seed, adrs):
        return self.sha256(pk_seed + bytes(64 - self.n) +
                                adrs.adrsc() + sk_seed, self.n)

    def sha256_prf_msg(self, sk_prf, opt_rand, m):
        return self.hmac_sha256(sk_prf, opt_rand + m, self.n)

    def sha256_f(self, pk_seed, adrs, m1):
        return self.sha256(pk_seed + bytes(64 - self.n) +
                            adrs.adrsc() + m1, self.n)

    #   10.3    SLH-DSA Using SHA2 for Security Categories 3 and 5

    def sha512_h_msg(self, r, pk_seed, pk_root, m):
        return self.mgf_sha512( r + pk_seed +
                self.sha512(r + pk_seed + pk_root + m), self.m)

    def sha512_prf_msg(self, sk_prf, opt_rand, m):
        return self.hmac_sha512(sk_prf, opt_rand + m, self.n)

    def sha512_h(self, pk_seed, adrs, m2):
        return self.sha512(pk_seed + bytes(128 - self.n) +
                            adrs.adrsc() + m2, self.n)

    #   --- FIPS 205 Algorithms

    def to_int(self, s, n):
        """ Algorithm 2: toInt(X, n). Convert a byte string to an integer."""
        t = 0
        for i in range(n):
            t = (t << 8) + int(s[i])
        return t

    def to_byte(self, x, n):
        """ Algorithm 3: toByte(x, n). Convert an integer to a byte string."""
        t = x
        s = bytearray(n)
        for i in range(n):
            s[n - 1 - i] = t & 0xFF
            t >>= 8
        return s

    def base_2b(self, s, b, out_len):
        """ Algorithm 4: base_2b (X, b, out_len).
            Compute the base 2**b representation of X."""
        i = 0               # in
        c = 0               # bits
        t = 0               # total
        v = []              # baseb
        m = (1 << b) - 1    # mask
        for j in range(out_len):
            while c < b:
                t = (t << 8) + int(s[i])
                i += 1
                c += 8
            c -= b
            v += [ (t >> c) & m ]
        return v

    def chain(self, x, i, s, pk_seed, adrs):
        """ Algorithm 5: chain(X, i, s, PK.seed, ADRS).
            Chaining function used in WOTS+."""
        if i + s >= self.w:
            return None
        t = x
        for j in range(i, i + s):
            adrs.set_hash_address(j)
            t = self.h_f(pk_seed, adrs, t)
        return t

    def wots_pkgen(self, sk_seed, pk_seed, adrs):
        """ Algorithm 6: wots_PKgen(SK.seed, PK.seed, ADRS).
            Generate a WOTS+ public key."""
        sk_adrs = adrs.copy()
        sk_adrs.set_type_and_clear(ADRS.WOTS_PRF)
        sk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        tmp = b''
        for i in range(self.len):
            sk_adrs.set_chain_address(i)
            sk = self.prf(pk_seed, sk_seed, sk_adrs)
            adrs.set_chain_address(i)
            tmp += self.chain(sk, 0, self.w - 1, pk_seed, adrs)
        wotspk_adrs = adrs.copy()
        wotspk_adrs.set_type_and_clear(ADRS.WOTS_PK)
        wotspk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        pk = self.h_t(pk_seed, wotspk_adrs, tmp)
        return pk

    def wots_sign(self, m, sk_seed, pk_seed, adrs):
        """ Algorithm 7: wots_sign(M, SK.seed, PK.seed, ADRS).
            Generate a WOTS+ signature on an n-byte message."""
        csum    =   0
        msg     =   self.base_2b(m, self.lg_w, self.len1)
        for i in range(self.len1):
            csum    +=  self.w - 1 - msg[i]
        csum    <<= ((8 - ((self.len2 * self.lg_w) % 8)) % 8)
        msg     +=  self.base_2b(self.to_byte(csum,
            (self.len2 * self.lg_w + 7) // 8), self.lg_w, self.len2)
        sk_adrs = adrs.copy()
        sk_adrs.set_type_and_clear(ADRS.WOTS_PRF)
        sk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        sig = b''
        for i in range(self.len):
            sk_adrs.set_chain_address(i)
            sk = self.prf(pk_seed, sk_seed, sk_adrs)
            adrs.set_chain_address(i)
            sig += self.chain(sk, 0, msg[i], pk_seed, adrs)

        return sig

    def wots_pk_from_sig(self, sig, m, pk_seed, adrs):
        """ Algorithm 8: wots_PKFromSig(sig, M, PK.seed, ADRS).
            Compute a WOTS+ public key from a message and its signature."""
        csum    =   0
        msg     =   self.base_2b(m, self.lg_w, self.len1)
        for i in range(self.len1):
            csum    +=  self.w - 1 - msg[i]
        csum    <<= ((8 - ((self.len2 * self.lg_w) % 8)) % 8)
        msg     +=  self.base_2b(self.to_byte(csum,
            (self.len2 * self.lg_w + 7) // 8), self.lg_w, self.len2)
        tmp     =   b''
        for i in range(self.len):
            adrs.set_chain_address(i)
            tmp +=  self.chain(sig[i*self.n:(i+1)*self.n],
                                msg[i], self.w - 1 - msg[i],
                                pk_seed, adrs)
        wots_pk_adrs    = adrs.copy()
        wots_pk_adrs.set_type_and_clear(ADRS.WOTS_PK)
        wots_pk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        pk_sig  =   self.h_t(pk_seed, wots_pk_adrs, tmp)
        return  pk_sig

    def xmss_node(self, sk_seed, i, z, pk_seed, adrs):
        """ Algorithm 9: xmss_node(SK.seed, i, z, PK.seed, ADRS).
            Compute the root of a Merkle subtree of WOTS+ public keys."""
        if z > self.hp or i >= 2**(self.hp -  z):
            return None
        if z == 0:
            adrs.set_type_and_clear(ADRS.WOTS_HASH)
            adrs.set_key_pair_address(i)
            node = self.wots_pkgen(sk_seed, pk_seed, adrs)
        else:
            lnode = self.xmss_node(sk_seed, 2 * i, z - 1, pk_seed, adrs)
            rnode = self.xmss_node(sk_seed, 2 * i + 1, z - 1, pk_seed, adrs)
            adrs.set_type_and_clear(ADRS.TREE)
            adrs.set_tree_height(z)
            adrs.set_tree_index(i)
            node = self.h_h(pk_seed, adrs, lnode + rnode)
        return node

    def xmss_sign(self, m, sk_seed, idx, pk_seed, adrs):
        """ Algorithm 10: xmss_sign(M, SK.seed, idx, PK.seed, ADRS).
            Generate an XMSS signature."""
        auth = b''
        for j in range(self.hp):
            k = (idx >> j) ^ 1
            auth += self.xmss_node(sk_seed, k, j, pk_seed, adrs)
        adrs.set_type_and_clear(ADRS.WOTS_HASH)
        adrs.set_key_pair_address(idx)
        sig = self.wots_sign(m, sk_seed, pk_seed, adrs)
        sig_xmss = sig + auth
        return sig_xmss

    def xmss_pk_from_sig(self, idx, sig_xmss, m, pk_seed, adrs):
        """ Algorithm 11: xmss_PKFromSig(idx, SIG_XMSS, M, PK.seed, ADRS).
            Compute an XMSS public key from an XMSS signature."""
        adrs.set_type_and_clear(ADRS.WOTS_HASH)
        adrs.set_key_pair_address(idx)
        sig     = sig_xmss[0:self.len*self.n]
        auth    = sig_xmss[self.len*self.n:]
        node_0  = self.wots_pk_from_sig(sig, m, pk_seed, adrs)

        adrs.set_type_and_clear(ADRS.TREE)
        adrs.set_tree_index(idx)
        for k in range(self.hp):
            adrs.set_tree_height(k + 1)
            auth_k = auth[k*self.n:(k+1)*self.n]
            if (idx >> k) & 1 == 0:
                adrs.set_tree_index(adrs.get_tree_index() // 2)
                node_1  = self.h_h(pk_seed, adrs, node_0 + auth_k)
            else:
                adrs.set_tree_index((adrs.get_tree_index() - 1) // 2)
                node_1  = self.h_h(pk_seed, adrs, auth_k + node_0)
            node_0 = node_1

        return node_0

    def ht_sign(self, m, sk_seed, pk_seed, i_tree, i_leaf):
        """ Algorithm 12: ht_sign(M, SK.seed, PK.seed, idx_tree, idx_leaf).
            Generate a hypertree signature."""
        adrs    = ADRS()
        adrs.set_tree_address(i_tree)
        sig_tmp = self.xmss_sign(m, sk_seed, i_leaf, pk_seed, adrs)
        sig_ht  = sig_tmp
        root    = self.xmss_pk_from_sig(i_leaf, sig_tmp, m, pk_seed, adrs)
        hp_m    = ((1 << self.hp) - 1)
        for j in range(1, self.d):
            i_leaf  =   i_tree & hp_m
            i_tree  =   i_tree >> self.hp
            adrs.set_layer_address(j)
            adrs.set_tree_address(i_tree)
            sig_tmp =   self.xmss_sign(root, sk_seed, i_leaf, pk_seed, adrs)
            sig_ht  +=  sig_tmp
            if j < self.d - 1:
                root = self.xmss_pk_from_sig(i_leaf, sig_tmp, root,
                                                pk_seed, adrs)
        return sig_ht

    def ht_verify(self, m, sig_ht, pk_seed, i_tree, i_leaf, pk_root):
        """ Algorithm 13: ht_verify(M, SIG_HT, PK.seed, idx_tree, idx_leaf,
                            PK.root). Verify a hypertree signature."""
        adrs    = ADRS()
        adrs.set_tree_address(i_tree)
        sig_tmp = sig_ht[0:(self.hp + self.len)*self.n]
        node    = self.xmss_pk_from_sig(i_leaf, sig_tmp, m, pk_seed, adrs)

        hp_m    = ((1 << self.hp) - 1)
        for j in range(1, self.d):
            i_leaf  =   i_tree & hp_m
            i_tree  =   i_tree >> self.hp
            adrs.set_layer_address(j)
            adrs.set_tree_address(i_tree)
            sig_tmp = sig_ht[j*(self.hp + self.len)*self.n:
                            (j+1)*(self.hp + self.len)*self.n]
            node = self.xmss_pk_from_sig(i_leaf, sig_tmp, node,
                                                pk_seed, adrs)
        return node == pk_root

    # PORS+FP specific methods

    def pors_fp_sk_gen(self, sk_seed, pk_seed, adrs, idx):
        sk_adrs = adrs.copy()
        sk_adrs.set_type_and_clear(ADRS.PORS_PRF)
        sk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        sk_adrs.set_tree_index(idx)
        return self.prf(pk_seed, sk_seed, sk_adrs)
    
    def pors_fp_msg_to_indices(self, message_digest, ctr):
        """Sample k distinct positions from [0, t]."""
        seed    = message_digest + self.to_byte(ctr, self.CTR_BYTES)
        found = set()
        current_blk_idx = 0
        while len(found) < self.k:
            block = self.shake256(seed + self.to_byte(current_blk_idx, 4), self.n)
            current_blk_idx += 1
            idx = int.from_bytes(block, 'big') % self.t_pors # TODO: Biased by t? Nachschauen ob/wie man einen PRNG richtig macht, 
            found.add(idx)
        return sorted(found)

    def octopus(self, indices):
        # Following the algorithm description in https://eprint.iacr.org/2025/2069.pdf
        I = set()
        P = set()
        A = []
        pors_h = math.ceil(math.log2(self.t_pors))
        s = self.t_pors - 2**(pors_h - 1) # internal nodes at pors_h height that have children

        # initialize algorithm
        for leaf in indices:
            if leaf < 2 * s:
                I.add(leaf)
            else:
                P.add(leaf - s)

        for level in range(pors_h, 0, -1):
            for i in sorted(I):
                P.add(i >> 1) # add parent
                if (i ^ 1) not in I:
                    A.append((level, i ^ 1))    # sibling needed for authentication
            I = P
            P = set()

        return A
   
    def pors_fp_node(self, sk_seed, pk_seed, adrs, i, z):
        """
        Computes a node in a left-filled Merkle tree.
        z is the height above the bottom-most level (depth h).
        """
        pors_h = math.ceil(math.log2(self.t_pors))
        current_depth = pors_h - z
        s = self.t_pors - 2**(pors_h - 1)

        # Bottom level
        if current_depth == pors_h:
            sk = self.pors_fp_sk_gen(sk_seed, pk_seed, adrs, i)
            adrs.set_tree_height(0)
            adrs.set_tree_index(i)
            return self.h_f(pk_seed, adrs, sk)

        # leaf at depth h-1
        # Leaves at depth h-1 start after the s parents of the 2s leaves at depth h
        if current_depth == pors_h - 1 and i >= s:
            sk = self.pors_fp_sk_gen(sk_seed, pk_seed, adrs, i + s)
            adrs.set_tree_height(0)
            adrs.set_tree_index(i + s) #plus to get the correct "leaf index"
            return self.h_f(pk_seed, adrs, sk)

        # internal node: hash the two children
        lnode = self.pors_fp_node(sk_seed, pk_seed, adrs, 2*i, z-1)
        rnode = self.pors_fp_node(sk_seed, pk_seed, adrs, 2*i+1, z-1)
        
        adrs.set_type_and_clear(ADRS.PORS_TREE)
        adrs.set_tree_height(z)
        adrs.set_tree_index(i)
        return self.h_h(pk_seed, adrs, lnode + rnode)

    def pors_fp_sign(self, md, sk_seed, pk_seed, adrs):
        pors_h = math.ceil(math.log2(self.t_pors))
        ctr = 0
        while True:
            indices = self.pors_fp_msg_to_indices(md, ctr)
            auth_nodes = self.octopus(indices)
            if len(auth_nodes) <= self.mmax:
                break
            ctr += 1
        
        secrets = b''
        for idx in indices: #add revealed secret key values
            secrets += self.pors_fp_sk_gen(sk_seed, pk_seed, adrs, idx)

        auth_vals = b''
        for (lev, pos) in auth_nodes: # add authentication node values
            auth_vals += self.pors_fp_node(sk_seed, pk_seed, adrs, pos, pors_h - lev)
        auth_vals += bytes(self.n * (self.mmax - len(auth_nodes)))  # pad to mmax

        ctr_bytes = self.to_byte(ctr, 4)  # TODO: checken ob 4 passt!?
        sig_pors  = bytes(ctr_bytes) + secrets + auth_vals

        return sig_pors

    def pors_fp_pk_from_sig(self, sig_pors, md, pk_seed, adrs):
        pors_h = math.ceil(math.log2(self.t_pors))
        s = self.t_pors - 2**(pors_h - 1)

        ctr         = self.to_int( sig_pors[0:4], 4)
        secrets   = sig_pors[4:4 + self.k * self.n]
        auth_raw  = sig_pors[4 + self.k * self.n:4 + (self.k + self.mmax) * self.n]

        # recompute indices and auth indices
        indices = self.pors_fp_msg_to_indices(md, ctr)
        auth_nodes    = self.octopus(indices)

        if len(auth_nodes) > self.mmax:
            return None

        # Compute leaf hashes and add to node list
        nodes = {}
        for j, idx in enumerate(indices):
            xi = secrets[j * self.n:(j + 1) * self.n] # get coreect byte from secrets list
            adrs.set_type_and_clear(ADRS.PORS_TREE)
            adrs.set_key_pair_address(adrs.get_key_pair_address())
            adrs.set_tree_height(0)
            adrs.set_tree_index(idx)
            # Determine if this index is at depth h or h-1
            if idx < 2 * s:
                nodes[(pors_h, idx)] = self.h_f(pk_seed, adrs, xi)
            else:
                # Map to depth h-1
                nodes[(pors_h - 1, idx - s)] = self.h_f(pk_seed, adrs, xi)

        # add auth_nodes to node list
        for j, (lev, pos) in enumerate(auth_nodes):
            nodes[(lev, pos)] = auth_raw[j * self.n:(j + 1) * self.n]

        # Climb tree bottom-up
        for lev in range(pors_h, 0, -1):
            new_nodes = {}
            at_level  = {pos: v for (l, pos), v in nodes.items() if l == lev}
            done      = set()
            for pos in at_level:
                if pos in done:
                    continue
                # check for siblings
                left    = pos & ~1        
                right   = left + 1        
                left_v  = nodes.get((lev, left))
                right_v = nodes.get((lev, right))
                if left_v is None or right_v is None:
                    return None
                # add parent node
                parent  = left >> 1
                adrs.set_type_and_clear(ADRS.PORS_TREE)
                adrs.set_key_pair_address(adrs.get_key_pair_address())
                adrs.set_tree_height(pors_h - lev)
                adrs.set_tree_index(parent)
                new_nodes[(lev - 1, parent)] = self.h_h(pk_seed, adrs,
                                                        left_v + right_v)
                done.add(left)
                done.add(right)
            nodes.update(new_nodes)

        return nodes.get((0, 0))        


    def slh_keygen_internal(self, sk_seed, sk_prf, pk_seed, param=None):
        """ Algorithm 18: slh_keygen_internal()."""
        if param != None:
            self.__init__(param)
        adrs    = ADRS()
        adrs.set_layer_address(self.d - 1)
        pk_root = self.xmss_node(sk_seed, 0, self.hp, pk_seed, adrs)
        sk = sk_seed + sk_prf + pk_seed + pk_root
        pk = pk_seed + pk_root
        return (pk, sk)     #   Alg 17 has (sk, pk)

    def split_digest(self, digest):
        """ Helper: Lines 11-16 of Alg 18 / Lines 10-15 of Alg 19."""
        ka1     = self.n #(self.k * self.a + 7) // 8 #Change if technique for index sampling is changed
        md      = digest[0:ka1]
        hd      = self.h // self.d
        hhd     = self.h - hd
        ka2     = ka1 + ((hhd + 7) // 8)
        i_tree  = self.to_int( digest[ka1:ka2], (hhd + 7) // 8) % (2**hhd)
        ka3     = ka2 + ((hd + 7) // 8)
        i_leaf  = self.to_int( digest[ka2:ka3], (hd + 7) // 8) % (2**hd)
        return (md, i_tree, i_leaf)

    def slh_sign_internal(self, m, sk, addrnd, param=None):
        """ Algorithm 19: slh_sign_internal(M, SK). """
        if param != None:
            self.__init__(param)
        adrs    = ADRS()
        sk_seed = sk[       0:  self.n]
        sk_prf  = sk[  self.n:2*self.n]
        pk_seed = sk[2*self.n:3*self.n]
        pk_root = sk[3*self.n:]

        if addrnd == None:
            addrnd = pk_seed

        r       = self.prf_msg(sk_prf, addrnd, m)
        sig     = r

        digest  = self.h_msg(r, pk_seed, pk_root, m)
        (md, i_tree, i_leaf) = self.split_digest(digest)

        adrs.set_tree_address(i_tree)
        adrs.set_type_and_clear(ADRS.PORS_TREE)
        adrs.set_key_pair_address(i_leaf)

        sig_pors = self.pors_fp_sign(md, sk_seed, pk_seed, adrs)
        sig     += sig_pors

        pk_pors = self.pors_fp_pk_from_sig(sig_pors, md, pk_seed, adrs)
        sig_ht  = self.ht_sign(pk_pors, sk_seed, pk_seed, i_tree, i_leaf)
        sig     += sig_ht

        return  sig

    def slh_verify_internal(self, m, sig, pk, param=None):
        """ Algorithm 20: slh_verify_internal(M, SIG, PK)."""
        if param != None:
            self.__init__(param)
        if len(sig) != self.sig_sz or len(pk) != self.pk_sz:
            return False

        pk_seed = pk[:self.n]
        pk_root = pk[self.n:]

        adrs    = ADRS()
        r       = sig[0:self.n]

        pors_sig_sz = self.CTR_BYTES + (self.k + self.mmax) * self.n
        sig_pors = sig[self.n : self.n + pors_sig_sz]
        sig_ht  = sig[self.n + pors_sig_sz:]

        digest  = self.h_msg(r, pk_seed, pk_root, m)
        (md, i_tree, i_leaf) = self.split_digest(digest)

        adrs.set_tree_address(i_tree)
        adrs.set_type_and_clear(ADRS.PORS_TREE)
        adrs.set_key_pair_address(i_leaf)

        pk_pors = self.pors_fp_pk_from_sig(sig_pors, md, pk_seed, adrs)
        return self.ht_verify(pk_pors, sig_ht, pk_seed,
                                i_tree, i_leaf, pk_root)

    def slh_keygen(self, param=None):
        """ Algorithm 21, Algorithm 21 slh_keygen()."""
        if param != None:
            self.__init__(param)
        sk_seed = self.rbg(self.n)
        sk_prf  = self.rbg(self.n)
        pk_seed = self.rbg(self.n)
        return self.slh_keygen_internal(sk_seed, sk_prf, pk_seed)

    def slh_sign(self, m, ctx, sk, addrnd=None, param=None):
        """ Algorithm 22, slh_sign(M, ctx, SK)."""
        if param != None:
            self.__init__(param)
        if len(ctx) > 255:
            return None
        mp = self.to_byte(0, 1) + self.to_byte(len(ctx), 1) + ctx + m
        sig = self.slh_sign_internal(mp, sk, addrnd)
        return sig

    #   shared formatting routine for alg 23 and alg 25

    def hash_slh_dsa_pad(self, m, ctx, ph):
        if len(ctx) > 255:
            return None

        if ph == 'SHA2-256':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x01])
            phm = SHA256.new(m).digest()
        elif ph == 'SHA2-384':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x02])
            phm = SHA384.new(m).digest()
        elif ph == 'SHA2-512':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x03])
            phm = SHA512.new(m).digest()
        elif ph == 'SHA2-224':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x04])
            phm = SHA224.new(m).digest()
        elif ph == 'SHA2-512/224':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x05])
            phm = SHA512.new(m,truncate="224").digest()
        elif ph == 'SHA2-512/256':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x06])
            phm = SHA512.new(m,truncate="256").digest()
        elif ph == 'SHA3-224':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x07])
            phm = SHA3_224.new(m).digest()
        elif ph == 'SHA3-256':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x08])
            phm = SHA3_256.new(m).digest()
        elif ph == 'SHA3-384':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x09])
            phm = SHA3_384.new(m).digest()
        elif ph == 'SHA3-512':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x0A])
            phm = SHA3_512.new(m).digest()
        elif ph == 'SHAKE-128':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x0B])
            phm = SHAKE128.new(m).read(256 // 8)
        elif ph == 'SHAKE-256':
            oid = bytes([   0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                            0x04, 0x02, 0x0C])
            phm = SHAKE256.new(m).read(512 // 8)
        else:
            return None

        mp  = ( self.to_byte(1, 1) +
                self.to_byte(len(ctx), 1) +
                ctx + oid + phm )
        return mp

    def hash_slh_sign(self, m, ctx, ph, sk, addrnd=None, param=None):
        """ Algorithm 23, hash_slh_sign(M, ctx, PH, SK). """
        if param != None:
            self.__init__(param)
        mp = self.hash_slh_dsa_pad(m, ctx, ph)
        if mp == None:
            return None
        sig = self.slh_sign_internal(mp, sk, addrnd)
        return sig

    def slh_verify(self, m, sig, ctx, pk, param=None):
        """ Algorithm 24, slh_verify(M, SIG, ctx, PK)."""
        if param != None:
            self.__init__(param)
        if len(ctx) > 255:
            return False
        mp  = ( self.to_byte(0, 1) + self.to_byte(len(ctx), 1) + ctx + m)
        return self.slh_verify_internal(mp, sig, pk)

    def hash_slh_verify(self, m, sig, ctx, ph, pk, param=None):
        """ Algorithm 25, hash_slh_verify(M, SIG, ctx, PH, PK)."""
        if param != None:
            self.__init__(param)
        if len(ctx) > 255:
            return None
        mp = self.hash_slh_dsa_pad(m, ctx, ph)
        if mp == None:
            return False
        return self.slh_verify_internal(mp, sig, pk)

#   run the test on these functions
if __name__ == '__main__':
    slh_dsa = SLH_DSA()
    test_slhdsa(slh_dsa, '(fips205.py)')

