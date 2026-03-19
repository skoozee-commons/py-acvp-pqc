#   fips205.py
#   2023-11-24  Markku-Juhani O. Saarinen < mjos@iki.fi>. See LICENSE

#   === FIPS 205 implementation https://doi.org/10.6028/NIST.FIPS.205
#   SLH-DSA / Stateless Hash-Based Digital Signature Standard

#   test_slhdsa is only used by the unit test in the end
import math
from enum import Enum

from test_slhdsa import test_slhdsa

#   hash functions
from Crypto.Hash import SHAKE128, SHAKE256
from Crypto.Hash import SHA224, SHA256, SHA384, SHA512
from Crypto.Hash import SHA3_224, SHA3_256, SHA3_384, SHA3_512

class Encoding(Enum):
    TLFC = 'tlfc'
    TL1C = 'tl1c'
    TSL  = 'tsl'


# TODO: Find correct position for this methods
def initialize_l_table(w: int, v:int) -> list[list[int]]:
    """Calculates the l table which contains the number of ways a sum can be represented with a number of elements"""
    max_sum = v * (w - 1) 

    # l_table[l][s] = number of vectors of length l with sum s
    l_table = [[0 for s in range(max_sum + 1)] for l in range(v + 1)]

    l_table[0][0] = 1

    # find ji satisfying lemma 8 of "At the Top of the Hypercube – Better Size-Time Tradeoffs for Hash-Based Signatures"
    for l in range(1, v + 1):
        for s in range(0, l * (w - 1) + 1):  # possible sums for this length
            for k in range(w):         # value of the first coordinate
                if s - k  >= 0:
                    l_table[l][s] += l_table[l - 1][s - k]
    return l_table

def map_to_vertex(w: int, v: int, d:int, x:int, l_table: list[list[int]]) -> list[int]:
    """Maps an integer x to a vertex in layer d of a hypercube [w]^v. According to Construction 5 in 'At the Top of the Hypercube - Better Size-Time Tradeoffs
    for Hash-Based Signatures'"""
    a = [0] * v
    xi = x
    di = d

    for i in range(v - 1):
        jmin = max(0, di - (w - 1) * (v - i - 1))
        jmax = min(w - 1, di)
        acc = 0
        for ji in range(jmin, jmax + 1):
            term = l_table[v - i - 1][di - ji]
            if acc + term > xi:
                break
            acc += term

        a[i] = w - ji
        xi -= acc
        di -= ji

    a[v - 1] = w - xi - di
    
    return a

def map_to_integer(w: int, v: int, a: list[int], l_table: list[list[int]]) -> tuple[int, int]:
    """
    Maps a vertex a in layer d of a hypercube [w]^v to an integer x. According to Construction 5 in 'At the Top of the Hypercube - Better Size-Time Tradeoffs
    for Hash-Based Signatures'
    """
    x_next = 0
    d_next = w - a[v - 1]

    for i in range(v - 2, -1, -1):
        ji = w - a[i]
        di = d_next + ji

        jmin = max(0, di - (w - 1) * (v - i - 1))

        acc = 0
        for j in range(jmin, ji):
            acc += l_table[v - i - 1][di - j]

        xi = x_next + acc

        x_next = xi
        d_next = di

    return x_next, d_next

def compute_d0_tl1c(w: int, v: int, l_table: list[list[int]], security_bits: int) -> int:
    """
    finds minimum d0 for TL1C encoding according to construction 3 in hypercube paper
    """
    target = 2 ** security_bits
    cumulative = 0
    for d in range(v * (w - 1) + 1):
        cumulative += l_table[v][d]
        if cumulative >= target:
            return d
    raise ValueError("Hypercube too small for TL1C")

def compute_d0_tsl(w: int, v: int, l_table: list[list[int]], security_bits: int) -> int:
    """
    finds minimum d0 for TSL encoding according to construction 4 in the paper
    """
    target = 2 ** security_bits
    for d in range(v * (w - 1) + 1):
        if l_table[v][d] >= target:
            return d
    raise ValueError("Hypercube too small for TSL at this security level")

def compute_lagrange_multipliers(sum_ld: float, sum_ld_cd: float, sum_ld_cd2: float, mu_scaled: int, wv: int) -> tuple[float, float] | None:
    """
    Computes lagrange multipliers according to Theorem 1 in https://eprint.iacr.org/2025/889.pdf for a given d0 and  
    Based on implementations of the authors: https://github.com/khovratovich/hypercube/blob/main/code/opt-compute.py 
    """
    # compute A
    v1 = (sum_ld_cd * sum_ld_cd) /  (sum_ld * sum_ld)
    v2 = mu_scaled * sum_ld_cd * sum_ld_cd - sum_ld_cd2 * wv  # multiply right term by wv as mu is scaled to keep precision
    v3 = (mu_scaled * sum_ld - wv) * sum_ld # multiply right term by wv as mu is scaled to keep precision

    if v3 == 0:
        return None
    
    discr = v1 - (v2/v3)

    if discr < 0:
        return None
    
    sqrt_discr = math.sqrt(discr)

    lambda2 = sum_ld_cd / sum_ld + sqrt_discr
    lambda1 = sum_ld * sqrt_discr / 2 # TODO: checken warum in code von Paper downscaled Variante von lambda 1 verwendet wird

    return lambda1, lambda2

def compute_density(d0: int, lambda1: float, lambda2: float, l_table: list[list[int]], v: int) -> tuple[list[float, float]]:
    mu_d_scaled = []
    cost        = 0

    for d in range(d0 + 1):
        val = (lambda2 - d) / (2 * lambda1)
        val = max(val, 0)
        mu_d_scaled.append(val)
        cost += val * l_table[v][d] * d

    return mu_d_scaled, cost


def compute_params_tlfc(w: int, v: int, l_table: list[list[int]], security_bits: int) -> tuple[int | None, list[float]| None]:
    """
    Finds optimal d0 and density values {mu_d} for TLFC (Construction 2),
    using Theorem 1 with mu = 2^{-security_bits}.
    Based on implementation of the authors: https://github.com/khovratovich/hypercube/blob/main/code/opt-compute.py
    """
    wv         = w ** v
    mu_scaled  = math.ceil(wv / (2 ** security_bits))  # mu * w^v, matches opt_compute scaling
    max_d      = v * (w - 1)

    best_d0        = None
    best_cost      = float('inf')
    best_mu = None

    for d0 in range(1, max_d):

        #compute sums
        sum_ld     = sum(l_table[v][d] for d in range(d0 + 1))
        sum_ld_cd  = sum(l_table[v][d] * d for d in range(d0 + 1))
        sum_ld_cd2 = sum(l_table[v][d] * d * d for d in range(d0 + 1))

        multipliers = compute_lagrange_multipliers(sum_ld, sum_ld_cd, sum_ld_cd2, mu_scaled, wv)

        if multipliers is None:
            continue

        lambda1 , lambda2 = multipliers

        mu_d, cost = compute_density(d0, lambda1, lambda2, l_table, v)
               
        if cost < best_cost:
            best_cost      = cost
            best_d0        = d0
            best_mu = mu_d[:]

    return best_d0, best_mu


#   A class for handling Addresses (Section 4.2.)

class ADRS:
    #   type constants
    WOTS_HASH   = 0
    WOTS_PK     = 1
    TREE        = 2
    FORS_TREE   = 3
    FORS_ROOTS  = 4
    WOTS_PRF    = 5
    FORS_PRF    = 6

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

SLH_DSA_PARAM = {       #   ( hashname, n,  h,  d,  hp, a,  k, lg_w, m )
    'SLH-DSA-SHA2-128s':    ( 'SHA2',   16, 63, 7,  9,  12, 14, 4,  30 ),
    'SLH-DSA-SHAKE-128s':   ( 'SHAKE',  16, 63, 7,  9,  12, 14, 4,  30 ), 
    'SLH-DSA-SHA2-128f':    ( 'SHA2',   16, 66, 22, 3,  6,  33, 4,  34 ),
    'SLH-DSA-SHAKE-128f':   ( 'SHAKE',  16, 66, 22, 3,  6,  33, 4,  34 ),
    'SLH-DSA-SHA2-192s':    ( 'SHA2',   24, 63, 7,  9,  14, 17, 4,  39 ),
    'SLH-DSA-SHAKE-192s':   ( 'SHAKE',  24, 63, 7,  9,  14, 17, 4,  39 ),
    'SLH-DSA-SHA2-192f':    ( 'SHA2',   24, 66, 22, 3,  8,  33, 4,  42 ),
    'SLH-DSA-SHAKE-192f':   ( 'SHAKE',  24, 66, 22, 3,  8,  33, 4,  42 ),
    'SLH-DSA-SHA2-256s':    ( 'SHA2',   32, 64, 8,  8,  14, 22, 4,  47 ),
    'SLH-DSA-SHAKE-256s':   ( 'SHAKE',  32, 64, 8,  8,  14, 22, 4,  47 ),
    'SLH-DSA-SHA2-256f':    ( 'SHA2',   32, 68, 17, 4,  9,  35, 4,  49 ),
    'SLH-DSA-SHAKE-256f':   ( 'SHAKE',  32, 68, 17, 4,  9,  35, 4,  49 )
}

#   SLH-DSA Implementation

class SLH_DSA:

    ENCODING_TL1C = 'tl1c'   # Top Layers with 1-Chain Checksum  (Construction 3)
    ENCODING_TLFC = 'tlfc'   # Top Layers with Full Checksum      (Construction 2)
    ENCODING_TSL  = 'tsl'    # Top Single Layer                   (Construction 4)

    #   initialize
    def __init__(self,  param='SLH-DSA-SHAKE-128f', encoding = "tsl"):

        #   set parameters
        if isinstance(param, str):
            if param not in SLH_DSA_PARAM:
                raise ValueError
            (self.hashname, self.n, self.h, self.d, self.hp,
                self.a, self.k, self.lg_w, self.m) = SLH_DSA_PARAM[param]
        else:
            (self.hashname, self.n, self.h, self.d, self.hp,
                self.a, self.k, self.lg_w, self.m) = param
            
        if encoding not in (self.ENCODING_TL1C,
                            self.ENCODING_TLFC,
                            self.ENCODING_TSL):
            raise ValueError(f"Unknown encoding: {encoding!r} ")
            
        self.encoding = encoding

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
        self.len1   = (8 * self.n + (self.lg_w - 1)) // self.lg_w # how many chains are needed to encode a message
        self.len2 = 0
             
        self.l_table = initialize_l_table(self.w, self.len1)

        # init hypercube params per encoding
        if encoding == self.ENCODING_TL1C:
            self.hc_d0 = compute_d0_tl1c(self.w, self.len1, self.l_table, 8 * self.n)
            self.len2 = 1 
        elif encoding == self.ENCODING_TLFC:
            lambda_bits = 8 * self.n
            log4_lambda = math.log(lambda_bits, 4)
            min_v = math.floor((lambda_bits + log4_lambda) / math.log2(self.w)) + 1

            v = max(self.len1 + 1, min_v)
            while True:
                l_table_candidate = initialize_l_table(self.w, v)
                d0, mu_d = compute_params_tlfc(
                    self.w, v, l_table_candidate, lambda_bits
                )
                if d0 is not None:
                    self.len1        = v
                    self.l_table     = l_table_candidate
                    self.hc_d0       = d0
                    self.hc_mu     = mu_d
                    break
                v += 1
            self.len2 = math.ceil(math.log(self.hc_d0 + 1) / math.log(self.w)) # checksum length
      
        elif encoding == self.ENCODING_TSL:
            #TODO: Auslagern: Sollte eigentlich in Parametersets schon festegelegt sein und nicht hier erst per trial and error herausgefunden werden, gilt auch für TLFC
            lambda_bits = 8 * self.n
            exponent = lambda_bits + math.log(lambda_bits, 4)
            v = self.len1 + 1
            # Find v such that hypercube should be large enough
            while True:
                wv = self.w ** v
                if 2 ** exponent < wv:
                    break
                v +=1

            l_table_candidate = initialize_l_table(self.w, v)
            
            d0 = compute_d0_tsl(self.w, v, l_table_candidate, 8 * self.n)
            self.len1    = v          
            self.l_table = l_table_candidate
            self.hc_d0   = d0
        
            self.len2 = 0      

        self.len    = self.len1 + self.len2
        
        #   external parameter sizes
        self.pk_sz  = 2 * self.n
        self.sk_sz  = 4 * self.n
        self.sig_sz = (1 + self.k*(1 + self.a) + self.h +
                        self.d * self.len) * self.n
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

    # Hypercube helper functions  
    def psi_tl1c(self, x):
        """
        Implementation of the Ψ mapping for TL1C (Construction 3).
        Maps an integer x to a vertex in the top d0 layers.
        """  

        w, v, d0   = self.w, self.len1, self.hc_d0

        total_number_of_vertices = w**v
        top_capacity = sum(self.l_table[v][0:d0+1])

        vertex_number_x = 0
        target_layer = 0

        # find target layer for x
        for d in range(d0+1):
            vertices_up_to_d_minus_1 = sum(self.l_table[v][0:d])
            vertices_up_to_d = sum(self.l_table[v][0:d + 1])
            lower_bound = total_number_of_vertices * (vertices_up_to_d_minus_1/top_capacity)
            upper_bound = total_number_of_vertices * (vertices_up_to_d/top_capacity)
            if lower_bound <= x < upper_bound:
                target_layer = d
                # calculate index of vertex in target layer
                vertex_number_x = ((x*top_capacity) - (total_number_of_vertices * vertices_up_to_d_minus_1)) // total_number_of_vertices
                break
                
        # get corresponding vertex for x in target layer
        return map_to_vertex(w, v, target_layer, vertex_number_x, self.l_table), target_layer
        

    def psi_tsl(self, x):
        """
        Implementation of the Ψ mapping for TSL (Construction 4).
        Maps an integer x to a vertex in a single large layer d0.
        """  

        w, v, d0   = self.w, self.len1, self.hc_d0

        total_number_of_vertices = self.w **v
        layer_size_d0 = self.l_table[v][d0]

        # calculate index of vertex in layer d0
        x_layer_d0 = (x*layer_size_d0) // total_number_of_vertices

        return map_to_vertex(w, v, d0, x_layer_d0, self.l_table), d0
        

    def psi_tlfc(self, x):
        """
        Implementation of the Ψ mapping for TLFC (Construction 2).
        Maps an integer x to a vertex in the top d0 layers.
        """  

        w, v  = self.w, self.len1

        total_number_of_vertices = w**v

        current_lower_bound = 0
        target_layer = -1

        # find target layer for x
        for d in range(v*(w-1)):
    
            current_upper_bound = current_lower_bound + (total_number_of_vertices * self.l_table[v][d] * self.hc_mu[d])

            if current_lower_bound <= x < current_upper_bound:
                target_layer = d
                break

            current_lower_bound = current_upper_bound

        # calculate index of vertex in top d0 layers
        vertex_number_x = math.floor((x - (current_lower_bound)) / (self.hc_mu[target_layer] * total_number_of_vertices))

        # get corresponding vertex for x in top d0 layers
        return map_to_vertex(w, v, target_layer, vertex_number_x, self.l_table), target_layer
    

    def psi(self, x):
        """Use the correct Ψ for the encoding."""
        if self.encoding == self.ENCODING_TL1C:
            return self.psi_tl1c(x)
        elif self.encoding == self.ENCODING_TLFC:
            return self.psi_tlfc(x)
        else:   
            return self.psi_tsl(x)
    
    def max_lengths(self):
        """Upper bound for chain() for each of the self.len chains, this depends on the checksum"""
        result = [self.w] * self.len1

        if self.encoding == self.ENCODING_TL1C:
            result.append(self.hc_d0 + 1)
        else:
            result += [self.w] * self.len2
        return result   
    
    def message_into_hash_chain_lengths(self, m):
        m_int = int.from_bytes(m, byteorder='big') % (self.w ** self.len1)
        vertex, d = self.psi(m_int)

        lengths = [coord - 1 for coord in vertex]

        # add checksum, not needed for TSL
        if self.encoding == self.ENCODING_TL1C:
            lengths.append(d)   
        elif self.encoding == self.ENCODING_TLFC:
            lengths += self.base_2b(self.to_byte(d, self.len2), self.lg_w, self.len2)
            
        return lengths


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

    def chain(self, x, i, s, pk_seed, adrs, max_len = None):
        """ Algorithm 5: chain(X, i, s, PK.seed, ADRS).
            Chaining function used in WOTS+."""
        if max_len is None:
            max_len = self.w
        if i + s >= max_len:
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

        for i, max_length in enumerate(self.max_lengths()):
            sk_adrs.set_chain_address(i)
            sk = self.prf(pk_seed, sk_seed, sk_adrs)
            adrs.set_chain_address(i)
            tmp += self.chain(sk, 0, max_length - 1, pk_seed, adrs, max_length)

        wotspk_adrs = adrs.copy()
        wotspk_adrs.set_type_and_clear(ADRS.WOTS_PK)
        wotspk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        pk = self.h_t(pk_seed, wotspk_adrs, tmp)
        return pk

    def wots_sign(self, m, sk_seed, pk_seed, adrs):
        """ Algorithm 7: wots_sign(M, SK.seed, PK.seed, ADRS).
            Generate a WOTS+ signature with non-uniform encoding on an n-byte message."""

        lengths = self.message_into_hash_chain_lengths(m)
        
        max_lengths = self.max_lengths()

        sk_adrs = adrs.copy()
        sk_adrs.set_type_and_clear(ADRS.WOTS_PRF)
        sk_adrs.set_key_pair_address(adrs.get_key_pair_address())
   
        sig = b''
        for i in range(self.len):
            sk_adrs.set_chain_address(i)
            sk = self.prf(pk_seed, sk_seed, sk_adrs)
            adrs.set_chain_address(i)
            sig += self.chain(sk, 0, lengths[i], pk_seed, adrs, max_lengths[i])

        return sig

    def wots_pk_from_sig(self, sig, m, pk_seed, adrs):
        """ Algorithm 8: wots_PKFromSig(sig, M, PK.seed, ADRS).
            Compute a WOTS+ public key from a message and its signature."""
        
        lengths = self.message_into_hash_chain_lengths(m)
        
        max_lengths = self.max_lengths()
        tmp     =   b''
        
        for i in range(self.len):
            adrs.set_chain_address(i)
            remaining_steps = max_lengths[i] - 1 - lengths[i]
            tmp +=  self.chain(sig[i*self.n:(i+1)*self.n],
                                lengths[i], remaining_steps,
                                pk_seed, adrs, max_lengths[i])


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

    def fors_sk_gen(self, sk_seed, pk_seed, adrs, idx):
        """ Algorithm 14: fors_SKgen(SK.seed, PK.seed, ADRS, idx).
            Generate a FORS private-key value."""
        sk_adrs = adrs.copy()
        sk_adrs.set_type_and_clear(ADRS.FORS_PRF)
        sk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        sk_adrs.set_tree_index(idx)
        return self.prf(pk_seed, sk_seed, sk_adrs)

    def fors_node(self, sk_seed, i, z, pk_seed, adrs):
        """ Algorithm 15: fors_node(SK.seed, i, z, PK.seed, ADRS).
            Compute the root of a Merkle subtree of FORS public values."""

        if z > self.a or i >= (self.k << (self.a - z)):
            return None
        if z == 0:
            sk = self.fors_sk_gen(sk_seed, pk_seed, adrs, i)
            adrs.set_tree_height(0)
            adrs.set_tree_index(i)
            node = self.h_f(pk_seed, adrs, sk)
        else:
            lnode = self.fors_node(sk_seed, 2 * i, z - 1, pk_seed, adrs)
            rnode = self.fors_node(sk_seed, 2 * i + 1, z - 1, pk_seed, adrs)
            adrs.set_tree_height(z)
            adrs.set_tree_index(i)
            node = self.h_h(pk_seed, adrs, lnode + rnode)
        return node

    def fors_sign(self, md, sk_seed, pk_seed, adrs):
        """ Algorithm 16: fors_sign(md, SK.seed, PK.seed, ADRS).
            Generate a FORS signature."""
        sig_fors = b''
        indices = self.base_2b(md, self.a, self.k)
        for i in range(self.k):
            sig_fors += self.fors_sk_gen(sk_seed, pk_seed, adrs,
                                            (i << self.a) + indices[i])
            for j in range(self.a):
                s = (indices[i] >> j) ^ 1
                sig_fors += self.fors_node(sk_seed,
                                            (i << (self.a - j)) + s, j,
                                            pk_seed, adrs)
        return sig_fors

    def fors_pk_from_sig(self, sig_fors, md, pk_seed, adrs):
        """ Algorithm 17: fors_pkFromSig(SIG_FORS, md, PK.seed, ADRS).
            Compute a FORS public key from a FORS signature."""
        def get_sk(sig_fors, i):
            return sig_fors[i*(self.a+1)*self.n:(i*(self.a+1)+1)*self.n]

        def get_auth(sig_fors, i):
            return sig_fors[(i*(self.a+1)+1)*self.n:(i+1)*(self.a+1)*self.n]

        indices = self.base_2b(md, self.a, self.k)

        root = b''
        for i in range(self.k):
            sk      = get_sk(sig_fors, i)
            adrs.set_tree_height(0)
            adrs.set_tree_index((i << self.a) + indices[i])
            node_0  = self.h_f(pk_seed, adrs, sk)

            auth    = get_auth(sig_fors, i)
            for j in range(self.a):
                auth_j = auth[j*self.n:(j+1)*self.n]
                adrs.set_tree_height(j + 1)
                if (indices[i] >> j) & 1 == 0:
                    adrs.set_tree_index(adrs.get_tree_index() // 2)
                    node_1 = self.h_h(pk_seed, adrs, node_0 + auth_j)
                else:
                    adrs.set_tree_index((adrs.get_tree_index() - 1) // 2)
                    node_1 = self.h_h(pk_seed, adrs, auth_j + node_0)
                node_0 = node_1
            root += node_0

        fors_pk_adrs = adrs.copy()
        fors_pk_adrs.set_type_and_clear(ADRS.FORS_ROOTS)
        fors_pk_adrs.set_key_pair_address(adrs.get_key_pair_address())
        pk  = self.h_t(pk_seed, fors_pk_adrs, root)
        return pk

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
        ka1     = (self.k * self.a + 7) // 8
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
        adrs.set_type_and_clear(ADRS.FORS_TREE)
        adrs.set_key_pair_address(i_leaf)

        sig_fors = self.fors_sign(md, sk_seed, pk_seed, adrs)
        sig     += sig_fors

        pk_fors = self.fors_pk_from_sig(sig_fors, md, pk_seed, adrs)
        sig_ht  = self.ht_sign(pk_fors, sk_seed, pk_seed, i_tree, i_leaf)
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
        sig_fors = sig[self.n:(1+self.k*(1+self.a))*self.n]
        sig_ht  = sig[(1 + self.k*(1 + self.a))*self.n:]

        digest  = self.h_msg(r, pk_seed, pk_root, m)
        (md, i_tree, i_leaf) = self.split_digest(digest)

        adrs.set_tree_address(i_tree)
        adrs.set_type_and_clear(ADRS.FORS_TREE)
        adrs.set_key_pair_address(i_leaf)

        pk_fors = self.fors_pk_from_sig(sig_fors, md, pk_seed, adrs)
        return self.ht_verify(pk_fors, sig_ht, pk_seed,
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

