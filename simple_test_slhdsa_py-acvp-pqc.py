from fips205withPlusC import SLH_DSA

#from fips205 import SLH_DSA

import os

def test_h_msg_with_counter():

    
    slh = SLH_DSA(param='SLH-DSA-SHAKE-256sPlusC')

    r = bytes([0] * slh.n)
    pk_seed = bytes([0] * slh.n)
    pk_root = bytes([0] * slh.n)
    counter = (0).to_bytes(4, 'big') 
    m = bytes([0x00])

    md = slh.shake_h_msg_with_counter(r, pk_seed, pk_root, m, counter)
    print(f"mhash: {md.hex()}")
    print("Length of mhash:", len(md))



if __name__ == "__main__":
    
    #slh = SLH_DSA(param='SLH-DSA-SHAKE-256s')
    slh = SLH_DSA(param='SLH-DSA-SHAKE-256sPlusC')

    print("n:", slh.n)
    print("h:", slh.h)
    print("d:", slh.d)
    print("hp:", slh.hp)
    print("a:", slh.a)
    print("k:", slh.k)
    print("w:", slh.w)

    print("len1:", slh.len1)
    print("len:", slh.len)    
    print("pk_sz:", slh.pk_sz)
    print("sk_sz:", slh.sk_sz)
    print("sig_sz:", slh.sig_sz)

    print("m:", slh.m)
    
    """ print("Max hash trials wots:", slh.MAX_HASH_TRIALS_WOTS)
    print("wanted checksum:", slh.WANTED_CHECKSUM)
    print("wots zero bits:", slh.WOTS_ZERO_BITS)
    print("wots counter bytes:", slh.WOTS_COUNTER_BYTES)
    print("fors zero last bits:", slh.FORS_ZERO_LAST_BITS)
    print("max hash trials fors:", slh.MAX_HASH_TRIALS_FORS)"""

    skSeed = bytes([0x00] * slh.n)
    skPrf  = bytes([0x00] * slh.n)
    pkSeed = bytes([0x00] * slh.n)

    # generate keys
    # use internal function to skip needed randomness
    pk, sk = slh.slh_keygen_internal(skSeed, skPrf, pkSeed)

    message = b"Test message"

    # sign message
    ctx = b""
    signature = slh.slh_sign_internal(message, sk, addrnd=None)

    # verfiy signature
    is_valid = slh.slh_verify_internal(message, signature, pk)

    print("PK:", pk.hex())
    print("SK:", sk.hex())
    print("Message:", message.hex())

    print("Valid:", is_valid)
    print("length signature:", len(signature))
