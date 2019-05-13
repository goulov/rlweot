from random import SystemRandom
from hashlib import sha512,sha384,sha256
from Crypto.Util.number import long_to_bytes
import os
from sage.stats.distributions.discrete_gaussian_polynomial import DiscreteGaussianDistributionPolynomialSampler
from rlweke import RLWE_KE

from Crypto.Cipher import AES
bs = AES.block_size
aes_pad = lambda s: s + (bs - len(s) % bs) * chr(bs - len(s) % bs)
aes_unpad = lambda s: s[:-ord(s[len(s)-1:])]

# GLOBAL PARAMETERS
kappa = 128 # security parameter in bits
kappaB = kappa/8 # security parameter in bytes

def bin2(i):
    return bin(i)[2:]

def sumstrings(m1,m2):
    assert len(m1) == len(m2)
    bs1=int("".join([bin(ord(ch))[2:].zfill(8) for ch in m1 ]),2)
    bs2=int("".join([bin(ord(ch))[2:].zfill(8) for ch in m2 ]),2)
    r=bin(bs1^^bs2)[2:].zfill(8*len(m1))
    rs="".join([ chr(int(r[i:i+8],2)) for i in range(0,len(r),8)])
    return rs

def rom1(m,Rq):
    n = Rq.degree()
    x = Rq.gen()
    r=Rq(0)
    h=sha256()
    for i in range(n) :
        h.update(m+str(i))
        a=Rq(int(h.hexdigest(),16))
        r+=a*x^i
    assert r in Rq
    return r

def rom2(m):
    h = sha512()
    h.update(m)
    return h.digest() # return elements of the size of the key of RLWE

def rom3(m):
    m1=m[:len(m)//2]
    m2=m[len(m)//2:]
    h1=sha384()
    h2=sha384()
    h1.update(m1)
    h2.update(m2)
    return h1.digest()+h2.digest() # return elements of the size of the key of RLWE + 2* security parameter

def rom4(m):
    h=sha256()
    h.update(m)
    return h.digest()[:kappaB] # return elements of the size of the security parameter

def AESenc(key,m,iv=""):
    if iv == "":
        iv = os.urandom(AES.block_size)
    h = sha256()
    h.update(key)
    hkey = h.digest()
    aes = AES.new(hkey, AES.MODE_CBC, iv)
    enc = aes.encrypt(aes_pad(m))
    return iv+enc

def AESdec(key,enc,iv=""):
    if iv == "":
        iv = enc[:AES.block_size]
        enc = enc[AES.block_size:]
    h = sha256()
    h.update(key)
    hkey = h.digest()
    aes = AES.new(hkey, AES.MODE_CBC, iv)
    m = aes_unpad(aes.decrypt(enc))
    return m

def SENC(key,m,z,iv=""):
    return AESenc(key,m+z,iv)

def SDEC(key,enc,iv=""):
    m2=AESdec(key,enc,iv)
    return (m2[:-kappaB],m2[-kappaB:])

class OTsender:
    def __init__(self,sid,m0,m1):
        self.sid = sid
        self.rlweke = RLWE_KE("B")
        self.m0 = m0
        self.m1 = m1

    def send1(self,sid,pr0,r):
        assert sid == self.sid
        h = rom1(bin2(sid)+bin2(r),self.rlweke.Rq)
        pr1 = pr0 + h
        assert pr1 in self.rlweke.Rq
        (ps0,sigma0) = self.rlweke.msg(pr0)
        (ps1,sigma1) = self.rlweke.msg(pr1)
        assert ps0 == ps1
        ps = ps0
        assert ps in self.rlweke.Rq
        self.sks0 = self.rlweke.key(pr0,sigma0)
        self.sks1 = self.rlweke.key(pr1,sigma1)
        w0 = os.urandom(kappaB)
        w1 = os.urandom(kappaB)
        bar_sks0 = rom2(bin2(sid) + self.sks0)
        bar_sks1 = rom2(bin2(sid) + self.sks1)
        z0 = os.urandom(kappaB)
        z1 = os.urandom(kappaB)
        a0 = SENC(bar_sks0,w0,z0)
        a1 = SENC(bar_sks1,w1,z1)
        bar_w0 = rom3(bin2(sid) + w0)
        bar_w1 = rom3(bin2(sid) + w1)
        u0 = sumstrings(bar_w0, w1 + bar_sks1 + z1)
        u1 = sumstrings(bar_w1, w0 + bar_sks0 + z0)
        self.ch = rom4(bin2(sid)+w0+w1+z0+z1)
        return (sid,ps,sigma0,sigma1,a0,a1,u0,u1)

    def send2(self,sid,ch2):
        assert sid == self.sid
        if ch2 != self.ch:
            print "[SENDER]: CHALLENGES DO NOT MATCH, ABORTING..."
            return -1
        else:
            c0 = AESenc(self.sks0,self.m0)
            c1 = AESenc(self.sks1,self.m1)
            return (self.sid, c0, c1)

class OTreceiver:
    def __init__(self,sid,b):
        self.sid = sid
        if b != 0 and b != 1:
            raise ValueError("b must be either 0 or 1")
        self.b = b
        self.rlweke = RLWE_KE("A")

    def recv1(self,sid):
        assert sid == self.sid
        prb = self.rlweke.pk
        r = SystemRandom().getrandbits(kappa)
        h = rom1(bin2(sid)+bin2(r), self.rlweke.Rq)
        if self.b == 0:
            pr0 = prb
        elif self.b == 1:
            pr0 = prb - h
        return (sid,pr0,r)

    def recv2(self,sid,ps,sigma0,sigma1,a0,a1,u0,u1):
        assert sid == self.sid
        if self.b == 0:
            self.skr = self.rlweke.key(ps,sigma0)
            bar_skr = rom2(bin2(sid) + self.skr)
            (x0,y0) = SDEC(bar_skr,a0)
            bar_x0 = rom3(bin2(sid) + x0)
            u0x0=sumstrings(u0,bar_x0)
            x1 = u0x0[:kappaB]
            bar_skr1 = u0x0[kappaB:-kappaB]
            y1 = u0x0[-kappaB:]
            a1 = SENC(bar_skr1,x1,y1)
            bar_x1 = rom3(bin2(sid) + x1)
            u1x1=sumstrings(u1,bar_x1)
            xp0 = u1x1[:kappaB]
            bar_skr0 = u1x1[kappaB:-kappaB]
            yp0 = u1x1[-kappaB:]
            if xp0 != x0 or y0!= yp0 or bar_skr0 != bar_skr or a0 != SENC(bar_skr0,x0,y0,a0[:16]):
                print "[RECEIVER]: CHECKS FAIL, ABORTING..."
        else: 
            self.skr = self.rlweke.key(ps,sigma1)
            bar_skr = rom2(bin2(sid) + self.skr)
            (x1,y1) = SDEC(bar_skr,a1)
            bar_x1 = rom3(bin2(sid) + x1)
            u1x1=sumstrings(u1,bar_x1)
            x0 = u1x1[:kappaB]
            bar_skr0 = u1x1[kappaB:-kappaB]
            y0 = u1x1[-kappaB:]
            a0 = SENC(bar_skr0,x0,y0)
            bar_x0 = rom3(bin2(sid) + x0)
            u0x0=sumstrings(u0,bar_x0)
            xp1 = u0x0[:kappaB]
            bar_skr1 = u0x0[kappaB:-kappaB]
            yp1 = u0x0[-kappaB:]
            if xp1 != x1 or y1!= yp1 or bar_skr1 != bar_skr or a1 != SENC(bar_skr1,x1,y1,a1[:16]):
                print "[RECEIVER]: CHECKS FAIL, ABORTING..."
        ch = rom4(bin2(sid) + x0 + x1 + y0 + y1)
        return (sid,ch)

    def recv3(self,sid,c0,c1):
        assert sid == self.sid
        if self.b == 0:
            mb = AESdec(self.skr,c0)
        else:
            mb = AESdec(self.skr,c1)
        return mb

if __name__ == "__main__":
    for _ in range(100):
        sid = SystemRandom().getrandbits(kappa)
        m0 = "this is message 0"
        m1 = "this is message 1"
        b = SystemRandom().getrandbits(1)
        S = OTsender(sid,m0,m1)
        R = OTreceiver(sid,b)
        (_,pr0,r) = R.recv1(sid)
        (_,ps,sig0,sig1,a0,a1,u0,u1) = S.send1(sid,pr0,r)
        (_,chp) = R.recv2(sid,ps,sig0,sig1,a0,a1,u0,u1)
        (_,c0,c1) = S.send2(sid,chp)
        mb = R.recv3(sid,c0,c1)
        if (b == 0 and mb == m0) or (b == 1 and mb == m1):
            print "GOOD!"
        else:
            print "FAILED!"
