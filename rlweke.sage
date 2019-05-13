from random import SystemRandom
from hashlib import sha512,sha256
from Crypto.Util.number import long_to_bytes
from sage.stats.distributions.discrete_gaussian_polynomial import DiscreteGaussianDistributionPolynomialSampler

# GLOBAL PARAMETERS
kappa = 128 # security parameter in bits
# m = rom1(str(pi.n(1000000)),Rq) # nothing-up-my-sleeves

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

class RLWE_KE:
    kappa = 128
    n = 512
    q = 25601
    sigma = 8/sqrt(2*pi)
    Z.<z> = PolynomialRing(ZZ,'z')
    Z2.<zz> = PolynomialRing(Zmod(2),'zz')
    phi = z^n+1
    Rq.<x> = PolynomialRing(Zmod(q),'x').quotient(phi)
    m = rom1(str(pi.n(1000000)),Rq) # nothing-up-my-sleeves
    D = DiscreteGaussianDistributionPolynomialSampler(Rq, n, sigma)

    def __init__(self, role):
        if not (role == "A" or role == "B"):
            raise ValueError("role must be either A or B")
        self.role = role
        self.sk = self.D()
        self.e = self.D()
        self.e2 = self.D()
        self.pk = self.m*self.sk + 2*self.e

    def _sig(self,p):
        ''' Sig(a): Rq -> Z2 '''
        b = SystemRandom().getrandbits(1)
        res = 0
        for i,coef in enumerate(p):
            if not (coef>=mod(-floor(self.q/4)+b,self.q) or coef<=mod(floor(self.q/4)+b,self.q)):
                res += self.zz^i
        assert res in self.Z2
        return res

    def _mod2(self,a,sg):
        ''' Mod2(a,sig): Rq x R2 -> R2 '''
        assert a in self.Rq
        assert sg in self.Z2
        aL = map(RR,list(a))
        sL = map(RR,list(sg))
        r = []
        for (ai,si) in zip(aL,sL):
            r.append(((ai + si*((self.q-1)/2))%self.q)%2)
        return self.Z2(r)

    def msg(self,pkA=""):
        if self.role == "A":
            return self.pk
        if self.role == "B":
            if pkA == "":
                raise ValueError("MsgB requires A's message")
            return (self.pk, self._sig(pkA*self.sk + 2*self.e2))

    def key(self,pkj,signal):
        self.K = self.sk * pkj + 2*self.e2
        return long_to_bytes(int(''.join(map(str,self._mod2(self.K,signal).coefficients(sparse=False))),2))

if __name__ == "__main__":
    for _ in range (100):
        alice = RLWE_KE("A")
        bob = RLWE_KE("B")
        mA = alice.msg()
        mB = bob.msg(mA)
        skA = alice.key(mB[0],mB[1])
        skB = bob.key(mA,mB[1])
        print skA == skB
