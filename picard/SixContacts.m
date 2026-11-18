// Magma V2. Exact algebra; the global arithmetic proof is in report.md.
K<r> := QuadraticField(-3);
S<X,Y> := PolynomialRing(K,2);
u:=X+r*Y; v:=X-r*Y;
assert u^6-v^6 eq 12*r*X*Y*(X^2-Y^2)*(X^2-9*Y^2);
F<U,V> := FunctionField(Rationals(),2);
P<x> := PolynomialRing(F);
q:=x^2+2*x-2;
g:=4*U*(2*x-1)-V*x^3*(x+4);
f:=q*g;
fbar:=q*(4*V*(2*x-1)-U*x^3*(x+4));
assert &+[Coefficient(f,i)*(-2)^i*x^(6-i): i in [0..6]] eq -8*fbar;
assert 4*V*(2*x-1)-V*x^3*(x+4) eq -V*q^2;
assert Resultant(q,2*x-1) eq -3;
assert Discriminant(f) eq -2^22*3^6*U^2*V^2*(U-V)^6;
I2:=&+[(-1)^i*Coefficient(f,i)*Coefficient(f,6-i)/Binomial(6,i): i in [0..6]];
assert I2 eq -16*(U^2+25*U*V+V^2)/5;
assert I2^5/Discriminant(f) eq (U^2+25*U*V+V^2)^5/
    (9112500*U^2*V^2*(U-V)^6);
a:=2*(U-V)^2; b:=-(U-V)^3*V;
assert 16*b*(a^2-4*b) eq -64*(U-V)^6*U*V;
assert 1-a^2/(4*b) eq U/V;
assert [5+120/s:s in [-15,-20,-24,-30,-60]] eq [-3,-1,0,1,3];
print "PASS six-contact identities";
Z:=Integers();
E:=EllipticCurve([Rationals()|0,0,0,-36,0]);
T:=E![12,36,1];
assert (2*T)[1] eq 25/4;
for n in [1..10] do
    Q:=n*T; t:=Q[1]/6;
    assert t*(t-1)*(t+1) eq 6*(Q[2]/36)^2;
    aa:=Numerator(t); bb:=Denominator(t);
    for z in [aa,bb,aa-bb,aa+bb] do
        N:=Z!Abs(z);
        for p in [2,3] do
            while N mod p eq 0 do N div:= p; end while;
        end for;
        assert IsSquare(N);
    end for;
end for;
print "PASS ten points on the four-contact counterexample";
quit;
