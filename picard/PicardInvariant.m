// Work in a rational function field. The three checks are identities for all
// nonsingular specializations, including the algebraic coefficient conjugates.
K<rho> := QuadraticField(-3);
L<t> := FunctionField(K);
s := 5 + 120/t;
U := (s+rho)^6;
V := (s-rho)^6;
j := -57600*(t*(t+15)*(t+20)*(t+24)*(t+30)*(t+60))^2/(7*t^2+300*t+3600)^6;
assert (U-V)^2/(U*V) eq 27*j/4;
F<a,b> := FunctionField(Rationals(),2);
P<x> := PolynomialRing(F);
f := (x^2+2*x-2)*(4*a*(2*x-1)-b*x^3*(x+4));
q2 := &+[(-1)^i*Coefficient(f,i)*Coefficient(f,6-i)/Binomial(6,i) : i in [0..6]];
assert Discriminant(f) eq -2^22*3^6*a^2*b^2*(a-b)^6;
xx := (a-b)^2/(a*b);
assert q2^5/Discriminant(f) eq (xx+27)^5/(9112500*xx^3);
assert Evaluate((xx+27)^5/(9112500*xx^3), [U,V]) eq (j+4)^5/(200000*j^3);
print "VERIFIED sextic discriminant, transvectant and rational moduli map";
quit;
