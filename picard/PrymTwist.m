// Laga--Shnidman, Remark 2.12 and Corollary 6.6, in a rational function field.
major, minor, patch := GetVersion();
printf "MAGMA %o.%o-%o\n", major, minor, patch;
K<i> := CyclotomicField(4);
F<u,v,d> := FunctionField(K,3);
R<x> := PolynomialRing(F);
U := u^6;
V := v^6;
delta := U-V;
l := v^2/d;
a := l^3 * 2*delta^2;
w := l^2 * (-delta*v^2);
b := w^3;
D := a^2-4*b;
sextic := (x^2+2*x-2)*(4*U*(2*x-1)-V*x^3*(x+4));
published := (x^2+2*x-2)*(b*x^4+4*b*x^3+2*D*x-D)/(-a*w);
assert published eq sextic/(2*d);
assert Degree(published) eq 6 and IsSeparable(published);
assert 1-a^2/(4*b) eq U/V;
assert (l^2*2*i*delta*u*v)^6 eq 16*b*D;
print "VERIFIED twisted Prym sextic, smoothness, marked value and common sixth root over Q(i)(u,v,d)";

// General coordinates of Ritzenthaler--Romagny, Theorem 1.1.
procedure CheckRitzenthalerRomagny()
    F<a,w> := FunctionField(Rationals(),2);
    R<x> := PolynomialRing(F);
    S<X,Y,Z> := PolynomialRing(F,3);
    M := Matrix(F,3,[0,-1,w, 0,0,-a, 1,w,w^2]);
    N := M^-1;
    assert Determinant(M) eq a;
    assert N eq Matrix(F,3,[w,2*w^2/a,1, -1,-w/a,0, 0,-1/a,0]);
    Bforms := [X^2,X*Z,Z^2];
    row := func<k | &+[M[k,j]*Bforms[j] : j in [1..3]]>;
    assert Y^4-row(2)*Y^2+row(1)*row(3) eq Y^4+a*Y^2*Z^2+w^3*Z^4-X^3*Z;
    column := func<j | N[1,j]+2*N[2,j]*x+N[3,j]*x^2>;
    RR := column(2)*(column(2)^2-column(1)*column(3));
    D := a^2-4*w^3;
    LS := (x^2+2*x-2)*(w^3*x^4+4*w^3*x^3+2*D*x-D)/(-a*w);
    assert Evaluate(RR,w*x) eq (w^2/a)^2*LS;
    print "VERIFIED ambient quartic, determinant, inverse matrix and RR/LS sextic substitution over Q(a,w)";
end procedure;
CheckRitzenthalerRomagny();
quit;
