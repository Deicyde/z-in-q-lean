// The common splitting extension of the three alternating cocycles on
// Gal(Q(i,sqrt(2),sqrt(3))/Q). All computations are exact.
major,minor,patch := GetVersion();
printf "MAGMA %o.%o-%o\n", major,minor,patch;
Q := Rationals();
P<x> := PolynomialRing(Q);
polynomials := [x^4-2, x^4-3, x^4-2*x^2+3];
discriminants := [ Integers()!Discriminant(f) : f in polynomials ];
assert discriminants eq [-2048,-6912,3072];
printf "Rational polynomial discriminants %o\n", discriminants;

L<z> := CyclotomicField(24);
i := z^6;
u := z^3+z^(-3);
v := z^2+z^(-2);
assert [i^2,u^2,v^2] eq [-1,2,3];
w := 1+i*u;
assert w*(1-i*u) eq 3;
radicands := [u,v,w];
for S in Subsets({1,2,3}) do
    if #S gt 0 then
        assert not IsSquare(&*[ radicands[j] : j in S ]);
    end if;
end for;
printf "Seven nontrivial squareclasses checked over Q(zeta_24)\n";

P0<t0> := PolynomialRing(L);
A<a> := ext<L | t0^2-u>;
P1<t1> := PolynomialRing(A);
B<b> := ext<A | t1^2-(A!v)>;
P2<t2> := PolynomialRing(B);
M<c> := ext<B | t2^2-(B!w)>;
assert AbsoluteDegree(M) eq 64;
Aroot := M!a;
Broot := M!b;
I := M!i;
V := M!v;
roots := [
    [Aroot,-Aroot,I*Aroot,-I*Aroot],
    [Broot,-Broot,I*Broot,-I*Broot],
    [c,-c,V/c,-V/c]
];
for j := 1 to 3 do
    assert #(Seqset(roots[j])) eq 4;
    assert forall{ r : r in roots[j] | Evaluate(polynomials[j],r) eq 0 };
end for;
printf "Absolute degree 64; all three quartics split in the radical tower\n";

function Lift(signs)
    // signs refer in order to i, sqrt(2), sqrt(3).
    for n in [1,5,7,11,13,17,19,23] do
        Z := z^n;
        if [Z^6,Z^3+Z^(-3),Z^2+Z^(-2)] eq
            [signs[1]*i,signs[2]*u,signs[3]*v] then
            f0 := hom<L -> M | M!Z>;
            f1 := hom<A -> M | f0, signs[2] eq 1 select Aroot else I*Aroot>;
            f2 := hom<B -> M | f1, signs[3] eq 1 select Broot else I*Broot>;
            return hom<M -> M | f2, signs[1]*signs[2] eq 1 select c else V/c>;
        end if;
    end for;
    error "No automorphism with the specified independent signs";
end function;

gen := [Lift([-1,1,1]), Lift([1,-1,1]), Lift([1,1,-1])];
bits := [];
for ij in [[1,2],[1,3],[2,3]] do
    f := gen[ij[1]];
    g := gen[ij[2]];
    assert f(g(M!z)) eq g(f(M!z));
    row := [];
    for r in [Aroot,Broot,c] do
        delta := f(g(r))/g(f(r));
        assert delta eq 1 or delta eq -1;
        Append(~row,delta eq -1 select 1 else 0);
    end for;
    Append(~bits,row);
end for;
assert bits eq [[1,0,0],[0,1,1],[0,0,1]];
assert Rank(Matrix(GF(2),3,3,&cat bits)) eq 3;
printf "Commutator exponents on (fourthroot2,fourthroot3,sqrt(1+sqrt(-2))) %o\n", bits;
printf "VERIFIED common splitting field degree 64, commutator rank 3 and rational ramification support contained in {2,3}\n";
// The presentation (-3,2) of the quaternion algebra of discriminant six.
D<I,J,K> := QuaternionAlgebra<Q | -3, 2>;
rad := [Q!x : x in [-3, 2, 6, 5]];
generators := [I,J,I*J,I+2*J];
assert [x^2 : x in generators] eq [D!d : d in rad];
for mask := 1 to 15 do
    product := &*[Q| rad[t] : t in [1..4] | IsOdd(mask div 2^(t-1))];
    assert not IsSquare(product);
end for;
E := Q;
for d in rad do
    T<X> := PolynomialRing(E);
    f := X^2-E!d;
    assert IsIrreducible(f);
    E := NumberField(f);
end for;
assert AbsoluteDegree(E) eq 16;
print "VERIFIED four quaternion generators, fifteen nonsquare rational products and compositum degree 16";
quit;
