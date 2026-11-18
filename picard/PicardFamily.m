versionMajor,versionMinor,versionPatch := GetVersion();
printf "MAGMA %o.%o-%o\n",versionMajor,versionMinor,versionPatch;
// Substitution in Laga--Shnidman, Remark 2.12, as a rational function identity.
F<u,v> := FunctionField(Rationals(),2);
R<x,y> := PolynomialRing(F,2);
U := u^6; V := v^6; A := U-V;
a := 2*A^2; w := -A*v^2; b := w^3; d := a^2-4*b;
q := x^2+2*x-2;
f := q*(4*U*(2*x-1)-V*x^3*(x+4));
assert d eq 4*A^3*U;
assert 16*b*d eq -64*(A*u*v)^6;
assert 1-a^2/(4*b) eq U/V;
assert -a*w*y^2-q*(b*x^4+4*b*x^3+2*d*x-d) eq A^3*(2*(v*y)^2-f);
print "VERIFIED Prym substitution and weighted parameters over Q(u,v)";
// Check the matching definition independently of the sextic's coefficients.
S<r1,r2,r3,r4,r5,r6> := PolynomialRing(Integers(),6);
roots := [r1,r2,r3,r4,r5,r6];
P<t> := PolynomialRing(S);
poly := &*[t-r : r in roots];
function matchings(L)
  if #L eq 0 then return S!1; end if;
  return &+[(L[1]-L[k])^2*$$([L[j]:j in [2..#L]|j ne k]):k in [2..#L]];
end function;
// 120 is divisible by every degree-six binomial coefficient.
assert -matchings(roots) eq &+[(-1)^j*(120 div Binomial(6,j))*Coefficient(poly,j)*Coefficient(poly,6-j):j in [0..6]];
assert Discriminant(poly) eq &*[(roots[j]-roots[k])^2 : j in [1..6],k in [1..6]|j lt k];
print "VERIFIED the fifteen matchings and ordinary discriminant in six indeterminates";
// Finite controls cover reduced nonintegral parameters, signs and denominator primes.
checks:=0; twists:=0; ordinary:=0; evenContacts:=0; oddContacts:=0;
for n in [-48..48] do
  for m in [1..24] do
    if GCD(n,m) ne 1 then continue; end if;
    branch:=n*m*(n-m)*(n+m)*(n-3*m)*(n+3*m);
    if branch eq 0 then continue; end if;
    e:=&*[Integers()| q[1] : q in Factorization(Abs(branch)) | q[1] gt 3 and q[2] mod 4 eq 2];
    assert IsSquarefree(e) and e gt 0;
    if e gt 1 then twists +:= 1; end if;
    for p in PrimesInInterval(5,97) do
      h:=Valuation(branch,p); vtw:=Valuation(e,p);
      assert vtw eq (h mod 4 eq 2 select 1 else 0);
      if IsEven(h) then
        assert IsEven(vtw+(h div 2));
        if h gt 0 then evenContacts+:=1; else ordinary+:=1; end if;
      else oddContacts+:=1; end if;
      checks+:=1;
    end for;
  end for;
end for;
assert Minimum([twists,ordinary,evenContacts,oddContacts]) gt 0;
printf "VERIFIED %o prime-parameter pairs, %o nontrivial twists, %o zero, %o positive even, %o odd valuations\n",checks,twists,ordinary,evenContacts,oddContacts;
quit;
