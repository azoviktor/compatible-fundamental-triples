-*
Organization:

1. Proof of Theorem 1 (conditional on multidegree lower bounds)
2. Proof of Theorem 2
3. Proofs of Multidegree Lower Bounds for the Compatibility Variety
    3i. mdeg(7,7,4) >= 3
   3ii. mdeg(7,6,5) >= 26
  3iii. mdeg(6,6,6) >= 81
*-


-- 1. Proof of Theorem 1 (conditional on multidegree lower bounds)
restart
FF = QQ
Rs = apply(3, i -> FF[f_(i,0,0)..f_(i,2,2)])
S = fold(Rs, tensor)
Fs = apply(Rs, R -> sub(genericMatrix(R,3,3), S))
F12 = Fs#0
F13 = Fs#1
F23 = Fs#2
F21 = transpose F12
F31 = transpose F13
F32 = transpose F23
adj = A -> (1/2)*((trace A)^2 - trace(A*A))*id_(S^3) - (trace A)*A + A*A
tripleProducts = {
    F12 * transpose adj(F23) * transpose F13,
    (transpose F13) * transpose adj(F12) * F23,
    (transpose F12) * transpose adj(F13) * transpose F23
    };
cubics = det \ Fs;
quartics = flatten apply(tripleProducts, A -> flatten entries(A - transpose A));
quintics = flatten \\ flatten \ entries \ {
    adj(F13) * F12 * adj(F32),
    adj(F12) * F13 * adj(F23),
    adj(F21) * F23 * adj(F13)
    };
I345 = ideal(cubics | quartics | quintics);

-- saturate by epipoles to get vanishing ideal
e12 = transpose (adj(F12))^{0}
e13 = transpose (adj F13)^{0}
e23 = (transpose adj F23)_{0}
e21 = transpose (transpose adj(F12))^{0}
IF = (I345:minors(2, e23 | e21)):minors(2, e12 | e13);

-- check dimension and multidegrees of IF (implying multidegree upper bounds for compatibility variety)
assert(18 + 3 == dim IF)
T = tally flatten entries last coefficients multidegree IF
assert(sort keys T == {9, 36, 81})
assert(sort values T == {1, 3, 6})

-- check that I is Cohen-Macaulay
assert(dim removeLowestDimension(IF) < 0)

-- check description of Betti table
degreeTally = tally apply(flatten entries mingens IF, p -> sum degree p)
assert(sort keys degreeTally == {3,4,5,7})
assert(sort values degreeTally == {3,9,18,108})

-- finally, check that 108 septic minors are minimal generators
Z = map(S^3, S^3, 0)
F = (Z | F12 | F13) || (transpose F12 | Z | F23) || (transpose F13 | transpose F23 | Z)
minorsDeletionList = (i,j) -> (
    assert(1<=i and i<j and j<=3);
    rc := flatten (
        for r in subsets(9,2) list 
        for c in subsets(9,2) list 
        if isSubset(set{first r, first c}, set(3*(i-1)..3*i-1)) and 
            isSubset(set{last r, last c}, set(3*(j-1)..3*j-1)) then (r,c) else continue
        );
    select(rc, rc->((r,c):=rc; 
        r==c or 
        (first r < first c and last r < last c) or
        (first r == first c and last r < last c) or 
        (first r < first c and last r == last c)
        ))
)
septics = apply(
    minorsDeletionList(1,2)|minorsDeletionList(1,3)|minorsDeletionList(2,3),
    rc->((r,c):=rc; det submatrix'(F,r,c))
    );
assert(#septics == 108)
assert(
    syz(sub(matrix{septics}, S/I345), DegreeLimit => {3,3,1}) | 
    syz(sub(matrix{septics}, S/I345), DegreeLimit => {3,1,3}) | 
    syz(sub(matrix{septics}, S/I345), DegreeLimit => {1,3,3}) == 0
)

-*
Proof of Theorem 2
*-
-- construct Demazure cubics and Martyushev sextic
demazureCubics = apply(Fs, F -> 2 * F * transpose F * F - trace(F * transpose F) * F);
martyushev = (trace(F^2))^3 - 12 * trace(F^2) * trace(F^4) + 32 * trace(F^6);
M6F = sum select(terms martyushev, t -> degree t == {2,2,2});
IlocalE = ideal(demazureCubics | quartics | {M6F});

-- fabricate a sufficiently generic compatible triple of essential matrices
P1 = id_(QQ^3) | matrix{{0},{0},{0}}
P2 = id_(QQ^3) | matrix{{1},{2},{3}}
P3 = id_(QQ^3) | matrix{{4},{5},{6}}
getF = (Pi, Pj) -> (
    Pij := Pi || Pj;
    matrix apply(3, i -> apply(3, j -> (-1)^(i+j) * det submatrix'(Pij, {j,3+i}, {})))
)
E0 = matrix{flatten entries getF(P1,P2) | flatten entries getF(P1,P3) | flatten entries getF(P2,P3)}

-- check that equations vanish at E0 and have the right Jacobian rank
assert(0 == sub(gens IlocalE, E0))
assert(11 + 3 == rank ker sub(transpose jacobian IlocalE, E0))

-- 3. Proofs of Multidegree Lower Bounds for Compatibility Variety

-*
3.i Proof of mdeg(7, 7, 4) = 9 = 3^2

Note: 3 is the number of camera-pairs (up to PGL4) consistent with a general fundamental matrix

Given general F_12 and F_13, and 4 general linear constraints on F_23, 
we must show that F_23 is uniquely determined.

Let L be a general (7,7,4)-slice.

Suppose the images of two general camera-triples,
(P1, P2, P3) and (Q1, Q2, Q3), both realize a point in L.
(By genericity, WMA after coordinate change that the cameras Pi have the forms given below.)

Then 
P1 ~ Q1 H1, P2 ~ Q2 H1            for H1 in PGL4, 
P1 ~ Q1 H2,            P3 ~ Q3 H2 for H2 in PGL4.

So H = H2^(-1) H1 stablizes P1.

By genericity, we may work on the affine chart h_(3,3)=1 in P^15.

As shown below, the condition 

F(P1, P2) = F(Q1, Q2) = F(P1 H2^(-1), P2 H1^(-1))  = F(P1 H, P2)

is then automatically satisfied. Additionally, the condition

F(P1, P3) = F(Q1, Q3) = F(P1 H1^(-1), P3 H2^(-1)) = F(P1, P3 H)

implies h_(4,4) = 1. Finally, all of the above conditions along with

F(P2, P3) = F(Q2, Q3) = F(P2 H1^(-1), P3 H2^(-1)) = F(P2, P3 H)

together imply H is the 4 x 4 identity matrix.

In conclusion, since H1 = H2, we have

(P1, P2, P3) ~ (Q1 H1, Q2 H1, Q3 H1),

and thus both camera triples map to the same triple of fundamental matrices in L.
*-
restart
P1 = matrix apply(3, i -> apply(4, j -> if member((i,j), {(0,0),(1,1),(2,2)}) then 1 else 0))
P2 = matrix apply(3, i -> apply(4, j	-> if member((i,j), {(0,1),(1,2),(2,3)}) then 1 else 0))
P3 = matrix apply(3, i -> apply(4, j -> if member((i,j), {(0,0),(1,2),(2,3)}) then 1 else 0))
getF = (Pi, Pj) -> (
    Pij := Pi || Pj;
    matrix apply(3, i -> apply(3, j -> (-1)^(i+j) * det submatrix'(Pij, {j,3+i}, {})))
)
R = QQ[h_(1,1)..h_(4,4)]
H = genericMatrix(R, 4, 4)
I = minors(2, matrix{flatten entries P1, flatten entries(P1 * H)}) + ideal(h_(3,3)-1)
dim I, degree I
getF(P1*H, P2) % I, getF(P1, P2)
getF(P1, P3*H) % I, getF(P1, P3)
I = I + ideal(getF(P1, P3*H) % I - getF(P1, P3))
dim I, degree I
getF(P2, P3*H) % I, getF(P2, P3)
I = I + ideal((getF(P2, P3*H) % I)- getF(P2, P3))
dim I, degree I
H%I

-*
3.ii Proof of mdeg(7, 6, 5) >= 36 = 3 * 12

We may assume F12 is given. Need to show there are 12 compatible pairs (F13, F23)
with F13 on a general plane in P^8 and F23 on a general 3-plane in P^8.

To begin, we fix cameras P1 and P2 with F(P1, P2) ~ F12, and count the number of cameras P3
which satisfy the required constraints.

Random choices give a specific instance where there are 12 valid cameras P3, which in turn
determine 12 distinct values for (F13, F23). This is shown by computing Groebner 
bases of zero-dimensional ideals.
*-
restart
FF = QQ
R = FF[a_1..a_3,b_1..b_3,c_1..c_3,d_1..d_3]
setRandomSeed 0
P1 = random(FF^3, FF^4)
P2 = random(FF^3, FF^4)
P3 = genericMatrix(R, 3, 4)
getF = (Pi, Pj) -> (
    Pij := Pi || Pj;
    matrix apply(3, i -> apply(3, j -> (-1)^(i+j) * det submatrix'(Pij, {j,3+i}, {})))
)
F12 = getF(P1, P2)
F13 = getF(P1, P3)
F23 = getF(P2, P3)
-- general plane
I = ideal for i from 1 to 6 list (matrix{flatten entries F13} * random(FF^9, FF^1));
-- general 3-plane
I = I + ideal for i from 1 to 5 list (matrix{flatten entries F23} * random(FF^9, FF^1));
-- normalize an entry of P3
I = I + ideal(P3_(2,2)-1);
-- remove excess solutions w/ rk(F13) < 2
-- ! this next line takes ~ 5 min !
elapsedTime I = I : minors(2, F13);
G = groebnerBasis(I, Strategy => "F4");
inI = ideal leadTerm G;
dim inI, degree inI -- (0, 12)
RmodI = R/I;
phi = map(RmodI, QQ[F_(1,1,1)..F_(2,3,3)], flatten entries F13 | flatten entries F23);
-- next line takes ~ 1min
elapsedTime I = ker phi;
dim I, degree I
-- check ideal is radical
-- ! this lines takes ~ 5 min !
elapsedTime degree radical I
-- finally: to guarantee all 81 points lie in the image,
--  check sufficient rank and epipole conditions
--  (all GBs below should quickly give {1})
F13 = matrix apply({1,2,3}, i -> apply({1,2,3}, j -> F_(1,i,j)))
F23 = matrix apply({1,2,3}, i -> apply({1,2,3}, j -> F_(2,i,j)))
gens gb(I + minors(2, F12))
gens gb(I + minors(2, F13))
gens gb(I + minors(2, F23))
gens gb(I + minors(3, F13|F23))
gens gb(I + minors(3, F12|transpose F23))
gens gb(I + minors(3, transpose F12|transpose F13))
-*
Thus mdeg >= 36. Reverse inequality follows from part 1.
*-

-*
3.iii Proof of mdeg(6, 6, 6) >= 81

Each Fij is constrained to lie on a general plane in P^8.

Random choices give a specific instance where the intersection of these planes with
the compatibility variety has global dimension 0 and at least 81 isolated, nonsingular points.
This is shown by computing Groebner bases of zero-dimensional ideals.
*-
restart
FF = QQ
R = FF[a..f]
setRandomSeed 2026
F12 = a * random(FF^3,FF^3,Height=>3) + b * random(FF^3,FF^3,Height=>3) + random(FF^3,FF^3,Height=>3)
F13 = c * random(FF^3,FF^3,Height=>3) + d * random(FF^3,FF^3,Height=>3) + random(FF^3,FF^3,Height=>3)
F23 = e * random(FF^3,FF^3,Height=>3) + f * random(FF^3,FF^3,Height=>3) + random(FF^3,FF^3,Height=>3)
adj = A -> (1/2)*((trace A)^2 - trace(A*A))*id_(FF^3) - (trace A)*A + A*A
tripleProducts = {
    F12 * transpose adj(F23) * transpose F13,
    (transpose F13) * transpose adj(F12) * F23,
    (transpose F12) * transpose adj(F13) * transpose F23
    };
I = ideal(det F12, det F13, det F23) + ideal apply(tripleProducts, M -> M - transpose M);
quintics = flatten \\ flatten \ entries \ {
    adj(F13) * F12 * adj(transpose F23),
    adj(F12) * F13 * adj(F23),
    adj(transpose F12) * F23 * adj(F13)
    };
I = I + ideal quintics;
-- ! the next line takes ~ 3 min!
elapsedTime G = groebnerBasis(I, Strategy => "F4");

-- ! Anton: skipped this block --- it doesn't terminate for me (in >1 hour) !
RmodI = R/I;
phi = map(RmodI, QQ[F_(1,1,1)..F_(3,3,3)], flatten entries F12 | flatten entries F13 | flatten entries F23)
elapsedTime K = ker phi;
dim K, degree K
degree radical K

needsPackage "FGLM"
-- ! the next line takes ~ 30 min!
elapsedTime FG = fglm(I, QQ[gens R, MonomialOrder => Lex]);
-- next line implies I is radical
p = first flatten entries gens FG;
degree radical ideal p
-- finally: to guarantee all 81 points lie in the image,
--  check sufficient rank and epipole conditions
--  (all ideals below should equal the whole ring)
assert all({
	I + minors(2, F12),
	I + minors(2, F13),
	I + minors(2, F23),
	I + minors(3, F13|F23),
	I + minors(3, F12|transpose F23),
	I + minors(3, transpose F12|transpose F13)
	}, J -> J == R)
-*
Thus mdeg >= 81. Reverse inequality follows from part 1.
*-
