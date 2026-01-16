
----------------------------------------------------------------------------------------
------ DECOMPOSITION LOCI OF TENSORS
------ A. Bernardi, A. Oneto, P. Santarsiero
------
------ In this file we collect all our computations and examples.
----------------------------------------------------------------------------------------

loadPackage "Resultants"

----------------------------------------------------------------------------------------
------ Parameters
C = QQ[l]
Csym = N -> QQ[l, a_1..a_(N_0), b_1..b_(N_1), c_1..c_(N_2)];

ringS = N -> C[x_1..x_(N_0)] ** C[y_1..y_(N_1)] ** C[z_1..z_(N_2)];
ringSsym = N -> (C' := Csym(N); return C'[x_1..x_(N_0)] ** C'[y_1..y_(N_1)] ** C'[z_1..z_(N_2)])

----------------------------------------------------------------------------------------
------ Auxiliary functions
----------------------------------------------------------------------------------------

-- flattenings on three factors
flatt1 = T -> contract(basis({0,1,1},S), transpose contract(basis({1,0,0},S),T));
flatt2 = T -> contract(basis({1,0,1},S), transpose contract(basis({0,1,0},S),T));
flatt3 = T -> contract(basis({1,1,0},S), transpose contract(basis({0,0,1},S),T));

-- linear systems of matrices on three factors
lin1 = T -> contract(basis({0,0,1},S), transpose contract(basis({0,1,0},S),T));
lin2 = T -> contract(basis({0,0,1},S), transpose contract(basis({1,0,0},S),T));
lin3 = T -> contract(basis({0,1,0},S), transpose contract(basis({1,0,0},S),T));

-- group action on three factors
phi = (A,B,C) -> map(S,S,transpose(A*transpose basis({1,0,0},S)) | transpose(B*transpose basis({0,1,0},S)) | transpose(C*transpose basis({0,0,1},S)))

----------------------------------------------------------------------------------------
------ Orbit n.9
----------------------------------------------------------------------------------------
S = ringS({2,2,4});

-- T9 is the generator of the orbit
T9 = x_1*(y_1*z_1 + y_2*z_3) + x_2*(y_1*z_2 + y_2*z_4);

-- the forbidden locus of an element in the orbit n.9 given by the dual multilinear form
-- 
-- Example: element of forbidden locus of T9
Q = x_2*y_2*(z_1+random(QQ)*z_2+random(QQ)*z_3)
radical minors(4,flatt3(T9-l*Q)) 

--
-- Example: element of forbidden locus of an element of T9
A = matrix{{0,1},{1,-1}}
B = matrix{{0,1},{1,-1}}
C = matrix{{0,0,0,1},{1,-1,0,0},{0,1,0,0},{0,0,1,0}}
T = (phi(A,B,C))(T9)

-- in this case, we need to compute the conjugate action on T
T' = (phi(transpose inverse A, transpose inverse B, transpose inverse C))(T)

-- consider a random rank-1 tensor and
-- a rank-1 tensor which is annihilated by contraction by T' but not T 
P = (sum for i from 1 to 2 list random(QQ)*x_i) * (sum for i from 1 to 2 list random(QQ)*y_i) *  (sum for i from 1 to 4 list random(QQ)*z_i)
Q = x_2*y_2*(z_1-z_2)

radical minors(4,flatt3(T-l*P)) -- it is in the decomposition locus
radical minors(4,flatt3(T-l*Q)) -- it is in the forbidden locus

----------------------------------------------------------------------------------------
------ Orbit n.13
----------------------------------------------------------------------------------------
N = {2,3,3};
S = ringSsym(N)

------
-- Example. T13 is the generator of the orbit
T13 = x_1*(y_1*z_1 + y_2*z_3) + x_2*(y_1*z_2 + y_3*z_3);

-- We follow the Procedure explained in Algorithm 1

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

-- Step 1.
-- Compute the maximal minors of flattenings of T - l*P
I = intersect(minors(2,flatt1(T13-l*P)), minors(3,flatt2(T13-l*P)), minors(3,flatt3(T13-l*P)))
K = ideal(I_0,I_1,I_2,I_3); primaryDecomposition K
contract(l,I_4)

-- Step 2.
-- We compute the hyperdeterminant of T - l*P
D = det lin1(T13-l*P)
supD = support(D);

R = Csym(N)[supD_0,supD_1]
D = sub(D,R)
factor D

-- Step 3.
-- We compute the determinant of T-l*P as pencil of 3x3 matrices
pencil = T13-sub(l,S)*P
detP = det lin1(pencil)
factor detP

-- It is never identically 0 and 
-- it is identically a pure cube only if the three factors are equal

-- Next, we look the intersection with the Segre of rank-one matrices
-- for the remaining cases
rank1 = primaryDecomposition radical minors(2,lin1(pencil))
netList rank1

----------------------------------------------------------------------------------------
------ Orbit n.15
----------------------------------------------------------------------------------------
N = {2,3,3};
S = ringSsym(N)

------
-- Example. T15 is the generator of the orbit
T15 = x_1*(y_1*z_1+y_2*z_2+y_3*z_3)+x_2*y_1*z_2

-- We follow the Procedure explained in Algorithm 1

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

-- Step 1.
-- Compute the maximal minors of flattenings of T - l*P
I = radical intersect(minors(2,flatt1(T15-l*P)), minors(3,flatt2(T15-l*P)), minors(3,flatt3(T15-l*P)))

K = ideal(for i to 4 list I_i); primaryDecomposition K
contract(l,I_5)

-- Step 2.
-- We compute the hyperdeterminant of T - l*P
D = det lin1(T15-l*P)
supD = support(D);

R = Csym(N)[supD_0,supD_1]
D = sub(D,R)
factorsD = factor discriminant(D)

-- We compute the ideal generated by the coefficients of the hyperdeterminant
-- since we want that it is identically zero as polynomial in l
cond = radical ideal (coefficients sub(discriminant(D), QQ[a_1,a_2, b_1..b_3, c_1..c_3][l]))_1
condSaturated = sub(cond,S) : sub(ideal(a_2,a_1),S)

-- Step 3.
-- We compute the determinant of T-l*P as pencil of 3x3 matrices
use S

pencil = T15-sub(l,S)*P
M = lin1(pencil)
newS = S/condSaturated
netList primaryDecomposition saturate(radical minors(2,sub(M,newS)),sub(ideal(x_1,x_2),newS))

-- under those conditions, we need to check if the intersection with the second secant variety 
-- is a unique point or they are two points
sub(D,R/(sub(condSaturated,R) + sub(ideal(a_2),R)))
sub(D,R/(sub(condSaturated,R) + sub(ideal(b_3,b_2),R)))
sub(D,R/(sub(condSaturated,R) + sub(ideal(c_3,c_1),R)))

----------------------------------------------------------------------------------------
------ Orbit n.16
----------------------------------------------------------------------------------------
N = {2,3,3};
S = ringSsym(N)

------
-- Example. T16 is the generator of the orbit
T16 = x_1*(y_1*z_1+y_2*z_2+y_3*z_3)+x_2*(y_1*z_2+y_2*z_3)

-- We follow the Procedure explained in Algorithm 1

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

-- Step 1.
-- Compute the maximal minors of flattenings of T - l*P
I = radical intersect(minors(2,flatt1(T16-l*P)), minors(3,flatt2(T16-l*P)), minors(3,flatt3(T16-l*P)))

K = ideal(for i to 4 list I_i); primaryDecomposition K
contract(l,I_5)

-- Step 2.
-- We compute the hyperdeterminant of T - l*P
D = det lin1(T16-l*P)
supD = support(D);

R = Csym(N)[supD_0,supD_1]
D = sub(D,R)
factorsD = factor discriminant(D)

-- We compute the ideal generated by the coefficients of the hyperdeterminant
-- since we want that it is identically zero as polynomial in l
cond = radical ideal (coefficients sub(discriminant(D), QQ[a_1,a_2, b_1..b_3, c_1..c_3][l]))_1
condSaturated = sub(cond,S) : sub(ideal(a_2,a_1),S)

-- Step 3.
-- We compute the determinant of T-l*P as pencil of 3x3 matrices
use S

pencil = T16-sub(l,S)*P
M = lin1(pencil)
newS = S/condSaturated
netList primaryDecomposition saturate(radical minors(2,sub(M,newS)),sub(ideal(x_1,x_2),newS))

-- we restrict the computation to the space we have computed in the previous step
sub(D,R/(sub(condSaturated,R)+sub(ideal(b_3,c_1),R)))

----------------------------------------------------------------------------------------
------ Orbit n.17
----------------------------------------------------------------------------------------
N = {2,3,3};
S = ringSsym(N)

------
-- Example. T17 is the generator of the orbit
T17 = x_1*(y_1*z_1+y_2*z_2)+x_2*(y_1*z_2+y_3*z_3)

-- We follow the Procedure explained in Algorithm 1

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

-- Step 1.
-- Compute the maximal minors of flattenings of T - l*P
I = radical intersect(minors(2,flatt1(T17-l*P)), minors(3,flatt2(T17-l*P)), minors(3,flatt3(T17-l*P)))

K = ideal(for i to 10 list I_i); primaryDecomposition K
contract(l,I_11)

-- Step 2.
-- We compute the hyperdeterminant of T - l*P
D = det lin1(T17-l*P)
supD = support(D);

R = Csym(N)[supD_0,supD_1]
D = sub(D,R)
factorsD = factor discriminant(D)

-- We compute the ideal generated by the coefficients of the hyperdeterminant
-- since we want that it is identically zero as polynomial in l
cond = radical ideal (coefficients sub(discriminant(D), QQ[a_1,a_2, b_1..b_3, c_1..c_3][l]))_1
condSaturated = sub(cond,S) : sub(ideal(a_2,a_1),S)

-- Step 3.
-- We compute the determinant of T-l*P as pencil of 3x3 matrices
use S

pencil = T17-sub(l,S)*P
M = lin1(pencil)
newS = S/condSaturated
primaryDecomposition saturate(radical minors(2,sub(M,newS)),sub(ideal(x_1,x_2),newS))

-- we restrict the computation to the space we have computed in the previous step
sub(D,R/(sub(condSaturated,R)+sub(ideal(b_2,c_1),R)))
sub(D,R/(sub(condSaturated,R)+sub(ideal(a_2,b_3,c_1,c_3),R)))
sub(D,R/(sub(condSaturated,R)+sub(ideal(a_2,b_2,b_3,c_3),R)))


----------------------------------------------------------------------------------------
------ Orbit n.19
----------------------------------------------------------------------------------------
N = {2,3,4};
S = ringSsym(N)

-- We follow the Procedure explained in Algorithm 6.2
T19 = x_1*(y_1*z_1+y_2*z_2+y_3*z_4)+x_2*(y_1*z_2+y_2*z_3)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

pencil = T19 - l*P

-- Step 1.
-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(T19-l*P))

-- Step 2.
-- We compute the maximal minors of the first flattening
I3 = radical minors(4,flatt3(T19-l*P))
I2 = radical minors(3,flatt2(T19-l*P))

---- We look for common roots
trim sub(I2,S/I3)

pencil = sub(T19-l*P, S/I3)
cond = minors(3,lin1(pencil))
ideal gens gb cond == cond
cond = ideal gens gb cond 

supD = support(cond)
R = Csym(N)[supD_0,supD_1]
D = sub(cond_0,R)
factorsD = factor discriminant(D)

R' = (ring(pencil))/sub(radical ideal discriminant(D),ring(pencil))
pencil' = sub(pencil,R')

(radical minors(2,lin1(pencil'))) : sub(ideal(x_1,x_2), R')
radical minors(3,lin1(sub(pencil',R'/sub(ideal(b_3,c_1,c_4),R'))))

----------------------------------------------------------------------------------------
------ Orbit n.20
----------------------------------------------------------------------------------------
N = {2,3,4};
S = ringSsym(N)

-- We follow the Procedure explained in Algorithm 6.2
T20 = x_1*(y_1*z_1+y_2*z_3+y_3*z_4)+x_2*y_1*z_2

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

pencil = T20 - l*P

-- Step 1.
-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(T20-l*P))

-- Step 2.
-- We compute the maximal minors of the first flattening
I3 = radical minors(4,flatt3(T20-l*P))
I2 = radical minors(3,flatt2(T20-l*P))

---- We look for common roots
trim sub(I2,S/I3)

pencil = sub(T20-l*P, S/I3)
cond = minors(3,lin1(pencil))
ideal gens gb cond == cond
cond = ideal gens gb cond 

supD = support(cond)
R = Csym(N)[supD_0,supD_1]
D = sub(cond_0,R)
factorsD = factor discriminant(D)

R' = (ring(pencil))/sub(radical ideal discriminant(D),ring(pencil))
pencil' = sub(pencil,R')

(radical minors(2,lin1(pencil'))) : sub(ideal(x_1,x_2), R')


----------------------------------------------------------------------------------------
------ Orbit n.21
----------------------------------------------------------------------------------------
N = {2,3,4};
S = ringSsym(N);

T21 = x_1*(y_1*z_1+y_2*z_3+y_3*z_4) + x_2*(y_1*z_2+y_2*z_4);

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

pencil = T21 - l*P

-- we check conciseness
I1 = radical minors(2,flatt1(T21-l*P))
I2 = radical minors(3,flatt2(T21-l*P))
I3 = radical minors(4,flatt3(T21-l*P))

irr = intersect(ideal(x_1,x_2),sub(ideal(l),S));

-- we check the intersection of the pencil with the second secant variety
PP = primaryDecomposition saturate(minors(3,lin1(T21-l*P)),irr)
netList PP

alpha = contract(l,PP_2_1)

-- we have three cases:
--------------------------------
-- case 1: A = 0
pencil1 = sub(pencil, S/ideal(alpha))
PP1 = primaryDecomposition saturate(minors(3,lin1(pencil1)),sub(irr,ring(pencil1)))
netList PP1

---- outside the intersections with b_3 = 0 and a_2 = 0:
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)),sub(ideal(b_3*a_2),ring(pencil1))})
    )
netList PP1'
---- we notice that it depends on the values on the third factor
---- if c_1 != 0, then we have no intersection
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)),sub(ideal(b_3*a_2*c_1),ring(pencil1))})
    )
netList PP1'
---- if c_1 = 0 and c_2 != 0, then we have null or smooth intersection
pencil1 = sub(pencil, S/ideal(sub(c_1,S),sub(alpha,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)),sub(ideal(b_3*a_2*c_2),ring(pencil1))})
    )
netList PP1'
---- if c_1 = c_2 = 0, then for the general choice of lambda we have smooth intersection
pencil1 = sub(pencil, S/ideal(sub(c_1,S),sub(c_2,S),sub(alpha,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)),sub(ideal(b_3*a_2),ring(pencil1))})
    )

cc = first entries transpose (coefficients(PP1'_0_0))_1
cc_1^2-4*cc_0*cc_2


--------------------------------
-- case 2: b3 = 0
pencil1 = sub(pencil, b_3 => 0)
PP1 = primaryDecomposition saturate(minors(3,lin1(pencil1)),irr)
netList PP1

alpha' = contract(l,PP1_1_1)

--------------
-- if alpha' != 0, c_1 != 0: then exists l such that we are supported at two points 
--------------
-- if alpha' != 0, c_1 = 0: then the intersection is a smooth simple point
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(c_1,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(alpha'),ring(pencil1))})
    )
netList PP1'

--------------
-- if alpha' = 0, c_1 != 0: then we have a 2-jet only if b2*a2 = 0
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(c_1),ring(pencil1))})
    )
netList PP1'

PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(c_1),ring(pencil1)), sub(ideal(b_2*a_2),ring(pencil1))})
    )
netList PP1'

------ if also b2 = 0, then we have a 2-jet if and only if b1 = 0 or a1c1+a2c2 = 0
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(b_2,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(c_1),ring(pencil1))})
    )
netList PP1'

------ if also a2 = 0, then we have a 2-jet if and only if b1c1+b2c3 = 0
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(a_2,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(c_1),ring(pencil1))})
    )
netList PP1'

--------------
-- if alpha' = 0, c_1 = 0: then we have a 2-jet only if b2*a2*c3 = 0
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(c_1,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1))})
    )
netList PP1'

PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1)), sub(ideal(b_2*a_2*c_3),ring(pencil1))})
    )
netList PP1'

----- if also b2 = 0: if a2b1c2 != 0 then there is a non-concise tensor, otherwise intersection is 2-jet
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(c_1,S),sub(b_2,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1))})
    )
netList PP1'

----- if also a2 = 0: if a2b2c3 != 0 then there is a non-concise tensor, otherwise intersection is 2-jet
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(c_1,S),sub(a_2,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1))})
    )
netList PP1'

----- if also c3 = 0: if b2 = 0 and a2b1c2 != 0 there is non-concise tensor, otherwise if b2 != 0, then we get a 2-jet
pencil1 = sub(pencil, S/ideal(sub(b_3,S),sub(alpha',S),sub(c_1,S),sub(c_3,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr,ring(pencil1))})
    )
netList PP1'



--------------------------------
-- case 2: a2 = 0 
-- in this case, we can add a1 in the irrelevant ideal, since (a1,a2) \neq 0
-- and also b3 since already considered
irr' = intersect(irr, sub(ideal(a_1),S), sub(ideal(b_3),S))

pencil1 = sub(pencil, a_2 => 0)
PP1 = primaryDecomposition saturate(minors(3,lin1(pencil1)),irr')
netList PP1

alpha'' = contract(l,PP1_1_1)

------------
-- if alpha'' != 0, c_1 != 0: then exists l such that we are supported at two points 
------------
-- if alpha'' != 0, c_1 = 0: then the it defines a simple point
pencil1 = sub(pencil, S/ideal(sub(a_2,S),sub(c_1,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr',ring(pencil1)), sub(ideal(alpha''),ring(pencil1))})
    )
netList PP1'

------------
-- if alpha'' = 0, c_1 != 0
pencil1 = sub(pencil, S/ideal(sub(a_2,S),sub(alpha'',S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr',ring(pencil1)), sub(ideal(c_1),ring(pencil1))})
    )
netList PP1'

------------
-- if alpha'' = 0, c_1 = 0: then we have a 2-jet only if c3 = 0
pencil1 = sub(pencil, S/ideal(sub(a_2,S),sub(alpha'',S),sub(c_1,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr',ring(pencil1))})
    )
netList PP1'

----- if also c3 = 0: if c2 = 0 and a1b3c4 != 0 then there is a non-concise tensor, otherwise intersection is 2-jet
pencil1 = sub(pencil, S/ideal(sub(a_2,S),sub(alpha'',S),sub(c_1,S),sub(c_3,S)))
PP1' = primaryDecomposition saturate(minors(3,lin1(pencil1)),
    intersect({sub(irr',ring(pencil1))})
    )
netList PP1'

-------------------------------------------------
-- numerical experiment
S = ringS({2,3,4})
T21 = x_1*(y_1*z_1+y_2*z_3+y_3*z_4) + x_2*(y_1*z_2+y_2*z_4);
P = x_1 * (sum for i from 1 to N_1 list (random(QQ)*y_i)) * (random(QQ)*z_2+random(QQ)*z_4)

l = sub(l,S)
pencil = T21 - l*P

-- we check conciseness
I1 = radical minors(2,flatt1(T21-l*P))
I2 = radical minors(3,flatt2(T21-l*P))
I3 = radical minors(4,flatt3(T21-l*P))

-- P is in the forbidden locus
saturate(minors(3,lin1(pencil)), intersect(ideal(x_1,x_2),ideal(l)))


----------------------------------------------------------------------------------------
------ Orbit n.22
----------------------------------------------------------------------------------------
N = {2,3,4};
S = ringSsym(N)

-- We follow the Procedure explained in Algorithm 6.2
T22 = x_1*(y_1*z_1+y_2*z_3)+x_2*(y_1*z_2+y_3*z_4)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));

pencil = T22 - l*P

-- Step 1.
-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(T22-l*P))

-- Step 2.
-- We compute the maximal minors of the first flattening
I3 = radical minors(4,flatt3(T22-l*P))
I2 = radical minors(3,flatt2(T22-l*P))

---- We look for common roots
trim sub(I2,S/I3)

pencil = sub(T22-l*P, S/I3)
cond = radical minors(3,lin1(pencil))

supD = support(cond)
R = Csym(N)[supD_0,supD_1]
D = sub(cond_0,R)
factorsD = factor discriminant(D)

R' = ring(pencil)/sub(ideal(c_1*c_2),ring(pencil))
pencil' = sub(pencil,R')
min3condition = (radical minors(3,lin1(pencil'))) : sub(ideal(x_1,x_2), R')


----------------------------------------------------------------------------------------
------ Orbit n.23
----------------------------------------------------------------------------------------
N = {2,3,4};
S = ringSsym(N)

-- We follow the Procedure explained in Algorithm 6.2
T23 = x_1*(y_1*z_1+y_2*z_2+y_3*z_3)+x_2*(y_1*z_2+y_2*z_3+y_3*z_4)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));
pencil = T23 - l*P

-- Step 1.
-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(T23-l*P))

-- Step 2.
-- We compute the maximal minors of the first flattening
I3 = radical minors(4,flatt3(T23-l*P))
I2 = radical minors(3,flatt2(T23-l*P))

---- We look for common roots
trim sub(I2,S/I3)

pencil = sub(T23-l*P, S/I3)
cond = radical minors(3,lin1(pencil))

supD = support(cond)
R = Csym(N)[supD_0,supD_1]
D = sub(cond_0,R)
factorsD = factor discriminant(D)

R' = ring(pencil)/sub(cond,ring(pencil))
pencil' = sub(pencil,R')

min3condition = (radical minors(3,lin1(pencil'))) : sub(ideal(x_1,x_2), R')
min2condition = (radical minors(2,lin1(pencil'))) : sub(ideal(x_1,x_2), R')

----------------------------------------------------------------------------------------
------ Orbit n.24
----------------------------------------------------------------------------------------
N = {2,3,5};
S = ringSsym(N)

-- 
T24 = x_1*(y_1*z_1+y_2*z_3+y_3*z_5)+x_2*(y_1*z_2+y_2*z_4)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));
pencil = T24 - l*P


-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(pencil))
I2 = radical minors(3,flatt2(pencil))
I3 = radical minors(5,flatt3(pencil))


----- Assume we are in the case the third flattening is vanishing
-- does not meet the 2nd secant variety at a 2-jet
pencil1 = sub(pencil, S/I3)
primaryDecomposition saturate(minors(3,lin1(pencil1)), sub(ideal(x_1,x_2),ring(pencil1)))



T24 = x_1*(y_1*z_1+y_2*z_2+y_3*z_5)+x_2*(y_1*z_2+y_2*z_4) 
-- generic rank-1 tensor 
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i)); 
pencil = T24 - l*P 
-- Step 1. -- We compute the maximal minors of the first flattening 
I1 = radical minors(2,flatt1(T24-l*P)) 
-- Step 2. -- We compute the maximal minors of the first flattening 
I3 = radical minors(5,flatt3(T24-l*P)) 
I2 = radical minors(3,flatt2(T24-l*P))


----------------------------------------------------------------------------------------
------ Orbit n.25
----------------------------------------------------------------------------------------
N = {2,3,5};
S = ringSsym(N)

-- 
T25 = x_1*(y_1*z_1+y_2*z_2+y_3*z_4)+x_2*(y_1*z_2+y_2*z_3+y_3*z_5)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));
pencil = T25 - l*P



-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(pencil))
I2 = radical minors(3,flatt2(pencil))
I3 = radical minors(5,flatt3(pencil))


----- Assume we are in the case the third flattening is vanishing
-- if the linear forms are not identically zero, then the intersection is not a 2-jet
pencil1 = sub(pencil, S/(I3))
primaryDecomposition saturate(minors(3,lin1(pencil1)), sub(ideal(x_1,x_2),ring(pencil1)))

-- c_4 = c_5 = 0: then the discriminant is in the forbidden locus
pencil1 = sub(pencil, S/(I3+sub(ideal(c_4,c_5),S)))
primaryDecomposition saturate(minors(3,lin1(pencil1)), sub(ideal(x_1,x_2),ring(pencil1)))

-- c_4 = c_5 != 0 and the other linear form is identically 0: then the discriminant is in the forbidden locus
pencil1 = sub(pencil, S/(I3+sub(ideal(c_3*c_4,-c_2*c_4+c_1*c_5),S)))
primaryDecomposition saturate(minors(3,lin1(pencil1)), 
    intersect(sub(ideal(x_1,x_2),ring(pencil1)),sub(ideal(c_4,c_5),ring(pencil1)))
    


-------------------------------------------------
-- numerical experiment
S = ringS({2,3,5})
T25 = x_1*(y_1*z_1+y_2*z_2+y_3*z_4)+x_2*(y_1*z_2+y_2*z_3+y_3*z_5)
P = (x_1+x_2) * (random(QQ)*(y_1+y_2)+random(QQ)*y_3) * (z_1 + 2*z_2 + z_3)

l = sub(l,S)
pencil = T25 - l*P

-- we check conciseness
I1 = radical minors(2,flatt1(T25-l*P))
I2 = radical minors(3,flatt2(T25-l*P))
I3 = radical minors(5,flatt3(T25-l*P))

pencil = T25 - P/32

-- P is in the forbidden locus: 
saturate(minors(3,lin1(pencil)), ideal(x_1,x_2))


----------------------------------------------------------------------------------------
------ Orbit n.26
----------------------------------------------------------------------------------------
N = {2,3,6};
S = ringSsym(N)

-- We follow the Procedure explained in Algorithm 6.2
T26 = x_1*(y_1*z_1+y_2*z_3+y_3*z_5)+x_2*(y_1*z_2+y_2*z_4+y_3*z_6)

-- generic rank-1 tensor
P = (sum for i from 1 to N_0 list (a_i*x_i)) * (sum for i from 1 to N_1 list (b_i*y_i)) * (sum for i from 1 to N_2 list (c_i*z_i));
pencil = T26 - l*P

-- We compute the maximal minors of the first flattening
I1 = radical minors(2,flatt1(T26-l*P))
I2 = radical minors(3,flatt2(T26-l*P))
I3 = radical minors(6,flatt3(T26-l*P))

