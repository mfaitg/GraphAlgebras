#Execution of this file thanks to the Read command in the console prints on screen the exchange relations for the algebras L01, L10 and L02.

Print("Here are the exchange relations for the algebras L01, L10 and L02:"\n");

####################################
## Definition of the ground field ##  (see discussion in the documentation)
####################################

q := Indeterminate(Rationals, "q");
hq := Indeterminate(Rationals, "hq");
groundField := FunctionField(Rationals, [q, hq]);
0q := Zero(groundField);  #Zero element in the ground field
1q := One(groundField); #Unit element in the ground field


##################################
## R-matrix and related tensors ##
##################################

## (Normalized) R-matrix and its flip ##
nR := [ [q, 0q, 0q, 0q], [0q, 1q, hq, 0q], [0q, 0q, 1q, 0q],
          [0q, 0q, 0q, q] ];
nRp := [ [q, 0q, 0q, 0q], [0q, 1q, 0q, 0q], [0q, hq, 1q, 0q], 
           [0q, 0q, 0q, q] ];


## Components of the skew-inverse of nR ##
nx1 := KroneckerProduct( [ [1q, 0q], [0q, 0q] ], IdentityMat(2,groundField) );
x2 := KroneckerProduct( IdentityMat(2,groundField), [ [q^(-1), 0q], [0q, 1q] ] );
ny1 :=  KroneckerProduct( [ [0q, 1q], [0q, 0q] ], IdentityMat(2,groundField) );
y2 := KroneckerProduct( IdentityMat(2,groundField), [ [0q, 0q], [-q^(-2)*hq, 0q] ] );
nz1 := KroneckerProduct( [ [0q, 0q], [0q, 1q] ], IdentityMat(2,groundField) ); 
z2 := KroneckerProduct( IdentityMat(2,groundField), [ [1q, 0q], [0q, q^(-1)] ] );


## Components of the skew-inverse of nRp ##
nx2 := KroneckerProduct( IdentityMat(2,groundField), [ [1q, 0q], [0q, 0q] ] );
x1 := KroneckerProduct( [ [q^(-1), 0q], [0q, 1q] ], IdentityMat(2,groundField) );
ny2 :=  KroneckerProduct( IdentityMat(2,groundField), [ [0q, 1q], [0q, 0q] ] );
y1 := KroneckerProduct( [ [0q, 0q], [-q^(-2)*hq, 0q] ], IdentityMat(2,groundField) );
nz2 := KroneckerProduct( IdentityMat(2,groundField), [ [0q, 0q], [0q, 1q] ] ); 
z1 := KroneckerProduct( [ [1q, 0q], [0q, q^(-1)] ], IdentityMat(2,groundField) );


## Components of the skew-inverse of nR^(-1) ##
nxm1 := KroneckerProduct( [ [1q, 0q], [0q, 0q] ], IdentityMat(2,groundField) );
xm2 := KroneckerProduct( IdentityMat(2,groundField), [ [q, 0q], [0q, 1q] ] );
nym1 :=  KroneckerProduct( [ [0q, 1q], [0q, 0q] ], IdentityMat(2,groundField) );
ym2 := KroneckerProduct( IdentityMat(2,groundField), [ [0q, 0q], [q^2*hq, 0q] ] );
nzm1 := KroneckerProduct( [ [0q, 0q], [0q, 1q] ], IdentityMat(2,groundField) ); 
zm2 := KroneckerProduct( IdentityMat(2,groundField), [ [1q, 0q], [0q, q] ] );



################################
## Defining relations for L01 ##
################################

## Definition of the free algebra on the generators of L01 ##
L01 := FreeAssociativeAlgebraWithOne(groundField, "a", "b", "c", "d");
a := L01.1;  b := L01.2;  c := L01.3;  d := L01.4;

## Matrix of generators ##
M := [ [a,b], [c,d] ];
M1 := KroneckerProduct( M, IdentityMat(2,L01) );
M2 := KroneckerProduct( IdentityMat(2,L01), M );

## Relations ##
lhs := M2*nR*M1*nRp;
rhs := nR*M1*nRp*M2;

Print("Exchange relations for L01 :\n");
for i in [1 .. 4] do
   for j in [1 .. 4] do
      Print(lhs[i][j], " = ", rhs[i][j], "\n");
   od;
od;



################################
## Defining relations for L10 ##
################################

## Definition of the free algebra on the generators of L10 ##
L10 := FreeAssociativeAlgebraWithOne(groundField, "aA", "bA", "cA", "dA",
                                                  "aB", "bB", "cB", "dB");
aA := L10.1;  bA := L10.2;  cA := L10.3;  dA := L10.4;
aB := L10.5;  bB := L10.6;  cB := L10.7;  dB := L10.8;
A2 := KroneckerProduct( IdentityMat(2,L10), [ [aA, bA], [cA, dA] ] ); 
B1 := KroneckerProduct( [ [aB, bB], [cB, dB] ], IdentityMat(2,L10) );


## Relations ##
rhs := q*nx2*nR^(-1)*A2*nR*B1*nR^(-1)*x1 
       + q*ny2*nR^(-1)*A2*nR*B1*nR^(-1)*y1
       + q*nz2*nR^(-1)*A2*nR*B1*nR^(-1)*z1;

Print("Exchange relations for L10 :\n");
for i in [1 .. 4] do
   for j in [1 .. 4] do
      Print( (B1*A2)[i][j] , " = ", rhs[i][j], "\n");
   od;
od;


## Equivalent set of relations, corresponding to the other ordering of variables ##
lhs := q^(-1)*nx1*nR*B1*nRp*A2*nR*x2 + q^(-1)*ny1*nR*B1*nRp*A2*nR*y2 + q^(-1)*nz1*nR*B1*nRp*A2*nR*z2;

Print("Equivalent set of relations for L10 :\n");
for i in [1 .. 4] do
   for j in [1 .. 4] do
      Print( (A2*B1)[i][j] , " = ", lhs[i][j], "\n");
   od;
od;



################################
## Defining relations for L02 ##
################################

## Definition of the free algebra on the generators of L02 ##
L02 := FreeAssociativeAlgebraWithOne(groundField, "a1", "b1", "c1", "d1",
                                                  "a2", "b2", "c2", "d2");
a1 := L02.1;  b1 := L02.2;  c1 := L02.3;  d1 := L02.4;
a2 := L02.5;  b2 := L02.6;  c2 := L02.7;  d2 := L02.8;
X1 := KroneckerProduct( [ [a1, b1], [c1, d1] ], IdentityMat(2,L02) ); 
Y2 := KroneckerProduct( IdentityMat(2,L02), [ [a2, b2], [c2, d2] ] );


## Relations ##
rhs := nx1*nR*X1*nR^(-1)*Y2*nR*x2 + ny1*nR*X1*nR^(-1)*Y2*nR*y2 + nz1*nR*X1*nR^(-1)*Y2*nR*z2;

Print("Exchange relations for L02 :\n");
for i in [1 .. 4] do
   for j in [1 .. 4] do
      Print( (Y2*X1)[i][j] , " = ", rhs[i][j], "\n");
   od;
od;


## Equivalent set of relations, corresponding to the other ordering of variables ##
lhs := xm2*nR^(-1)*Y2*nR*X1*nR^(-1)*nxm1 + ym2*nR^(-1)*Y2*nR*X1*nR^(-1)*nym1 + zm2*nR^(-1)*Y2*nR*X1*nR^(-1)*nzm1;

Print("Equivalent set of relations for L02 :\n");
for i in [1 .. 4] do
   for j in [1 .. 4] do
      Print( (X1*Y2)[i][j] , " = ", lhs[i][j], "\n");
   od;
od;

