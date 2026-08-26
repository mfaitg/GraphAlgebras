####################################
## Definition of the ground field ##
####################################

l := 3; #Replace 3 by any odd integer > 1 of your choice.
        #But note that, in practice, the size of matrices will be unmanageable for l >= 5.

q := E(l); #l-th root of unity
groundField := CF(l); #Cyclotomic field associated to q


#############################################################################
## Function isSimpleXqChi: decides if the algebra Xq(chi) is simple over C ##
#############################################################################

isSimpleXqChi := function(x1, x2, x3, x4)
   local i, j, k, m, n, F1, F2, F3, F4, XqChi;

   ## Construction of the matrices of the right regular representation of Xq(chi) ##

   F1 := NullMat(l^4, l^4, groundField);;
   for i in [0 .. l-1] do
      for j in [0 .. l-1] do
         for k in [0 .. l-1] do
            for m in [0 .. l-1] do
               n := 1 + i + j*l + k*l^2 + m*l^3;
               #We define the non-zero coefficients in the n-th column of F1:
               if i < l-1 then
                  F1[n + 1][n] := 1;
               else
                  F1[n - (l-1)][n] := x1;
               fi;
            od;
         od;
     od;
   od;


   F2 := NullMat(l^4, l^4, groundField);;
   for i in [0 .. l-1] do
      for j in [0 .. l-1] do
         for k in [0 .. l-1] do
            for m in [0 .. l-1] do
               n := 1 + i + j*l + k*l^2 + m*l^3;
               #We define the non-zero coefficients in the n-th column of F2:
               if i = 0 and j = l-1 then
                  F2[n - l*(l-1)][n] := x2;
               elif i > 0 and j = l-1 then
                  F2[n - l*(l-1)][n] := x2*q^(-2*i);
                  F2[n - 1][n] := q^(-2*i) - 1;
               elif i = 0 and j < l-1 then
                  F2[n + l][n] := 1;
               else
                  F2[n + l][n] := q^(-2*i);
                  F2[n -1 ][n] := q^(-2*i) - 1;
               fi;
            od;
         od;
     od;
   od;


   F3 := NullMat(l^4, l^4, groundField);;
   for i in [0 .. l-1] do
      for j in [0 .. l-1] do
         for k in [0 .. l-1] do
            for m in [0 .. l-1] do
               n := 1 + i + j*l + k*l^2 + m*l^3;
               #We define the non-zero coefficients in the n-th column of F2:
               if j = 0 and k = l-1 then
                  F3[n - l^2*(l-1)][n] := x3*q^(2*i);
               elif j > 0 and k = l-1 then
                  F3[n - l^2*(l-1)][n] := x3*q^(2*(i-j));
                  F3[n - l][n] := q^(2*i)*( q^(-2*j) - 1 );
               elif j = 0 and k < l-1 then
                  F3[n + l^2][n] := q^(2*i) ;
               else
                  F3[n + l^2][n] := q^(2*(i-j));
                  F3[n - l][n] := q^(2*i)*( q^(-2*j) - 1 );
               fi;
            od;
         od;
     od;
   od;


   F4 := NullMat(l^4, l^4, groundField);;
   for i in [0 .. l-1] do
      for j in [0 .. l-1] do
         for k in [0 .. l-1] do
            for m in [0 .. l-1] do
               n := 1 + i + j*l + k*l^2 + m*l^3;
               #We define the non-zero coefficients in the n-th column of F2:
               if k = 0 and m = l-1 then
                  F4[n - l^3*(l-1)][n] := x4*q^(2*(j-i));
               elif k > 0 and m = l-1 then
                  F4[n - l^3*(l-1)][n] := x4*q^(2*(j-i-k));
                  F4[n - l^2][n] := q^(2*(j-i))*( q^(-2*k) - 1 );
               elif k = 0 and m < l-1 then
                  F4[n + l^3][n] := q^(2*(j-i));
               else
                  F4[n + l^3][n] := q^(2*(j-i-k));
                  F4[n - l^2][n] := q^(2*(j-i))*( q^(-2*k) - 1 );
               fi;
            od;
         od;
     od;
   od;

   ## Definition of the algebra as its regular representation and central simplicity test ##

   XqChi := AlgebraWithOne( groundField, [F1, F2, F3, F4] );
   return IsSimpleAlgebra(XqChi) and Dimension(Centre(XqChi)) = 1;
end;