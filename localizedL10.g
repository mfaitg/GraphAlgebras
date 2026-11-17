#############################
## Choose the ground field ##
#############################

## Ground field Q(s): rational functions in the formal variable s such that q = s^2 ##
s := Indeterminate(Rationals, "s");
groundField := FunctionField(Rationals, [s]);
q := s^2;


## Ground field CF(ord): Cyclotomic Field for exp(2*i*pi/ord), where ord is an odd integer. ##
# CF(ord) alreay contains a square root s of q, that is s = q^((ord+1)/2) and we make this choice for the square root.
# In this way there is no need to introduce a quadratic extension of CF(ord).
# Comment the three lines above and uncomment the four lines below to use this as ground field. You can change 3 to any order you want.
# ord := 3;
# groundField := CF(ord);
# q := E(ord);
# s := q^( (ord+1)/2 ); #Square root of q, of order ord.


hq := q - q^(-1);



####################
## Algebra L10Loc ##
####################

groupL10 := FreeGroup("bA","cA","dA","bB","cB","dB");
lbA := groupL10.1;  lcA := groupL10.2;  ldA := groupL10.3;
lbB := groupL10.4;  lcB := groupL10.5;  ldB := groupL10.6;

L10Loc := FreeMagmaRing(groundField, groupL10);
embL10Loc := Embedding(groupL10, L10Loc);
bA := lbA^embL10Loc;  cA := lcA^embL10Loc; dA := ldA^embL10Loc;
bB := lbB^embL10Loc;  cB := lcB^embL10Loc; dB := ldB^embL10Loc;
1L10Loc := One(L10Loc);  0L10Loc := Zero(L10Loc);
aA := (1L10Loc + q^2*bA*cA)*dA^(-1); 
aB := (1L10Loc + q^2*bB*cB)*dB^(-1);

relationsL10Loc := [ 
   [lcA*lbA, q^2*bA*cA + q^(-1)*hq*(1L10Loc-dA^2)],
   [ldA*lbA, q^2*bA*dA],
   [ldA*lcA, q^(-2)*cA*dA],
   [ldA^(-1)*lbA, q^(-2)*bA*dA^(-1)],
   [ldA^(-1)*lcA, q^2*cA*dA^(-1)],

   [lcB*lbB, q^2*bB*cB + q^(-1)*hq*(1L10Loc-dB^2)],
   [ldB*lbB, q^2*bB*dB],
   [ldB*lcB, q^(-2)*cB*dB],
   [ldB^(-1)*lbB, q^(-2)*bB*dB^(-1)],
   [ldB^(-1)*lcB, q^2*cB*dB^(-1)],

   [lbB*lbA, (q^-1)*bA*bB],
   [lbB*lcA, (-hq)*aA*dB+(q*hq^2)*bA*cB+(q)*cA*bB+(-hq)*dA*aB+(hq)*dA*dB],
   [lbB*ldA, (-hq)*bA*dB+(q^-1)*dA*bB],
   [lbB*ldA^(-1), q*dA^(-1)*bB + hq*bA*dA^(-2)*dB],

   [lcB*lbA, (q)*bA*cB+(-hq/q^2)*dA*dB],
   [lcB*lcA, (q^-1)*cA*cB],
   [lcB*ldA, (q)*dA*cB],
   [lcB*ldA^(-1), q^(-1)*dA^(-1)*cB],

   [ldB*lbA, (q)*bA*dB],
   [ldB*lcA, (q^-1)*cA*dB+(-hq)*dA*cB],
   [ldB*ldA, (q^-1)*dA*dB],
   [ldB*ldA^(-1), q*dA^(-1)*dB],

   [ldB^(-1)*lbA, q^(-1)*bA*dB^(-1)],
   [ldB^(-1)*lcA, q*cA*dB^(-1) + q^4*hq*dA*cB*dB^(-2)],
   [ldB^(-1)*ldA, q*dA*dB^(-1)],
   [ldB^(-1)*ldA^(-1), q^(-1)*dA^(-1)*dB^(-1)]
 ];

applyRuleL10Loc := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsL10Loc) ] do
      pattern := relationsL10Loc[i][1];
      replace := relationsL10Loc[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embL10Loc)*replace*(suffix^embL10Loc);
      fi;
   od;
   return word^embL10Loc;
end;


reduceL10Loc := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0L10Loc;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleL10Loc(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceL10Loc(redP);
   fi;
end;



###################
## Algebra HqLoc ##
###################

groupHq := FreeGroup("b","c","d","e","f","k");
lb := groupHq.1;  lc := groupHq.2;  ld := groupHq.3;
le := groupHq.4;  lf := groupHq.5;  lk := groupHq.6;

HqLoc := FreeMagmaRing(groundField, groupHq);
embHqLoc := Embedding(groupHq, HqLoc);
b := lb^embHqLoc;  c := lc^embHqLoc; d := ld^embHqLoc;
e := le^embHqLoc;  f := lf^embHqLoc;  k := lk^embHqLoc;
1HqLoc := One(HqLoc);  0HqLoc := Zero(HqLoc);
a := (1HqLoc + q^(-1)*b*c)*d^(-1); 


relationsHqLoc := [ 
   [lc*lb, b*c],  [ld*lb, q*b*d],  [ld*lc, q*c*d],
   [ld^(-1)*lb, q^(-1)*b*d^(-1)],  [ld^(-1)*lc, q^(-1)*c*d^(-1)],

   [lk*le, q^2*e*k],  [lk*lf, q^(-2)*f*k],  [lf*le, e*f - (k - k^(-1))/(q-q^(-1))],
   [lk^(-1)*le, q^(-2)*e*k^(-1)],  [lk^(-1)*lf, q^2*f*k^(-1)],

   [le*lb, b*e + a*k],  [le*lc, c*e],  [le*ld, d*e + c*k],  [le*ld^(-1), d^(-1)*e - c*d^(-2)*k],

   [lf*lb, q*b*f],  [lf*lc, q^(-1)*c*f + d], [lf*ld, q*d*f],  [lf*ld^(-1), q^(-1)*d^(-1)*f],

   [lk*lb, q^(-1)*b*k],  [lk*lc, q*c*k],  [lk*ld, q^(-1)*d*k],  [lk*ld^(-1), q*d^(-1)*k],

   [lk^(-1)*lb, q*b*k^(-1)],  [lk^(-1)*lc, q^(-1)*c*k^(-1)],  [lk^(-1)*ld, q*d*k^(-1)],
   [lk^(-1)*ld^(-1), q^(-1)*d^(-1)*k^(-1)]

 ];


applyRuleHqLoc := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsHqLoc) ] do
      pattern := relationsHqLoc[i][1];
      replace := relationsHqLoc[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embHqLoc)*replace*(suffix^embHqLoc);
      fi;
   od;
   return word^embHqLoc;
end;


reduceHqLoc := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0HqLoc;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleHqLoc(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceHqLoc(redP);
   fi;
end;



######################
## Frolov's algebra ##
######################

groupFrol := FreeGroup("X1","X2","X3","X4","Y1","Y2");
lX1 := groupFrol.1;  lX2 := groupFrol.2;  lX3 := groupFrol.3;
lX4 := groupFrol.4;  lY1 := groupFrol.5;  lY2 := groupFrol.6;

Frol := FreeMagmaRing(groundField, groupFrol);
embFrol := Embedding(groupFrol, Frol);
X1 := lX1^embFrol;  X2 := lX2^embFrol; X3 := lX3^embFrol;
X4 := lX4^embFrol;  Y1 := lY1^embFrol;  Y2 := lY2^embFrol;
1Frol := One(Frol);  0Frol := Zero(Frol);


relationsFrol := [ 
   [lX2*lX1, q^(-2)*X1*X2 - q^(-1)*hq*1Frol],  [lX3*lX1, q^2*X1*X3], [lX4*lX1, q^(-2)*X1*X4],
   [lX3*lX2, q^(-2)*X2*X3 - q^(-1)*hq*1Frol],  [lX4*lX2, q^2*X2*X4], [lX4*lX3, q^(-2)*X3*X4 - q^(-1)*hq*1Frol],

   [lY2*lY1, q^(-1)*Y1*Y2],  [lY2^(-1)*lY1, q*Y1*Y2^(-1)],  [lY2*lY1^(-1), q*Y1^(-1)*Y2],  [lY2^(-1)*lY1^(-1), q^(-1)*Y1^(-1)*Y2^(-1)],

   [lY1*lX1, X1*Y1],  [lY1*lX2, X2*Y1],  [lY1*lX3, X3*Y1],  [lY1*lX4, X4*Y1],
   [lY1^(-1)*lX1, X1*Y1^(-1)],  [lY1^(-1)*lX2, X2*Y1^(-1)],  [lY1^(-1)*lX3, X3*Y1^(-1)],  [lY1^(-1)*lX4, X4*Y1^(-1)],
   [lY2*lX1, X1*Y2],  [lY2*lX2, X2*Y2],  [lY2*lX3, X3*Y2],  [lY2*lX4, X4*Y2],
   [lY2^(-1)*lX1, X1*Y2^(-1)],  [lY2^(-1)*lX2, X2*Y2^(-1)],  [lY2^(-1)*lX3, X3*Y2^(-1)],  [lY2^(-1)*lX4, X4*Y2^(-1)]
 ];


applyRuleFrol := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsFrol) ] do
      pattern := relationsFrol[i][1];
      replace := relationsFrol[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embFrol)*replace*(suffix^embFrol);
      fi;
   od;
   return word^embFrol;
end;


reduceFrol := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0Frol;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleFrol(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceFrol(redP);
   fi;
end;



######################################################
## Isomorphism of algebras between L10Loc and HqLoc ##
######################################################

## Morphism L10Loc ---> HqLoc ##
im_L10ToHq := [ [lbA, q^(-1)*hq*f],  [lcA, hq*k^(-1)*e],  [ldA, k^(-1)],
                [ldA^(-1), k],  [lbB, s^(-1)*(b + hq*d*f)],  
                [lcB, s^(-1)*(c + q*hq*d*k^(-1)*e)],
                [ldB, s*d*k^(-1)],  [ldB^(-1), s*d^(-1)*k] ];

apply_L10ToHq := function(word)
   local i, img, poly;
   poly := One(HqLoc); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_L10ToHq do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

L10ToHq := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(HqLoc);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_L10ToHq(wordsP[i]);
   od;
  return reduceHqLoc(fP);
end;

# The following GAP function allows us to check that these values indeed define a morphism.
# For this it suffices to launch the command "isCompatibleL10Hq(L10ToHq);" in the GAP console.
isCompatibleL10Hq := function(f)
   local rel, answer;
   answer := true;
   for rel in relationsL10Loc do
      if f(rel[1]^embL10Loc) <> f(rel[2]) then
        answer := false;
        Print(rel,"\n");
        break;
      fi;
   od;
   return answer;
end;


## Inverse morphism, HqLoc ---> L10Loc ##
im_HqToL10 := [ [le, hq^(-1)*dA^(-1)*cA],  [lf, q*hq^(-1)*bA],  [lk, dA^(-1)],
                [lk^(-1), dA],  [lb, s*(bB - bA*dA^(-1)*dB)],
                [lc, s*(q^2*cB - q^2*cA*dA^(-1)*dB)],  [ld, s*dA^(-1)*dB],
                [ld^(-1), s*dA*dB^(-1)] ];

apply_HqToL10 := function(word)
   local i, img, poly;
   poly := One(L10Loc); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_HqToL10 do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

HqToL10 := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(L10Loc);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_HqToL10(wordsP[i]);
   od;
  return reduceL10Loc(fP);
end;

#You can check that the morphisms L10ToHq and HqToL10 are indeed inverse each other by running the following commands in the console (uncomment before copy-pasting):
# for el in [bA, cA, dA, dA^(-1), bB, cB, dB, dB^(-1)] do
#    Print( "HqToL10(L10ToHq( ",el," )) = ", HqToL10(L10ToHq(el)), "\n" );
# od;

# for el in [e, f, k, k^(-1), b, c, d, d^(-1)] do
#    Print( "L10ToHq(HqToL10( ",el," )) = ", L10ToHq(HqToL10(el)), "\n" );
# od;



################################################################
## Isomorphism of algebras between HqLoc and Frolov's algebra ##
################################################################

## Morphism Frol ---> HqLoc ##
im_FrolToHq := [ [lX1, -c*d*k^(-1)], [lX2, q^(-1)*hq*d^(-2)*f*k], [lX3, hq*d^2*e + q^2*c*d*k],
                 [lX4, b*d^(-1)*k^(-1)], [lY1, k^(-1)], [lY1^(-1), k], [lY2, s*d*k^(-1)], [lY2^(-1), s*d^(-1)*k] ];

apply_FrolToHq := function(word)
   local i, img, poly;
   poly := One(HqLoc); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_FrolToHq do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

FrolToHq := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(HqLoc);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_FrolToHq(wordsP[i]);
   od;
  return reduceHqLoc(fP);
end;

# The following GAP function allows us to check that these values indeed define a morphism.
# For this it suffices to launch the command "isCompatibleFrolHq(FrolToHq);" in the GAP console.
isCompatibleFrolHq := function(f)
   local rel, answer;
   answer := true;
   for rel in relationsFrol do
      if f(rel[1]^embFrol) <> f(rel[2]) then
        answer := false;
        Print(rel,"\n");
        break;
      fi;
   od;
   return answer;
end;


## Inverse morphism, HqLoc ---> Frol ##
im_HqToFrol := [ [le, hq^(-1)*( X1 + q^2*X3*Y1^2 )*Y2^(-2)], [lf, q*hq^(-1)*X2*Y1^(-1)*Y2^2],
                 [lk, Y1^(-1)], [lk^(-1), Y1],
                 [lb, s*X4*Y1^(-2)*Y2], [lc, -s*X1*Y2^(-1)], [ld, s*Y1^(-1)*Y2], [ld^(-1), s*Y1*Y2^(-1)] ];

apply_HqToFrol := function(word)
   local i, img, poly;
   poly := One(Frol); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_HqToFrol do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

HqToFrol := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(Frol);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_HqToFrol(wordsP[i]);
   od;
  return reduceFrol(fP);
end;


#You can check that the morphisms FrolToHq and HqToFrol are indeed inverse each other by running the following commands in the console (uncomment before copy-pasting):
# for el in [X1, X2, X3, X4, Y1, Y1^(-1), Y2, Y2^(-1)] do
#    Print( "HqToFrol(FrolToHq( ",el," )) = ", HqToFrol(FrolToHq(el)), "\n" );
# od;

# for el in [e, f, k, k^(-1), b, c, d, d^(-1)] do
#    Print( "FrolToHq(HqToFrol( ",el," )) = ", FrolToHq(HqToFrol(el)), "\n" );
# od;



#################################################################
## Isomorphism of algebras between L10Loc and Frolov's algebra ##
#################################################################

## Morphism Frol ---> L10Loc ##

im_FrolToL10 := [ [lX1, q^2*(cA*dA^(-1)*dB - cB)*dB], [lX2, q^2*bA*dA*dB^(-2)], [lX3, dA^(-2)*cB*dB],
                  [lX4, dA^2*bB*dB^(-1) - q^4*bA*dA], [lY1, dA], [lY1^(-1), dA^(-1)],
                  [lY2, dB], [lY2^(-1), dB^(-1)] ];

apply_FrolToL10 := function(word)
   local i, img, poly;
   poly := One(L10Loc); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_FrolToL10 do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

FrolToL10 := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(L10Loc);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_FrolToL10(wordsP[i]);
   od;
  return reduceL10Loc(fP);
end;


# The following GAP function allows us to check that these values indeed define a morphism.
# For this it suffices to launch the command "isCompatibleFrolL10(FrolToL10);" in the GAP console.
isCompatibleFrolL10 := function(f)
   local rel, answer;
   answer := true;
   for rel in relationsFrol do
      if f(rel[1]^embFrol) <> f(rel[2]) then
        answer := false;
        Print(rel,"\n");
        break;
      fi;
   od;
   return answer;
end;



## Inverse morphism L10Loc ---> Frol ##

im_L10ToFrol := [ [lbA, X2*Y1^(-1)*Y2^2], [lcA, ( X1 + q^2*X3*Y1^2 )*Y1*Y2^(-2)], [ldA, Y1], [ldA^(-1), Y1^(-1)],
                  [lbB, X4*Y1^(-2)*Y2 + q^2*X2*Y1^(-2)*Y2^3], [lcB, X3*Y1^2*Y2^(-1)], [ldB, Y2],
                  [ldB^(-1), Y2^(-1)] ];


apply_L10ToFrol := function(word)
   local i, img, poly;
   poly := One(Frol); #Unit element in the target algebra
   for i in [ 1 .. Length(word) ] do
      for img in im_L10ToFrol do
         if Subword(word,i,i) = img[1] then
            poly := poly*img[2];
            break;
         fi;
      od;
   od;
   return poly;
end;

L10ToFrol := function(P)
   local i, listP, wordsP, coeffsP, fP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, not used in the sequel.
   fP := Zero(Frol);  #Zero element in the target algebra
   for i in [ 1 .. Length(wordsP) ] do
      fP := fP + coeffsP[i]*apply_L10ToFrol(wordsP[i]);
   od;
  return reduceFrol(fP);
end;


#You can check that the morphisms FrolToL10 and L10ToFrol are indeed inverse each other by running the following commands in the console (uncomment before copy-pasting):
# for el in [X1, X2, X3, X4, Y1, Y1^(-1), Y2, Y2^(-1)] do
#    Print( "L10ToFrol(FrolToL10( ",el," )) = ", L10ToFrol(FrolToL10(el)), "\n" );
# od;

# for el in [bA, cA, dA, dA^(-1), bB, cB, dB, dB^(-1)] do
#    Print( "FrolToL10(L10ToFrol( ",el," )) = ", FrolToL10(L10ToFrol(el)), "\n" );
# od;



######################################################################
## Computing the Quantum Moment Map in terms of Frolov's generators ##
######################################################################

A := [ [aA, bA], [cA, dA] ];;
invA := [ [dA, -q^2*bA], [-q^2*cA, q^2*aA - q*hq*dA] ];;
B := [ [aB, bB], [cB, dB] ];;
invB := [ [dB, -q^2*bB], [-q^2*cB, q^2*aB - q*hq*dB] ];;
C := q^(-3)*B*invA*invB*A;;
C11 := L10ToFrol(C[1][1]);;  C12 := L10ToFrol(C[1][2]);;
C21 := L10ToFrol(C[2][1]);;  C22 := L10ToFrol(C[2][2]);;

U := 1Frol + X1*X2;;  V := 1Frol + X3*X4;;

# Run the following commands to check the expressions of C12, C21 and C22 through Frolov's isomorphism (uncomment before copy-pasting in the console):

# C22 = q^(-2)*reduceFrol(U*V + X1*X4);
## Answer is "true", meaning that the equality is correct

# C12 = q^(-2)*reduceFrol(-X4 - X2*V + C22*X4*Y1^(-2) + q^2*C22*X2*Y1^(-2)*Y2^2);
## Answer is "true", meaning that the equality is correct

# C21 = q^(-2)*reduceFrol(-X1 - U*X3 + X1*C22*Y2^(-2) + q^2*X3*C22*Y1^2*Y2^(-2));
## Answer is "true", meaning that the equality is correct


