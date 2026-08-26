####################################
## Definition of the ground field ##
####################################

#Ground field Q(q): rational functions in the formal variable q
q := Indeterminate(Rationals, "q");
groundField := FunctionField(Rationals, [q]);


#Ground field CF(3): third root of unity. Comment the two line above and uncomment the two lines below to use this as ground field. You can also change 3 to any order you want.
# q:= E(3);
# groundField := CF(3);

hq := q - q^(-1);



#################
## Algebra L01 ##
#################

monoL01 := FreeMonoid("a","b","c","d");
la := monoL01.1;  lb := monoL01.2;  lc := monoL01.3;  ld := monoL01.4;


L01 := FreeMagmaRing(groundField, monoL01);
embL01 := Embedding(monoL01, L01);
a := la^embL01;  b := lb^embL01;  c := lc^embL01; d := ld^embL01;
1L01 := One(L01);  0L01 := Zero(L01);


relationsL01 := [ [lb*la, a*b+q^(-1)*hq*b*d], [lc*la, a*c-q^(-1)*hq*d*c],
                  [ld*la, a*d],  [lc*lb, q^2*b*c+q^(-1)*hq*(1L01-d^2)],
                  [lb*ld, q^(-2)*d*b],  [lc*ld, q^2*d*c],
                  [la*ld, 1L01+q^2*b*c] ];


applyRuleL01 := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsL01) ] do
      pattern := relationsL01[i][1];
      replace := relationsL01[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embL01)*replace*(suffix^embL01);
      fi;
   od;
   return word^embL01;
end;


reduceL01 := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0L01;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleL01(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceL01(redP);
   fi;
end;



#################
## Algebra L10 ##
#################

monoL10 := FreeMonoid("aA","bA","cA","dA","aB","bB","cB","dB");
laA := monoL10.1;  lbA := monoL10.2;  lcA := monoL10.3;  ldA := monoL10.4;
laB := monoL10.5;  lbB := monoL10.6;  lcB := monoL10.7;  ldB := monoL10.8;

L10 := FreeMagmaRing(groundField, monoL10);
embL10 := Embedding(monoL10, L10);
aA := laA^embL10;  bA := lbA^embL10;  cA := lcA^embL10; dA := ldA^embL10;
aB := laB^embL10;  bB := lbB^embL10;  cB := lcB^embL10; dB := ldB^embL10;
1L10 := One(L10);  0L10 := Zero(L10);

relationsL10 := [ 
   [lbA*laA, aA*bA+q^(-1)*hq*bA*dA],
   [lcA*laA, aA*cA-q^(-1)*hq*dA*cA],
   [ldA*laA, aA*dA],
   [lcA*lbA, q^2*bA*cA+q^(-1)*hq*(1L10-dA^2)],
   [lbA*ldA, q^(-2)*dA*bA],
   [lcA*ldA, q^2*dA*cA],
   [laA*ldA, 1L10+q^2*bA*cA],

   [lbB*laB, aB*bB+q^(-1)*hq*bB*dB],
   [lcB*laB, aB*cB-q^(-1)*hq*dB*cB],
   [ldB*laB, aB*dB],
   [lcB*lbB, q^2*bB*cB+q^(-1)*hq*(1L10-dB^2)],
   [lbB*ldB, q^(-2)*dB*bB],
   [lcB*ldB, q^2*dB*cB],
   [laB*ldB, 1L10+q^2*bB*cB],

   [laB*laA, (q^-1)*aA*aB+(hq^2/q)*aA*dB+((-q^2*hq^3+hq)/q^2)*bA*cB+(-hq)*cA*bB+(hq^2/q)*dA*aB+(-hq^2/q)*dA*dB],
   [laB*lbA, (q^-1)*bA*aB+(hq^2/q)*bA*dB+(-hq/q^2)*dA*bB],
   [lbB*laA, (q)*aA*bB+(-hq)*bA*aB+(hq)*bA*dB],
   [lbB*lbA, (q^-1)*bA*bB],
   [laB*lcA, (-hq)*aA*cB+(q)*cA*aB+(hq)*dA*cB],
   [laB*ldA, (-q^2*hq)*bA*cB+(q)*dA*aB],
   [lbB*lcA, (-hq)*aA*dB+(q*hq^2)*bA*cB+(q)*cA*bB+(-hq)*dA*aB+(hq)*dA*dB],
   [lbB*ldA, (-hq)*bA*dB+(q^-1)*dA*bB],
   [lcB*laA, (q^-1)*aA*cB+(-hq/q^2)*cA*dB+(hq^2/q)*dA*cB],
   [lcB*lbA, (q)*bA*cB+(-hq/q^2)*dA*dB],
   [ldB*laA, (q)*aA*dB+(-q^2*hq)*bA*cB],
   [ldB*lbA, (q)*bA*dB],
   [lcB*lcA, (q^-1)*cA*cB],
   [lcB*ldA, (q)*dA*cB],
   [ldB*lcA, (q^-1)*cA*dB+(-hq)*dA*cB],
   [ldB*ldA, (q^-1)*dA*dB]
 ];


applyRuleL10 := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsL10) ] do
      pattern := relationsL10[i][1];
      replace := relationsL10[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embL10)*replace*(suffix^embL10);
      fi;
   od;
   return word^embL10;
end;


reduceL10 := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0L10;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleL10(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceL10(redP);
   fi;
end;



#################
## Algebra L02 ##
#################

monoL02 := FreeMonoid("a1","b1","c1","d1","a2","b2","c2","d2");
la1 := monoL02.1;  lb1 := monoL02.2;  lc1 := monoL02.3;  ld1 := monoL02.4;
la2 := monoL02.5;  lb2 := monoL02.6;  lc2 := monoL02.7;  ld2 := monoL02.8;

L02 := FreeMagmaRing(groundField, monoL02);
embL02 := Embedding(monoL02, L02);
a1 := la1^embL02;  b1 := lb1^embL02;  c1 := lc1^embL02;  d1 := ld1^embL02;
a2 := la2^embL02;  b2 := lb2^embL02;  c2 := lc2^embL02;  d2 := ld2^embL02;
1L02 := One(L02);  0L02 := Zero(L02);


relationsL02 := [ 
   [lb1*la1, a1*b1+q^(-1)*hq*b1*d1],
   [lc1*la1, a1*c1-q^(-1)*hq*d1*c1],
   [ld1*la1, a1*d1],
   [lc1*lb1, q^2*b1*c1+q^(-1)*hq*(1L02-d1^2)],
   [lb1*ld1, q^(-2)*d1*b1],
   [lc1*ld1, q^2*d1*c1],
   [la1*ld1, 1L02+q^2*b1*c1],

   [lb2*la2, a2*b2+q^(-1)*hq*b2*d2],
   [lc2*la2, a2*c2-q^(-1)*hq*d2*c2],
   [ld2*la2, a2*d2],
   [lc2*lb2, q^2*b2*c2+q^(-1)*hq*(1L02-d2^2)],
   [lb2*ld2, q^(-2)*d2*b2],
   [lc2*ld2, q^2*d2*c2],
   [la2*ld2, 1L02+q^2*b2*c2],

   [la2*la1, (1)*a1*a2+(-hq/q^3)*c1*b2],
   [lb2*la1, (1)*a1*b2],
   [la2*lb1, (hq/q)*a1*b2+(1)*b1*a2+(-hq/q)*d1*b2],
   [lb2*lb1, (q^2)*b1*b2],
   [lc2*la1, (1)*a1*c2+(hq/q)*c1*a2+(-hq/q)*c1*d2],
   [ld2*la1, (1)*a1*d2+(hq/q)*c1*b2],
   [lc2*lb1, (-hq/q)*a1*a2+(hq/q)*a1*d2+(q^-2)*b1*c2+((q^2*hq^2+hq^2)/q^2)*c1*b2+(hq/q)*d1*a2+(-hq/q)*d1*d2],
   [ld2*lb1, (-q*hq)*a1*b2+(1)*b1*d2+(q*hq)*d1*b2],
   [la2*lc1, (1)*c1*a2],
   [lb2*lc1, (q^-2)*c1*b2],
   [la2*ld1, (hq/q)*c1*b2+(1)*d1*a2],
   [lb2*ld1, (1)*d1*b2],
   [lc2*lc1, (q^2)*c1*c2],
   [ld2*lc1, (1)*c1*d2],
   [lc2*ld1, (-q*hq)*c1*a2+(q*hq)*c1*d2+(1)*d1*c2],
   [ld2*ld1, (-q*hq)*c1*b2+(1)*d1*d2]
 ];


applyRuleL02 := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsL02) ] do
      pattern := relationsL02[i][1];
      replace := relationsL02[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embL02)*replace*(suffix^embL02);
      fi;
   od;
   return word^embL02;
end;


reduceL02 := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0L02;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleL02(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceL02(redP);
   fi;
end;
