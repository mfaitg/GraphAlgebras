#Ground field Q(q): rational functions in the formal variable q
q := Indeterminate(Rationals,"q");
groundField := FunctionField(Rationals,[q]); 

#Ground field CF(3): third root of unity. Comment the two line above and uncomment the two lines below to use this as ground field.
# q:= E(3);
# groundField := CF(3);

groupUq := FreeGroup("e","f","k");
le := groupUq.1;  lf := groupUq.2;  lk := groupUq.3;

Uq := FreeMagmaRing(groundField, groupUq);
embUq := Embedding(groupUq, Uq);
e := le^embUq;  f := lf^embUq;  k := lk^embUq;
1Uq := One(Uq);  0Uq := Zero(Uq);


relationsUq := [  [lk*le, q^2*e*k],  [lk*lf, q^(-2)*f*k], 
                  [lf*le, e*f - (k - k^(-1))/(q-q^(-1))],
                  [lk^(-1)*le, q^(-2)*e*k^(-1)],  [lk^(-1)*lf, q^2*f*k^(-1)]  ];


applyRuleUq := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsUq) ] do
      pattern := relationsUq[i][1];
      replace := relationsUq[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embUq)*replace*(suffix^embUq);
      fi;
   od;
   return word^embUq;
end;


reduceUq := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0Uq;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleUq(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceUq(redP);
   fi;
end;