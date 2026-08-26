#Ground field Q(q): rational functions in the formal variable q
q := Indeterminate(Rationals,"q");
groundField := FunctionField(Rationals,[q]); 

#Ground field CF(3): third root of unity. Comment the two line above and uncomment the two lines below to use this as ground field.
# q:= E(3);
# groundField := CF(3);

monoOq := FreeMonoid("a","b","c","d");
la := monoOq.1; lb := monoOq.2; lc := monoOq.3; ld := monoOq.4;

Oq := FreeMagmaRing(groundField, monoOq);
embOq := Embedding(monoOq, Oq);
a := la^embOq;  b := lb^embOq;  c := lc^embOq; d := ld^embOq;
1Oq := One(Oq);  0Oq := Zero(Oq);

relationsOq := [ [lb*la, q*a*b],  [lc*la, q*a*c],  [lc*lb, b*c],
                 [lb*ld, q^(-1)*d*b],  [lc*ld, q^(-1)*d*c],
                 [ld*la, a*d + (q-q^(-1))*b*c],  [la*ld, 1Oq + q^(-1)*b*c ]
               ];


applyRuleOq := function(word)
   local i, pos, pattern, replace, prefix, suffix;
   for i in [ 1 .. Length(relationsOq) ] do
      pattern := relationsOq[i][1];
      replace := relationsOq[i][2];
      pos := PositionWord(word, pattern, 1);
      if pos <> fail then
         prefix := Subword(word, 1, pos-1);
         suffix := Subword(word, pos+Length(pattern), Length(word));
         return (prefix^embOq)*replace*(suffix^embOq);
      fi;
   od;
   return word^embOq;
end;


reduceOq := function(P)
   local i, listP, wordsP, coeffsP, redP;
   listP := CoefficientsAndMagmaElements(P);
   wordsP := listP{ [ 1,3 .. Length(listP)-1 ] };
   coeffsP := listP{ [ 2,4 .. Length(listP) ] };
   Unbind(listP); #Delete local variable listP, because not used in the sequel.
   
   redP := 0Oq;  #Zero element in the free algebra
   for i in [ 1 .. Length(wordsP) ] do
      redP := redP + coeffsP[i]*applyRuleOq(wordsP[i]);
   od;
   if redP = P then
      return P;
   else
      return reduceOq(redP);
   fi;
end;