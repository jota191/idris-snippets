uip : (A : Type) -> (x : A) -> (y : A) 
   -> (p : x = y) -> (q : x = y) -> p = q
uip a x x Refl Refl = Refl

