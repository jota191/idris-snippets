data I : Type where
  Pos  : Nat -> I
  Neg  : Nat -> I
  Zer  : I

data Even : I -> Type where
  Ev_Z : Even Zer
  Ev_2 : Even (Pos 1)
  Ev_m2: Even (Neg 1)
  Ev_P : Even (Pos n) -> Even (Pos (S (S n)))
  Ev_N : Even (Neg n) -> Even (Neg (S (S n)))

even_10 : Even (Pos 9)
even_10 = Ev_P (Ev_P (Ev_P (Ev_P Ev_2)))

eqthmEven : (n : Nat) -> Even (Pos n) 
  -> Even (Pos (S (S n)))
eqthmEven n e = Ev_P e

simpl : (m : Nat) -> (n : Nat) -> n = m 
  -> m = n
simpl m n eq = sym eq


data Buff : Type -> Type where
  Empty : Buff a
  One   : a -> Buff a
  Two   : a -> a -> Buff a

data IsEmptyBuff : Buff a -> Type where
  IsEmpty : (Empty : Buff a) 
     -> IsEmptyBuff Empty

data IsFullBuff : Buff a -> Type where
