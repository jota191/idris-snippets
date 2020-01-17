-- A simple expression Language

data Exp : Type -> Type where
  ValN  : Nat  -> Exp Nat
  ValB  : Bool -> Exp Bool
  Add   : Exp Nat -> Exp Nat -> Exp Nat
  Eq    : (Eq a) => Exp a -> Exp a -> Exp Bool


{- CANNOT PATTERN MATCH ON TYPES-}
-- https://stackoverflow.com/questions/23220884/why-is-typecase-a-bad-thing
-- type inference, actually returning a type
-- typeOf : Exp -> Type
-- typeOf (ValN k) = Nat
-- typeOf (ValB x) = Bool
-- typeOf (Add x y) with (typeOf x)
--   typeOf (Add x y) | Nat = Nat
-- typeOf (Eq x y)
--    = Void

eval : (e : Exp a) -> a
eval (ValN k)  = k
eval (ValB x)  = x
eval (Add x y) = eval x + eval y
eval (Eq x y)  = eval x == eval y


optimize : Exp a -> Exp a
optimize (Add (ValN Z) y) = optimize y
optimize (Add a y) = Add a $ optimize y
optimize (Eq x y) = Eq (optimize x)(optimize y) 
optimize a = a

th_optimize_correct : {a : Type} ->
   (e : Exp a) -> eval e = eval (optimize e)
th_optimize_correct (ValN k) = Refl
th_optimize_correct (ValB x) = Refl
th_optimize_correct (Add (ValN Z) y) 
  = rewrite th_optimize_correct y in Refl
th_optimize_correct (Add (ValN (S k)) y) 
  = rewrite th_optimize_correct y in Refl
th_optimize_correct (Add (Add x z) y) 
  = rewrite th_optimize_correct y in Refl
th_optimize_correct (Eq x y) 
  = rewrite th_optimize_correct y in 
    rewrite th_optimize_correct x in Refl

