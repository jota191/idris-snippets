-- A simple expression Language

data Exp : Type -> Type where
  ValN  : Nat  -> Exp Nat
  ValB  : Bool -> Exp Bool
  Add   : Exp Nat -> Exp Nat -> Exp Nat



-- evaluator
eval : (e : Exp a) -> a
eval (ValN k)  = k
eval (ValB x)  = x
eval (Add x y) = eval x + eval y

-- optimization
optimize : Exp a -> Exp a
optimize (Add (ValN Z) y) = optimize y
optimize (Add a y) = Add a $ optimize y
optimize a = a


-- correctness
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



-- evaluation as a relation
data EvalRel : Exp a -> a -> Type where
  EvalValN : {i : Nat} -> EvalRel (ValN i) i
  EvalValB : {b : Bool}-> EvalRel (ValB b) b
  EvalAdd  : EvalRel t i -> EvalRel u j -> EvalRel (Add t u) (i + j) 


theorem_soundness : (Eq a) => {a : Type} ->
   (e : Exp a) -> (v : a) -> (eval e = v) -> EvalRel e v 
theorem_soundness (ValN k) (eval (ValN k)) Refl = EvalValN
theorem_soundness (ValB x) (eval (ValB x)) Refl = EvalValB
theorem_soundness {a = Nat} (Add x y) (eval (Add x y)) Refl 
  = let l = theorem_soundness {a = Nat} x (eval x) Refl
        r = theorem_soundness {a = Nat} y (eval y) Refl
    in EvalAdd l r


theorem_completness :
   (e : Exp a) -> (v : a) -> EvalRel e v -> (eval e = v)
theorem_completness (ValN v) v EvalValN 
  = Refl
theorem_completness (ValB v) v EvalValB 
  = Refl
theorem_completness (Add y z) (i + j) (EvalAdd p q) 
  = rewrite the (eval y = i) (theorem_completness y i p) in
    rewrite the (eval z = j) (theorem_completness z j q) in
    Refl
