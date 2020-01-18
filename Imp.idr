-- an EDSL for Imperative Programs

infixl 5 :+
infixl 5 :-
infixl 6 :*

data AExp : Type where
  ANum : Nat -> AExp
  AVar : String -> AExp
  (:+) : AExp -> AExp -> AExp
  (:-) : AExp -> AExp -> AExp
  (:*) : AExp -> AExp -> AExp

infixl 4 :==
infixl 3 :<=
infixl 3 :/\
prefix 5 :~

data BExp : Type where
  BTrue  : BExp
  BFalse : BExp
  (:==)  : AExp -> AExp -> BExp
  (:<=)  : AExp -> AExp -> BExp
  (:~)   : BExp -> BExp
  (:/\)  : BExp -> BExp -> BExp

-- examples
-- 2 + 3 * 4

ex1 : AExp
ex1 = ANum 2 :+ ANum 3 :* ANum 4

ex2 : BExp
ex2 = ex1 :== ex1 :/\ BTrue

Mem : Type
Mem = String -> Nat

-- evaluation
aeval : Mem -> AExp -> Nat
aeval m (ANum k) = k
aeval m (AVar s) = m s
aeval m (x :+ y) = aeval m x + aeval m y
aeval m (x :- y) = minus (aeval m x) $ aeval m y 
aeval m (x :* y) = aeval m x * aeval m y

beval : Mem -> BExp -> Bool
beval m BTrue = True
beval m BFalse = False
beval m (x :== y) = aeval m x == aeval m y
beval m (x :<= y) = aeval m x <= aeval m y
beval m ((:~) x) = not $ beval m x
beval m (x :/\ y) = beval m x && beval m y


emptyMem : Mem
emptyMem = \s => Z

sing : String -> Nat -> Mem
sing s n = \a => if a == s then n else Z


beq_str : (x, y : String) -> Bool
beq_str x y = decAsBool $ decEq x y

update : String -> Nat -> Mem -> Mem
update s n m = \a => if beq_str a s then n else m a

--theorems about maps
t_update_eq : (m : Mem) -> (x : String) -> (v : Nat)
  -> (update x v m) x = v
t_update_eq m x v with (decEq x x)
  update_eq _ _ _ | Yes _     = Refl
  update_eq _ _ _ | No contra = absurd $ contra Refl


t_update_permute : (m : Mem) -> (x, y : String) 
  -> (v, w : Nat) -> Not (x = y) 
  -> update x v (update y w m) = update y w (update x v m)
t_update_permute m x y v w pneq with (decEq x y) 
  t_update_permute _ _ _ _ _ pneq | Yes ok = absurd (pneq ok)
  t_update_permute m x y v w pneq | No contra = cong ?refl1
  
-- extensionality needed!!

