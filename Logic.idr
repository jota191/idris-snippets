--** Conjunction (pairs are builtin, I prefer to define them by hand 
--  as an exercise)
data And : Type -> Type -> Type where
  Conj : a -> b -> And a b

  -- destructors
and_elim_l : a `And` b -> a
and_elim_l (Conj x y) = x

and_elim_r : a `And` b -> b
and_elim_r (Conj x y) = y

------------------------------------------------------------
--** Disjunction
data Or : Type -> Type -> Type where
  Inl : a -> a `Or` b
  Inr : b -> a `Or` b

  -- destructor
or_elim : (a -> c) -> (b -> c) -> (a `Or` b -> c)
or_elim f g (Inl x) = f x
or_elim f g (Inr x) = g x


--** Bottom
data Bot : Type where {}

bot_elim : Bot -> a
bot_elim x impossible

-- Negation
neg : Type -> Type
neg a = a -> Bot


--Iff
iff : Type -> Type -> Type
iff a b = (a -> b) `And` (b -> a)

------------------------------------------------------------
-- no more definitions by hand, we use builtins, as intended:
-- forall: dependent product
-- arrow:  arrow type
-- exists: dependent coproduct (dep pair)


-- * some theorems

t_ainna : a -> neg (neg a)
t_ainna a = \contra => contra a

t_curry : (a `And` b -> c) -> a -> b -> c
t_curry f a b = f (Conj a b)


t_tauto1 : (a `And` b -> c) `iff` (a -> b -> c)
t_tauto1 = Conj t_curry 
                (\f => \(Conj  a b) => f a b) -- uncurry


-- a first order tautology, over nats
t_tauto2 : (p : Nat -> Type) -> (x : Nat ** neg (p x)) 
  -> neg ((x : Nat) -> p x)
t_tauto2 p (x ** pf) = \a => let aux  = a x
                             in pf aux




-- destructors a la Martin Lof Type Theory

data N = Zero | Succ N

nat_elim : (p : N -> Type) -> p Zero 
  -> ((n : N) -> p n -> p (Succ n)) -> (n : N) -> p n
nat_elim p e f Zero = e
nat_elim p e f (Succ n) = f n (nat_elim p e f n)



-- axiom of choice, in natural numbers
choiceN : (r : Nat -> Nat -> Type) -> 
   ((x : Nat) -> ( y : Nat ** r x y)) -> 
   (f : (Nat -> Nat) ** ((x : Nat) -> r x (f x)))
choiceN r f = (\n => fst (f n) ** \k => snd (f k))
