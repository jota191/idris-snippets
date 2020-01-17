import Prelude.Algebra as Alg

-- Definition of natural numbers

data N = Zero | Succ N

-- Addition

add : N -> N -> N
add Zero     n = n
add (Succ m) n = Succ (add m n)


-- Some properties

add_assoc : (n, m, k : N) -> add (add n m) k = add n (add m k)
add_assoc Zero     m k = the (add m k = add m k) Refl
add_assoc (Succ x) m k = rewrite (add_assoc x m k) in Refl

add_neutral_R : (m : N) -> add m Zero = m
add_neutral_R Zero = Refl
add_neutral_R (Succ x) = rewrite (add_neutral_R x) in Refl


-- Semigroup and monoid, interfaces do not have laws included

implementation Semigroup N where
  (<+>) = add

implementation Monoid N where
  neutral = Zero


-- I do them by my own

interface (Monoid a) => VerifiedMonoid a where
  assoc_proof : (x, y, z : a) -> (x <+> y) <+> z = x <+> (y <+> z)
  neutral_R   : (x : a) -> x <+> Alg.neutral = x
  neutral_L   : (x : a) -> the a Alg.neutral <+> x = x

-- Implementation

implementation VerifiedMonoid N where
  assoc_proof = add_assoc
  neutral_R = add_neutral_R
  neutral_L = \ _ => Refl

-- Maybe is a monoid, with Nothing as the neutral, given a monoid as
-- the supporter, lets redefine optionals (a la ML, to avoid name
-- clash)

data Option a = Some a | None

implementation Semigroup a => Semigroup (Option a) where
  (Some x) <+> (Some y) = Some $ x <+> y
  (Some x) <+> None = Some x
  None <+> r = r

implementation Monoid a => Monoid (Option a) where
  neutral = None

implementation VerifiedMonoid a => VerifiedMonoid (Option a) where
  assoc_proof (Some x) (Some y) (Some z) = cong $ assoc_proof x y z
                                 -- rewrite assoc_proof x y z in Refl
  assoc_proof (Some x) (Some y) None = Refl
  assoc_proof (Some x) None z = Refl
  assoc_proof None y z        = Refl
  neutral_R  (Some x) = Refl
  neutral_R  None = Refl
  neutral_L  x = Refl

-- equality
eq : N -> N -> Bool
eq Zero Zero = True
eq Zero (Succ x) = False
eq (Succ x) Zero = False
eq (Succ x) (Succ y) = eq x y

zeroNotSucc : {n : N} -> (Zero = Succ n) -> Void
zeroNotSucc Refl impossible

succNotZero : {n : N} -> (Succ n = Zero) -> Void
succNotZero Refl impossible

succ_inj : {n, m : N} -> Succ n = Succ m -> n = m
succ_inj Refl = Refl

decide_eq : (n, m : N) -> Dec (n = m)
decide_eq Zero Zero = Yes Refl
decide_eq Zero (Succ x) = No $ zeroNotSucc
decide_eq (Succ x) Zero = No $ succNotZero
decide_eq (Succ x) (Succ y) 
  = let dec = decide_eq x y
    in case dec of
      Yes prf   => Yes $ cong prf
      No contra => No $ \sxnsy => contra $ succ_inj sxnsy

decide_eq' : (n, m : N) -> Dec (n = m)
decide_eq' n m with (eq n m)
  decide_eq' n m | True = ?l
  decide_eq' n m | False = ?la
  
  -- let lala = eq n m 
       -- in case eq n m of
       --     True => ?h
       --     False=> ?j


