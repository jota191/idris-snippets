module HoTT

-- Pattern matching rules in Idris are strong. One can prove
-- uniqueness of identity proofs, which is not compatible with
-- univalence.

uip : {A : Type} -> (x : A) -> (y : A) 
   -> (p : x = y) -> (q : x = y) -> p = q
uip x x Refl Refl = Refl

{- interludium: I was about to define this:

-- Let's define an isomorphism interface
-- interface Iso (A : Type) (B : Type) where
  ab : A -> B
  ba : B -> A
  ia : (a : A) -> ba (ab a) = a
  ib : (b : B) -> ab (ba b) = b

-- Univalence axiom:
univalence_ax : Iso a b => a = b
univalence_ax = believe_me ()

if interface definitions are just as in Haskell, this allows only une
definition of Iso Bool Bool, and then it is not clear how to get the
inconsistency

-}

record Iso (a : Type) (b : Type) where
  constructor MkIso
  ab : a -> b
  ba : b -> a
  ia : (x : a) -> ba (ab x) = x
  ib : (x : b) -> ab (ba x) = x

postulate univalence_ax : Iso a b -> a = b {- only one way -}

-- Now let us prove that a type with two constructors is isomorphic to
-- itself. There are two automorphisms, and with uip we can prove that
-- constructors are not injective!

--data Bool : Type where
--  True  : Bool
--  False : Bool


-- We define an isomorphism from Bool to Bool using the identity
isoId : Iso Bool Bool
isoId = MkIso id id (\_ => Refl) (\_ => Refl)


-- and another one using negation
neg : Bool -> Bool
neg False = True
neg True  = False

isoNeg : Iso Bool Bool
isoNeg = MkIso neg neg p p 
  where p = (\x => case x of
                     False => Refl
                     True  => Refl)

-- Now, from this isomorphisms we have two different proofs of the
-- equality of Bool and Bool
bool_eq1 : Bool = Bool
bool_eq1 = univalence_ax isoId

bool_eq2 : Bool = Bool
bool_eq2 = univalence_ax isoNeg


-- Now, we apply uip, resulting in the fact that the former proofs
-- are equal:
theorem_eq1eqeq2 : HoTT.bool_eq1 = HoTT.bool_eq2
theorem_eq1eqeq2 = uip Bool Bool bool_eq1 bool_eq2
