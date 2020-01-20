import Data.List

infix 5 .=.
data Field : lty -> Type -> Type where
  (.=.) : (l : lty) -> t -> Field l t

infixr 3 :<
data HList : List (lty, Type) -> Type where
   EmptyList : HList []
   (:<) : Field l t -> HList xs -> HList ((l,t) :: xs)


labelsOf : List (lty, Type) -> List lty
labelsOf = map fst


data IsSet : List t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)

data Record : List (lty, Type) -> Type where
  MkRecord : IsSet (labelsOf ts) -> HList ts -> Record ts
