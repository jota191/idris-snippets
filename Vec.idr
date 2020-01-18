module Vec

infixr 4 :::
data Vec : Nat -> Type -> Type where
  VNil : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a  

-- examples
v3 : Vec 3 Nat
v3 = 3 :: 4 :: 5 :: VNil

v7 : Vec 7 Nat
v7 = 1 :: 3 :: 6 :: 7 :: v3


-- detructors

-- safe head
vHead : Vec (S n) a -> a
vHead (x :: xs) = x

-- safe tail
vTail : Vec (S n) a -> Vec n a
vTail (x :: xs) = xs

-- tail for all vector, returning the empty vector in the empty case
univTail : Vec n a -> Vec (pred n) a
univTail VNil = VNil
univTail (x :: xs) = xs

-- append
(++) : Vec n a -> Vec m a -> Vec (n + m) a
(++) VNil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

t_succEqPlus1 : {n : Nat} -> S n = n + 1
t_succEqPlus1 {n = Z}   = Refl
t_succEqPlus1 {n = S k} = rewrite t_succEqPlus1 {n = k}
                          in Refl



-- reverse (not efficient, but an exercise to convince 
--  the compiler that [plus n 1 = S n])
rev : Vec n a -> Vec n a
rev {n = Z} VNil = VNil
rev {n = S k} (x :: xs) = rewrite t_succEqPlus1 {n = k} 
                          in xs ++ (x :: VNil) 


-- finite sets
data Fin : nat -> Type where
  FZ : Fin (S n)
  FS : Fin n -> Fin (S n)

-- get by index

getN : {n : Nat} -> Fin n -> Vec n a -> a
getN {n = Z} _ _ impossible
getN {n = (S k)}  FZ    (x :: xs) = x
getN {n = (S k)} (FS i) (_ :: xs) = getN {n = k} (the (Fin k) i) xs

-- filter, using dependent product
filter : Vec n a -> (a -> Bool) -> (m : Nat ** Vec m a)
filter VNil p      = (0 ** VNil)
filter (x :: xs) p = let (k ** vec) = filter xs p
                     in if p x
                     then (S k ** x :: vec)
                     else (k ** vec)

--to test:
even : Nat -> Bool
even Z     = True
even (S n) = not $ even n
-- filter v7 even ---->
-- (2 ** 6 :: 4 :: VNil) : (m : Nat ** Vec m Nat)

-- drop, I was going to use fin, this is the stdlib interface..
drop : (n : Nat) -> Vec (n + m) a -> Vec m a
drop Z xs            = xs
drop (S k) (x :: xs) = drop k xs


-- some theorems
t_constail : vTail ((x :: VNil) ++ xs) = xs
t_constail = Refl

t_appDrop : (v : Vec n a) -> (w : Vec m a) -> w = drop n (v ++ w) 
t_appDrop { n  =  Z }     VNil _ = Refl
t_appDrop { n  =  (S k) } (x :: xs) w 
  = rewrite t_appDrop {n = k} xs w in Refl
