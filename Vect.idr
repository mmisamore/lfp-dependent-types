module Vect

import Data.String
import Decidable.Equality

-- All functions are total by default
%default total

-- Vectors with known lengths
data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

-- Show a vector of known length
Show a => Show (Vect n a) where
  show Nil = "[]"
  show xs = "[" ++ showHelper xs ++ "]" where
    showHelper : Show a => Vect n a -> String
    showHelper []  = "" 
    showHelper [x] = show x
    showHelper (x :: y) = show x ++ ", " ++ showHelper y 

-- Append two vectors and record new length in the type
appendVect : Vect n a -> Vect m a -> Vect (n + m) a
appendVect [] y = y 
appendVect (x :: z) y = x :: appendVect z y

-- Return the length of a vector. Here "n" is implicit argument
lengthVect : Vect n a -> Nat
lengthVect {n} x = n 

-- Zip two vectors. Note we don't have to truncate because we know they 
-- have same lengths at the type level.
zipVect : Vect n a -> Vect n b -> Vect n (a,b)
zipVect [] [] = []
zipVect (x :: z) (y :: w) = (x,y) :: zipVect z w 
-- Show that zipWith [1,2,3,4] [1,2,3] is a type error

-- Take first k elements from a vector of known length
vectTake : (k : Nat) -> Vect (k + l) a -> Vect k a 
vectTake Z _ = Nil 
vectTake (S k) (x :: xs) = x :: vectTake k xs 
-- vectTake 4 [1,2,3] is a type error
-- return type depends on input "k" and is guaranteed to have k elements

-- Inductive proofs of natural number inequalities 
infixr 10 :<=:
data (:<=:) : Nat -> Nat -> Type where
  ZeroLessThanEqual : (Z :<=: n)
  IndLessThanEqual  : (n :<=: m) -> (S n :<=: S m)
-- the (0 :<=: 2) ZeroLessThanEqual is okay
-- the (1 :<=: 2) ZeroLessThanEqual is type error (good)
-- IndLessThanEqual (the (0 :<=: 2) ZeroLessThanEqual) is 1 :<=: 3 (good)

-- Given a *proof* that k is less than or equal to n, take first k elements from a vector of length n
betterTake : (k : Nat) -> Vect n a -> {auto pf: (k :<=: n)} -> Vect k a
betterTake Z _ = [] 
betterTake (S k) [] impossible 
betterTake (S k) (x :: xs) {pf = IndLessThanEqual ip} = x :: betterTake k xs {pf = ip}
-- We can statically infer the proofs with "auto"!
-- Here's what it looks like to do it manually:
-- betterTake 2 [1,2,3,4,5] {pf = IndLessThanEqual $ IndLessThanEqual $ ZeroLessThanEqual }

-- What about proving stuff at runtime? We can do that too!
-- k :<=: n is decidable. This means we either have a proof that k :<=: n or a proof that this is not the case.
-- Important: the below function is total, so it gives a proof either way.
decideLessThanEqual : (k : Nat) -> (n : Nat) -> Dec (k :<=: n)
decideLessThanEqual Z n = Yes ZeroLessThanEqual 
decideLessThanEqual (S k) Z = 
  No succNotLessThan where
    -- Impossible for a successor to be less than or equal to 0
    succNotLessThan : ((S k) :<=: 0) -> Void
    succNotLessThan ZeroLessThanEqual impossible
    succNotLessThan (IndLessThanEqual _) impossible
decideLessThanEqual (S k) (S j) = 
  case decideLessThanEqual k j of
    Yes pf => Yes (IndLessThanEqual pf)
    No contra => No (contra . predLessThan) 
  where
      -- Taking predecessors preserves ordering
      predLessThan : (S n :<=: S m) -> (n :<=: m)
      predLessThan (IndLessThanEqual pf) = pf 

-- Now we can decide if we can take k elements from an n-element vector at runtime. This property is decidable at
-- runtime and the typechecker statically enforces that we have a proof either way. 
vectTakeK : IO ()
vectTakeK = do
             s <- getLine
             let k    = cast s 
             let vect = the (Vect 5 Int) [1,2,3,4,5]
             case decideLessThanEqual k (lengthVect vect) of
                  Yes pf => printLn (betterTake k vect)
                  No contra => printLn "k wasn't less than or equal to 5"
-- :exec vectTakeK is a program that takes user input of k and returns first k elements of fixed-length vector,
-- if possible, with a statically enforced boundary check. Observe that vectTakeK is total: it provably cannot crash!


-- Let's reverse a vector and prove that the reverse has the same length as the initial vector
-- Note that we haven't proven that we actually reversed the vector, and the initial version of this function had a bug
-- where it didn't!
reverseVect : Vect n a -> Vect n a
reverseVect []       = [] 
reverseVect (x :: y) = rewrite (succIsPlusOne (lengthVect y)) in appendVect (reverseVect y) [x] 
  where
    -- Prove that the successor of n is the same as n + 1
    succIsPlusOne : (n : Nat) -> (S n = plus n 1)
    succIsPlusOne Z     = Refl 
    succIsPlusOne (S k) = cong (succIsPlusOne k) 


-- A type for proofs of vector equalities
data VectsAreEqual : Vect n a -> Vect m a -> Type where
  EmptyVectEqual : VectsAreEqual Nil Nil 
  IndVectAreEqual : (n = m) -> (x = y) -> VectsAreEqual xs ys -> VectsAreEqual (x :: xs) (y :: ys)

-- Lemma: Vectors differ if the first two elements differ
firstEltsDiffer : (contra : (x = z) -> Void) -> VectsAreEqual (x :: y) (z :: w) -> Void
firstEltsDiffer contra (IndVectAreEqual _ firstEltPrf _) = contra firstEltPrf

-- Decide whether or not two vectors are equal at runtime assuming element equality is decidable. The output is a
-- *validated proof* explaining *why* they are equal or not, instead of just a Bool
decideVectorEq : DecEq a => (xs : Vect n a) -> (ys : Vect m a) -> Dec (VectsAreEqual xs ys) 
decideVectorEq [] []       = Yes EmptyVectEqual 
decideVectorEq [] (x :: y) = No emptyNotNonempty where
                              emptyNotNonempty : VectsAreEqual [] (x :: y) -> Void
                              emptyNotNonempty EmptyVectEqual impossible
                              emptyNotNonempty (IndVectAreEqual _ _ _) impossible
decideVectorEq (x :: y) [] = No nonEmptyIsNotEmpty where
                              nonEmptyIsNotEmpty : VectsAreEqual (x :: y) [] -> Void
                              nonEmptyIsNotEmpty EmptyVectEqual impossible
                              nonEmptyIsNotEmpty (IndVectAreEqual _ _ _) impossible
decideVectorEq (x :: y) (z :: w) 
                           = case decEq x z of
                               -- The first elements are provably equal, so check the remainder
                               Yes firstEltPrf => case decideVectorEq y w of
                                                       Yes prf   => ?tbd_1
                                                       No contra => ?tbd_2
                               -- The first elements are provably unequal, so the vectors are too
                               No contra => No (firstEltsDiffer contra) 


-- Decide if one vector is the reverse of another or not

