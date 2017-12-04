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

-- Type-safe head of a vector
head : Vect (S n) a -> a
head (x :: _) = x 

-- Type-safe tail of a vector
tail : Vect (S n) a -> Vect n a
tail (_ :: xs) = xs 

%hide last
-- Type-safe last element of a vector
last : Vect (S n) a -> a
last (x :: [])        = x
last (_ :: (y :: xs)) = last (y :: xs) 

%hide init
-- Type-safe non-empty initial segment of a vector
init : Vect (S n) a -> Vect n a
init (x :: [])        = [] 
init (x :: (y :: xs)) = x :: (init (y :: xs))  

-- Append two vectors and record new length in the type
appendVect : Vect n a -> Vect m a -> Vect (n + m) a
appendVect [] y = y 
appendVect (x :: z) y = x :: appendVect z y

-- Empty vector is left neutral
lemLeftAppendNil : (xs : Vect n a) -> appendVect [] xs = xs
lemLeftAppendNil xs = Refl

-- Empty vector is right neutral
lemRightAppendNil : (xs : Vect n a) -> appendVect xs [] = xs
lemRightAppendNil []       = Refl
lemRightAppendNil (x :: y) = rewrite lemRightAppendNil y in Refl 

-- Append is associative vectors with append are a monoid
lemAppendAssoc : (xs : Vect n a) -> (ys : Vect m a) -> (zs : Vect o a) 
              -> appendVect (appendVect xs ys) zs = appendVect xs (appendVect ys zs)
lemAppendAssoc [] ys zs = Refl
lemAppendAssoc xs [] zs = rewrite lemRightAppendNil xs in Refl
lemAppendAssoc xs ys [] = rewrite lemRightAppendNil ys in 
                          rewrite lemRightAppendNil (appendVect xs ys) in Refl 
lemAppendAssoc (x :: xs) (y :: ys) (z :: zs) = rewrite lemAppendAssoc xs (y :: ys) (z :: zs) in Refl 

-- Lemma: A non-empty vector can be decomposed into the append of a head to a tail
lemUnCons : (xs : Vect (S n) a) -> appendVect [head xs] (tail xs) = xs
lemUnCons (x :: xs) = Refl

-- Lemma: A non-empty vector can be decomposed into the append of an initial segment to the last elt
lemUnSnoc : (xs : Vect (S n) a) -> appendVect (init xs) [last xs] = xs
lemUnSnoc (x :: [])        = Refl
lemUnSnoc (x :: (y :: xs)) = rewrite lemUnSnoc (y :: xs) in Refl 

-- Return the length of a vector. Here "n" is implicit argument
lengthVect : Vect n a -> Nat
lengthVect {n} xs = n 

-- Zip two vectors. Note we don't have to truncate because we know they 
-- have same lengths at the type level.
zipVect : Vect n a -> Vect n b -> Vect n (a,b)
zipVect [] [] = []
zipVect (x :: z) (y :: w) = (x,y) :: zipVect z w 
-- Show that zipWith [1,2,3,4] [1,2,3] is a type error

-- Take first k elements from a vector of known length
vectTake : (k : Nat) -> Vect (k + l) a -> Vect k a 
vectTake Z _             = Nil 
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
decideLessThanEqual Z n     = Yes ZeroLessThanEqual 
decideLessThanEqual (S k) Z = No succNotLessThan where
                                -- Impossible for a successor to be less than or equal to 0
                                succNotLessThan : ((S k) :<=: 0) -> Void
                                succNotLessThan ZeroLessThanEqual impossible
                                succNotLessThan (IndLessThanEqual _) impossible
decideLessThanEqual (S k) (S j) 
                            = case decideLessThanEqual k j of
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

-- O(n^2) list reversal
reverse1 : List a -> List a 
reverse1 []        = [] 
reverse1 (x :: xs) = (reverse1 xs) ++ [x] 

-- Lemma: Reversing an append of Lists is the same as appending the reversed Lists in reverse
lemReverseAppend : (xs : List a) -> (ys : List a) -> reverse1 (xs ++ ys) = reverse1 ys ++ reverse1 xs
lemReverseAppend [] ys        = rewrite List.appendNilRightNeutral (reverse1 ys) in Refl
lemReverseAppend (x :: xs) ys = rewrite lemReverseAppend xs ys in
                                rewrite List.appendAssociative (reverse1 ys) (reverse1 xs) [x] in
                                Refl

-- Lemma: Reversing a List twice (with naive algo) is the identity
lemReverseInvolution : (xs : List a) -> reverse1 (reverse1 xs) = xs
lemReverseInvolution []        = Refl
lemReverseInvolution (x :: xs) = rewrite lemReverseAppend (reverse1 xs) [x] in 
                                 rewrite lemReverseInvolution xs in
                                 Refl 

-- Lemma: The successor of n is the same as n + 1
lemSuccIsPlusOne : (n : Nat) -> S n = plus n 1
lemSuccIsPlusOne Z     = Refl 
lemSuccIsPlusOne (S k) = cong (lemSuccIsPlusOne k) 

-- Lemma: Zero is right additive identity for naturals
lemPlusZero : (n : Nat) -> n + 0 = n
lemPlusZero Z     = Refl
lemPlusZero (S k) = cong (lemPlusZero k)

-- Lemma: Successor distributes over a sum on the right
lemSuccPlusRightSucc : (n : Nat) -> (m : Nat) -> S (n + m) = n + (S m)
lemSuccPlusRightSucc Z m     = Refl
lemSuccPlusRightSucc (S k) m = cong (lemSuccPlusRightSucc k m) 

-- Lemma: Addition of naturals is commutative
lemPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
lemPlusCommutes Z m     = rewrite lemPlusZero m in Refl
lemPlusCommutes (S k) m = rewrite lemPlusCommutes k m in
                          rewrite lemSuccPlusRightSucc m k in
                          Refl

-- Lemma: Succ on the left is the same as Succ on the right 
lemLeftSuccRightSucc : (n : Nat) -> (m : Nat) -> (S n) + m = n + (S m)
lemLeftSuccRightSucc Z m     = Refl
lemLeftSuccRightSucc (S k) m = cong (lemSuccPlusRightSucc k m)

-- O(n) vector reversal. Uses rewrite.
reverseVect : Vect n a -> Vect n a
reverseVect xs = go [] xs where 
  go : Vect n a -> Vect m a -> Vect (n + m) a 
  go {n} acc []                  = rewrite lemPlusZero n in acc
  go {n} {m = S m} acc (x :: xs) = rewrite sym (lemLeftSuccRightSucc n m) in go (x :: acc) xs

-- O(n^2) vector reversal. This is the mathematical definition.
reverseVect2 : Vect n a -> Vect n a
reverseVect2 [] = []
reverseVect2 {n = S k} (x :: xs) = rewrite lemSuccIsPlusOne k in appendVect (reverseVect2 xs) [x]

-- Type of snoc vectors
data SnocVect : Nat -> Type -> Type where
  SnocNil : SnocVect 0 a
  Snoc : SnocVect n a -> a -> SnocVect (S n) a

-- Every vector is a snoc vector
snocOfVect : Vect n a -> SnocVect n a
snocOfVect []          = SnocNil
snocOfVect v@(x :: xs) = Snoc (snocOfVect (init v)) (last v) 

-- Take the head of a snoc vector
snocHead : SnocVect (S n) a -> a
snocHead (Snoc SnocNil x)       = x 
snocHead (Snoc s@(Snoc xs y) x) = snocHead s 

-- Take the tail of a snoc vector
snocTail : SnocVect (S n) a -> SnocVect n a
snocTail (Snoc SnocNil x)       = SnocNil
snocTail (Snoc s@(Snoc xs y) x) = Snoc (snocTail s) x

-- Every snoc vector is a vector
vectOfSnoc : SnocVect n a -> Vect n a
vectOfSnoc SnocNil       = []
vectOfSnoc s@(Snoc xs x) = snocHead s :: vectOfSnoc (snocTail s)

-- Lemma: Head of a vector of a Snoc is the head
lemHeadVectOfSnoc : (xs : SnocVect (S n) a) -> head (vectOfSnoc xs) = snocHead xs 
lemHeadVectOfSnoc (Snoc xs x) = Refl

-- Lemma: Head of a Snoc of a vector is the head 
lemHeadSnocOfVect : (xs : Vect (S n) a) -> snocHead (snocOfVect xs) = head xs
lemHeadSnocOfVect (x :: xs) = lemHeadSnocOfVect_1 xs x
  where
    -- Lemma: Head of a snoc vector with non-empty initial segment is the head of the initial segment
    lemSnocHeadOfSnoc : (xs : SnocVect (S n) a) -> (x : a) -> snocHead (Snoc xs x) = snocHead xs 
    lemSnocHeadOfSnoc (Snoc xs y) x = Refl

    -- Lemma: Head of init of non-empty vector is just the head of the vector 
    lemHeadInitIsHead : (xs : Vect (S n) a) -> (x : a) -> head (init (x :: xs)) = x
    lemHeadInitIsHead (y :: ys) x = Refl

    -- Helper for Snoc over init/last 
    lemHeadSnocOfVect_1 : (xs : Vect n a) -> (x : a) -> snocHead (Snoc (snocOfVect (init (x :: xs))) (last (x :: xs))) = x
    lemHeadSnocOfVect_1 {n = Z} [] _     = Refl 
    lemHeadSnocOfVect_1 {n = (S k)} xs x = rewrite lemSnocHeadOfSnoc (snocOfVect (init (x :: xs))) (last (x :: xs)) in 
                                           rewrite lemHeadSnocOfVect (init (x :: xs)) in 
                                           rewrite lemHeadInitIsHead xs x in 
                                           Refl 

-- Lemma: vectOfSnoc of snocOfVect is identity on the head
lemVectSnocHeadId : (xs : Vect (S n) a) -> head (vectOfSnoc (snocOfVect xs)) = head xs
lemVectSnocHeadId xs = rewrite lemHeadVectOfSnoc (snocOfVect xs) in 
                       rewrite lemHeadSnocOfVect xs in 
                       Refl 

-- Lemma: Vector of snoc tail is the tail of the vector
lemTailVectOfSnoc : (xs : SnocVect (S n) a) -> vectOfSnoc (snocTail xs) = tail (vectOfSnoc xs)
lemTailVectOfSnoc (Snoc xs x) = Refl

-- Lemma: Tail of a snoc vector with non-empty initial segment is the tail of the initial segment with the last elt
lemSnocTailOfSnoc : (xs : SnocVect (S n) a) -> (x : a) -> snocTail (Snoc xs x) = Snoc (snocTail xs) x
lemSnocTailOfSnoc (Snoc ys y) x = Refl


-- snocTail (snocOfVect xs) = snocOfVect (tail xs)


-- Lemma: Every non-empty vector can be written as a cons
lemVectIsCons : (x : a) -> (y : a) -> (xs : Vect n a) -> (ys : Vect m a) -> (x = y) -> (xs = ys) -> (x :: xs = y :: ys) 
lemVectIsCons x y xs ys prf prf1 = rewrite prf in 
                                   rewrite prf1 in Refl

lem : (xs : Vect n a) -> (x : a) -> vectOfSnoc (snocTail (Snoc (snocOfVect (init (x :: xs))) (last (x :: xs)))) = xs
lem {n = Z} [] _ = Refl
lem {n = (S k)} xs x = rewrite lemSnocTailOfSnoc (snocOfVect (init (x :: xs))) (last (x :: xs)) in 
                       ?lem_rhs_2
 

-- Lemma: vectOfSnoc of snocOfVect is identity 
lemVectSnocId : (xs : Vect n a) -> vectOfSnoc (snocOfVect xs) = xs
lemVectSnocId {n = Z} []            = Refl
lemVectSnocId {n = (S k)} (x :: xs) = rewrite lemHeadSnocOfVect (x :: xs) in 
                                      let toReduce = vectOfSnoc (snocTail (Snoc (snocOfVect (init (x :: xs))) (last (x :: xs)))) in 
                                      rewrite lemVectIsCons x x toReduce xs Refl ?help2 in 
                                      Refl


-- Reverse a vector without using rewrite 
reverseVect3 : Vect n a -> Vect n a
reverseVect3 xs with (snocOfVect xs)
  reverseVect3 []        | SnocNil = []
  reverseVect3 (x :: xs) | Snoc ys y = y :: reverseVect3 (vectOfSnoc ys) 




-- Lemma: Vectors differ if they differ in length
vectDiffOnLength : (xs : Vect n a) -> (ys : Vect m a) -> ((n = m) -> Void) -> (xs = ys) -> Void
vectDiffOnLength ys ys c Refl = c Refl 

-- Lemma: Zero is never a successor
zeroNotSuccessor : (0 = S n) -> Void
zeroNotSuccessor Refl impossible

-- Lemma: Nonempty vectors differ if the tails differ
restDiffer : (y : Vect n a) -> (w : Vect m a) -> ((y = w) -> Void) -> (x :: y = z :: w) -> Void
restDiffer w w contra Refl = contra Refl 

-- Lemma: Nonempty vectors differ if the first elements differ
firstEltsDiffer : (y : Vect n a) -> (w : Vect m a) -> ((x = z) -> Void) -> (x :: y = z :: w) -> Void
firstEltsDiffer w w contra Refl = contra Refl 

-- Better decidable equality for Vectors
decEquality : DecEq a => (xs : Vect n a) -> (ys : Vect m a) -> Dec (xs = ys)
decEquality [] []       = Yes Refl 
decEquality [] (x :: y) = No (\refl => vectDiffOnLength [] (x::y) zeroNotSuccessor refl) 
decEquality (x :: y) [] = No (\refl => vectDiffOnLength [] (x::y) zeroNotSuccessor (sym refl)) 
decEquality (x :: y) (z :: w) = 
  case decEq x z of
    Yes Refl => case decEquality y w of
                  Yes Refl   => Yes Refl
                  No  contra => No (restDiffer y w contra)
    No contra => No (firstEltsDiffer y w contra)

