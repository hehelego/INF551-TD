{-
-- Credit: https://ncatlab.org/nlab/show/W-type
--
-- type [W A B]
-- A is the type of tree node labels
-- B is the type of tree label arity
--
-- A term of type [W A B] is a rooted tree with some subtree
-- If the root is [root : A], the subtree is a family of [W A B] indexed by [B root].
--
-- **Remark** If a tree node [z] is a leaf, then [B z] should be a type of zero inhabitant.
--
-- Induction rule over [W A B]:
-- + A general way to deduce [P (tree a f)] for every root [a] with subtrees [f]
--   under the inductive hypothesis that [P (sub x)] holds for every [x : B a].
-- + (contained in the previous item) [P z] for every leaf node [z].
-}

data W (A : Set) (B : A → Set) : Set where
  tree : (root : A) (sub : B root → W A B) → W A B

elim : {A : Set} {B : A → Set} (P : W A B → Set)
     → (h : (root : A) (sub : B root → W A B) (IH : (x : B root) → P (sub x)) → P (tree root sub))
     → (w : W A B)
     → P w
elim P h (tree root sub) = h root sub (λ x → elim P h (sub x))

-- empty
data 𝟘 : Set where

-- singleton
-- defined as a record because the eta-expansion definitional equality is needed
record 𝟙 : Set where
  constructor *

-- binary/boolean
data 𝟚 : Set where
  0₂ : 𝟚
  1₂ : 𝟚

-- either one predecessor or none
arity01 : 𝟚 → Set
arity01 0₂ = 𝟘
arity01 1₂ = 𝟙

-- defining the natural number type as a W-type
Nat : Set
Nat = W 𝟚 arity01

zero : Nat
zero = tree 0₂ λ ()

suc : Nat → Nat
suc n = tree 1₂ (λ * → n)

-- the [base] takes a parameter of type [𝟘 → Nat] this is because
-- we cannot prove that all elements of type [𝟘 → Nat] are equal.
Ind : (P : Nat → Set)
    → (base : (empty : 𝟘 → Nat) → P (tree 0₂ empty))
    → (step : (n : Nat) (IH : P n) → P (suc n))
    → (n : Nat)
    → P n
Ind P base step (tree 0₂ empty) = base empty
Ind P base step (tree 1₂ sub) = let n  = sub *
                                    IH = Ind P base step n
                                 in step n IH
