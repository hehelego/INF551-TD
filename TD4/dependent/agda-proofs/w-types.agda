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
data 𝟙 : Set where
  * : 𝟙

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

-- an example of using the [Nat] type defined by W.
add : Nat → Nat → Nat
add = elim (λ _ → Nat → Nat) λ { 0₂ sub IH → (λ x → x)
                               ; 1₂ sub IH → (λ x → suc (IH * x)) }


data nat-equality : Nat → Nat → Set where
  reflexivity : (n : Nat) → nat-equality n n

w0 = zero
w1 = suc w0
w2 = suc w1
w3 = suc w2
w4 = suc w3
w5 = suc w4

add00 = reflexivity w0
add01 = reflexivity w1
add02 = reflexivity w2
add03 = reflexivity w3
add04 = reflexivity w4
add05 = reflexivity w5
add10 = reflexivity w1
add11 = reflexivity w2
add12 = reflexivity w3
add13 = reflexivity w4
add14 = reflexivity w5
add20 = reflexivity w2
add21 = reflexivity w3
add22 = reflexivity w4
add23 = reflexivity w5
add30 = reflexivity w3
add31 = reflexivity w4
add32 = reflexivity w5
add40 = reflexivity w4
add41 = reflexivity w5
add50 = reflexivity w5
