-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

dec< : (m n : Nat) → m < n ∨ n ≤ m
dec< zero zero = right z≤n
dec< zero (suc n) = left z<s
dec< (suc m) zero = right z≤n
dec< (suc m) (suc n) with dec< m n
... | left  m<n = left  (s<s m<n)
... | right n≤m = right (s≤s n≤m)


data Prog : Set where
  -- boolean literal
  𝕓 : Bool → Prog
  -- natural number literal
  𝕟 : Nat → Prog
  -- sum of two natural numbers
  _+ₑ_ : Prog → Prog → Prog
  -- test to see if the a number is less than another number
  _<ₑ_ : Prog → Prog → Prog
  -- branching program
  if_then_else_ : Prog → Prog → Prog → Prog
  -- pair of two expression
  ⟨_,_⟩ : Prog → Prog → Prog
  -- unitary value
  𝕠 : Prog

data Value : Prog → Set where
  boolV : {b : Bool} → Value (𝕓 b)
  natV : {n : Nat} → Value (𝕟 n)
  pairV : {p q : Prog} → Value p → Value q → Value ⟨ p , q ⟩
  unitV : Value 𝕠

-- TODO: this reduction relation is non-deterministic, can we show that it is confluent?
infixr 5 _⇒_
data _⇒_ : Prog → Prog → Set where
  -- compute the result of a sum
  +-natval : {m n : Nat} → 𝕟 m +ₑ 𝕟 n ⇒ 𝕟 (m + n)
  -- reduce one operand of a summation
  +-left  : {p p' q : Prog} → p ⇒ p' → p +ₑ q ⇒ p' +ₑ q
  +-right : {p q q' : Prog} → q ⇒ q' → p +ₑ q ⇒ p +ₑ q'
  -- compute the result of a comparison
  <-true  : {m n : Nat} → m < n → 𝕟 m <ₑ 𝕟 n ⇒ 𝕓 true
  <-false : {m n : Nat} → n ≤ m → 𝕟 m <ₑ 𝕟 n ⇒ 𝕓 false
  -- reduce one operand of a comparison 
  <-left  : {p p' q : Prog} → p ⇒ p' → p <ₑ q ⇒ p' <ₑ q
  <-right : {p q q' : Prog} → q ⇒ q' → p <ₑ q ⇒ p <ₑ q'
  -- take one branch of a if-then-else expression
  if-true  : {p q : Prog} → if 𝕓 true  then p else q ⇒ p
  if-false : {p q : Prog} → if 𝕓 false then p else q ⇒ q
  -- reduce the branching condition of a if-then-else expression
  if-cond : {c c' p q : Prog} → c ⇒ c' → if c then p else q ⇒ if c' then p else q
  -- reduce one component of a pair
  pair-left  : {p p' q : Prog} → p ⇒ p' → ⟨ p , q ⟩ ⇒ ⟨ p' , q ⟩
  pair-right : {p q q' : Prog} → q ⇒ q' → ⟨ p , q ⟩ ⇒ ⟨ p , q' ⟩

data Type : Set where
  𝔹 : Type
  ℕ : Type
  ⟪_,_⟫ : Type → Type → Type
  𝟙 : Type

data ⊢_∷_ : Prog → Type → Set where
  -- type of atomic values
  ⊢ℕ : {n : Nat}  → ⊢ 𝕟 n ∷ ℕ
  ⊢𝔹 : {b : Bool} → ⊢ 𝕓 b ∷ 𝔹
  -- type of compositional expressions : build from types of sub-expressions
  ⊢+ : {p q : Prog} → ⊢ p ∷ ℕ → ⊢ q ∷ ℕ → ⊢ p +ₑ q ∷ ℕ
  ⊢< : {p q : Prog} → ⊢ p ∷ ℕ → ⊢ q ∷ ℕ → ⊢ p <ₑ q ∷ 𝔹
  -- branching condition must be boolean and the two branches have the identical type
  ⊢if : {c p q : Prog} {A : Type} → ⊢ c ∷ 𝔹 → ⊢ p ∷ A → ⊢ q ∷ A → ⊢ if c then p else q ∷ A
  -- pair type
  |-pair : {p q : Prog} {A B : Type} → ⊢ p ∷ A → ⊢ q ∷ B → ⊢ ⟨ p , q ⟩ ∷ ⟪ A , B ⟫
  -- unit type
  |-𝟙 : ⊢ 𝕠 ∷ 𝟙

preserve : {A : Type} {p q : Prog} → ⊢ p ∷ A → p ⇒ q → ⊢ q ∷ A
preserve {ℕ} ⊢p:N +-natval = ⊢ℕ
preserve {ℕ} (⊢+ ⊢p:N ⊢q:N) (+-left  p⇒p') = let ⊢p':N = preserve ⊢p:N p⇒p' in ⊢+ ⊢p':N ⊢q:N
preserve {ℕ} (⊢+ ⊢p:N ⊢q:N) (+-right q⇒q') = let ⊢q':N = preserve ⊢q:N q⇒q' in ⊢+ ⊢p:N  ⊢q':N
preserve (⊢< ⊢m:N ⊢n:N) (<-true  m<n) = ⊢𝔹
preserve (⊢< ⊢m:N ⊢n:N) (<-false n≤m) = ⊢𝔹
preserve (⊢< ⊢p:N ⊢q:N) (<-left  p⇒p') = let ⊢p':N = preserve ⊢p:N p⇒p' in ⊢< ⊢p':N ⊢q:N
preserve (⊢< ⊢p:N ⊢q:N) (<-right q⇒q') = let ⊢q':N = preserve ⊢q:N q⇒q' in ⊢< ⊢p:N  ⊢q':N
preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) if-true  = ⊢p:A
preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) if-false = ⊢q:A
preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) (if-cond c⇒c') = let ⊢c':B = preserve ⊢c:B c⇒c' in ⊢if ⊢c':B ⊢p:A ⊢q:A
preserve (|-pair ⊢p:A ⊢q:B) (pair-left  p⇒p') = let ⊢p':A = preserve ⊢p:A p⇒p' in |-pair ⊢p':A ⊢q:B
preserve (|-pair ⊢p:A ⊢q:B) (pair-right q⇒q') = let ⊢q':B = preserve ⊢q:B q⇒q' in |-pair ⊢p:A  ⊢q':B
preserve {𝟙} {𝕠} ⊢𝟙 ()

progress : {A : Type} {p : Prog} → ⊢ p ∷ A → Σ Prog (λ q → p ⇒ q) ∨ Value p
progress ⊢ℕ = right natV
progress ⊢𝔹 = right boolV
progress {ℕ} {p +ₑ q} (⊢+ ⊢p:N ⊢q:N) 
  with progress ⊢p:N
... | left (p' , p⇒p') = left (p' +ₑ q , +-left  p⇒p')
... | right (natV {m})
  with progress ⊢q:N
... | left (q' , q⇒q') = left (p +ₑ q' , +-right q⇒q')
... | right (natV {n}) = left (𝕟 (m + n) , +-natval)
progress {𝔹} {p <ₑ q} (⊢< ⊢p:N ⊢q:N)
  with progress ⊢p:N
... | left (p' , p⇒p') = left (p' <ₑ q , <-left  p⇒p')
... | right (natV {m})
  with progress ⊢q:N
... | left (q' , q⇒q') = left (p <ₑ q' , <-right q⇒q')
... | right (natV {n})
  with dec< m n
... | left  m<n = left (𝕓 true  , <-true  m<n)
... | right n≤m = left (𝕓 false , <-false n≤m)
progress {A} {if c then p else q} (⊢if ⊢c:B ⊢p:A ⊢q:A) 
  with progress ⊢c:B
... | left (c' , c⇒c') = left (if c' then p else q , if-cond c⇒c')
... | right (boolV {true} ) = left (p , if-true )
... | right (boolV {false}) = left (q , if-false)
progress {⟪ A , B ⟫} {⟨ p , q ⟩} (|-pair ⊢p:A ⊢q:B)
  with progress ⊢p:A
... | left (p' , p⇒p') = left (⟨ p' , q ⟩ , pair-left   p⇒p')
... | right vp
  with progress ⊢q:B
... | left (q' , q⇒q') = left (⟨ p , q' ⟩ , pair-right  q⇒q')
... | right vq = right (pairV vp vq)
progress {𝟙} {𝕠} |-𝟙 = right unitV
