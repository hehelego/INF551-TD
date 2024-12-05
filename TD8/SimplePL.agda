-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality

data Trichotomy : Nat → Nat → Set where
  tri-= : {m n : Nat} → m ≡ n → Trichotomy m n
  tri-< : {m n : Nat} → m < n → Trichotomy m n
  tri-> : {m n : Nat} → n < m → Trichotomy m n

trichotomy : (m n : Nat) → Trichotomy m n
trichotomy zero zero = tri-= refl
trichotomy zero (suc n) = tri-< z<s
trichotomy (suc m) zero = tri-> z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | tri-= m=n = tri-= (cong suc m=n)
... | tri-< m<n = tri-< (s<s m<n)
... | tri-> m>n = tri-> (s<s m>n)

dec< : (m n : Nat) → m < n ∨ n ≤ m
dec< zero zero = right z≤n
dec< zero (suc n) = left z<s
dec< (suc m) zero = right z≤n
dec< (suc m) (suc n) with dec< m n
... | left  m<n = left  (s<s m<n)
... | right n≤m = right (s≤s n≤m)

data Type : Set
data Ctx : Set
data Lookup : Ctx → Nat → Type → Set
data Prog : Set
data _⊢_∷_ : Ctx → Prog → Type → Set
data Value : Prog → Set
data _↦_ : Prog → Prog → Set

infixr 20 _⇒_
data Type where
  𝟙 : Type
  𝔹 : Type
  ℕ : Type
  ⟪_,_⟫ : Type → Type → Type
  _⇒_ : Type → Type → Type

infixl 15 _//_
data Ctx where
  ∅ : Ctx
  _//_ : Ctx → Type → Ctx

data Lookup where
  at-head : {Γ : Ctx} {A : Type} → Lookup (Γ // A) zero A
  in-tail : {Γ : Ctx} {n : Nat} {A B : Type} → Lookup Γ n A → Lookup (Γ // B) (suc n) A

infixr 10 _·_
infix 10 ⟨_,_⟩
data Prog where
  -- boolean literal
  bool : Bool → Prog
  -- natural number literal
  nat : Nat → Prog
  -- sum of two natural numbers
  _+ₑ_ : Prog → Prog → Prog
  -- test to see if the a number is less than another number
  _<ₑ_ : Prog → Prog → Prog
  -- branching program
  if_then_else_ : Prog → Prog → Prog → Prog
  -- pair of two expression
  ⟨_,_⟩ : Prog → Prog → Prog
  proj0 : Prog → Prog
  proj1 : Prog → Prog
  -- unitary value
  unit : Prog
  -- variable, function abstraction and application
  var : Nat → Prog
  abs : Prog → Prog
  _·_ : Prog → Prog → Prog

lift : Nat → Prog → Prog
lift n (bool x) = bool x
lift n (nat x) = nat x
lift n (p +ₑ q) = let p' = lift n p ; q' = lift n q in p' +ₑ q'
lift n (p <ₑ q) = let p' = lift n p ; q' = lift n q in p' <ₑ q'
lift n (if c then p else q) = let c' = lift n c
                                  p' = lift n p
                                  q' = lift n q
                               in if c' then p' else q'
lift n ⟨ p , q ⟩ = let p' = lift n p ; q' = lift n q in ⟨ p' , q' ⟩
lift n (proj0 p) = let p' = lift n p in proj0 p'
lift n (proj1 p) = let p' = lift n p in proj1 p'
lift n unit = unit
lift n (var x) with dec< x n
... | left  x<n = var x
... | right n≤x = var (suc x)
lift n (abs p) = let p' = lift (suc n) p in abs p'
lift n (p · q) = let p' = lift n p ; q' = lift n q in p' · q'


subs : Prog → Nat → Prog → Prog
subs (bool x) n r = bool x
subs (nat x) n r = nat x
subs (p +ₑ q) n r = let p' = subs p n r ; q' = subs q n r in p' +ₑ q'
subs (p <ₑ q) n r = let p' = subs p n r ; q' = subs q n r in p' <ₑ q'
subs (if c then p else q) n r = let c' = subs c n r
                                    p' = subs p n r
                                    q' = subs q n r
                                 in if c' then p' else q'
subs ⟨ p , q ⟩ n r = let p' = subs p n r ; q' = subs q n r in ⟨ p' , q' ⟩
subs (proj0 p) n r = let p' = subs p n r in proj0 p'
subs (proj1 p) n r = let p' = subs p n r in proj1 p'
subs unit n r = unit
subs (var x) n r with trichotomy x n
... | tri-= x=n = r
... | tri-< x<n = var x
... | tri-> x>n = var (pred x)
subs (abs p) n r = let n' = suc n
                       r' = lift 0 r
                    in abs (subs p n' r')
subs (p · q) n r = let p' = subs p n r ; q' = subs q n r in p' · q'


-- TODO: this reduction relation is non-deterministic, can we show that it is confluent?
infixr 5 _↦_
data _↦_ where
  -- compute the result of a sum
  +-natval : {m n : Nat} → nat m +ₑ nat n ↦ nat (m + n)
  -- reduce one operand of a summation
  +-left  : {p p' q : Prog} → p ↦ p' → p +ₑ q ↦ p' +ₑ q
  +-right : {p q q' : Prog} → q ↦ q' → p +ₑ q ↦ p +ₑ q'
  -- compute the result of a comparison
  <-true  : {m n : Nat} → m < n → nat m <ₑ nat n ↦ bool true
  <-false : {m n : Nat} → n ≤ m → nat m <ₑ nat n ↦ bool false
  -- reduce one operand of a comparison 
  <-left  : {p p' q : Prog} → p ↦ p' → p <ₑ q ↦ p' <ₑ q
  <-right : {p q q' : Prog} → q ↦ q' → p <ₑ q ↦ p <ₑ q'
  -- take one branch of a if-then-else expression
  if-true  : {p q : Prog} → if bool true  then p else q ↦ p
  if-false : {p q : Prog} → if bool false then p else q ↦ q
  -- reduce the branching condition of a if-then-else expression
  if-cond : {c c' p q : Prog} → c ↦ c' → if c then p else q ↦ if c' then p else q
  -- reduce one component of a pair
  pair-left  : {p p' q : Prog} → p ↦ p' → ⟨ p , q ⟩ ↦ ⟨ p' , q ⟩
  pair-right : {p q q' : Prog} → q ↦ q' → ⟨ p , q ⟩ ↦ ⟨ p , q' ⟩
  -- evaluate projection of a pair
  proj0-pair : {p p' : Prog} → p ↦ p' → proj0 p ↦ proj0 p'
  proj1-pair : {p p' : Prog} → p ↦ p' → proj1 p ↦ proj1 p'
  pair-fst : {p q : Prog} → proj0 ⟨ p , q ⟩ ↦ p
  pair-snd : {p q : Prog} → proj1 ⟨ p , q ⟩ ↦ q
  -- reduce a function call
  app-left  : {p p' q : Prog} → p ↦ p' → p · q ↦ p' · q
  app-right : {p q q' : Prog} → q ↦ q' → p · q ↦ p · q'
  app-beta : {p q : Prog} → (abs p) · q ↦ (subs p 0 q)


infix 10 _⊢_∷_
data _⊢_∷_ where
  -- type of atomic values
  ⊢ℕ : {Γ : Ctx} {n : Nat}  → Γ ⊢ nat n ∷ ℕ
  ⊢𝔹 : {Γ : Ctx} {b : Bool} → Γ ⊢ bool b ∷ 𝔹
  -- type of compositional expressions : build from types of sub-expressions
  ⊢+ : {Γ : Ctx} {p q : Prog} → Γ ⊢ p ∷ ℕ → Γ ⊢ q ∷ ℕ → Γ ⊢ p +ₑ q ∷ ℕ
  ⊢< : {Γ : Ctx} {p q : Prog} → Γ ⊢ p ∷ ℕ → Γ ⊢ q ∷ ℕ → Γ ⊢ p <ₑ q ∷ 𝔹
  -- branching condition must be boolean and the two branches have the identical type
  ⊢if : {Γ : Ctx} {c p q : Prog} {A : Type} → Γ ⊢ c ∷ 𝔹 → Γ ⊢ p ∷ A → Γ ⊢ q ∷ A → Γ ⊢ if c then p else q ∷ A
  -- pair type
  ⊢pair : {Γ : Ctx} {p q : Prog} {A B : Type} → Γ ⊢ p ∷ A → Γ ⊢ q ∷ B → Γ ⊢ ⟨ p , q ⟩ ∷ ⟪ A , B ⟫
  ⊢proj0 : {Γ : Ctx} {p : Prog} {A B : Type} → Γ ⊢ p ∷ ⟪ A , B ⟫ → Γ ⊢ proj0 p ∷ A
  ⊢proj1 : {Γ : Ctx} {p : Prog} {A B : Type} → Γ ⊢ p ∷ ⟪ A , B ⟫ → Γ ⊢ proj1 p ∷ B
  -- unit type
  ⊢𝟙 : {Γ : Ctx} → Γ ⊢ unit ∷ 𝟙
  -- functions
  ⊢ax : {Γ : Ctx} {i : Nat} {A : Type} → Lookup Γ i A → Γ ⊢ var i ∷ A
  ⊢app : {Γ : Ctx} {p q : Prog} {A B : Type} → Γ ⊢ p ∷ A ⇒ B → Γ ⊢ q ∷ A → Γ ⊢ p · q ∷ B
  ⊢abs : {Γ : Ctx} {p : Prog} {A B : Type} → Γ // A ⊢ p ∷ B → Γ ⊢ abs p ∷ A ⇒ B

data Value where
  unitV : Value unit
  boolV : {b : Bool} → Value (bool b)
  natV : {n : Nat} → Value (nat n)
  pairV : {p q : Prog} → Value p → Value q → Value ⟨ p , q ⟩
  lambdaV : {p : Prog} → Value (abs p)

-- subs-lift-lemma : {Γ : Ctx} {p q : Prog} {A B : Type} {n : Nat}
--                 → Γ ⊢ subs (abs p) n q ∷ A ⇒ B
--                 → Γ ⊢ abs (subs p (suc n) (lift 0 q)) ∷ A ⇒ B
-- subs-lift-lemma = ?


-- falsified :
-- A ⊢ var 0 ∷ A
-- A // B ⊢ var 0 ∷ B
-- weaken : {Γ : Ctx} {p : Prog} {A C : Type}
--        → Γ ⊢ p ∷ A
--        → Γ // C ⊢ p ∷ A

lift-lemma : {n : Nat} {Γ : Ctx} {p : Prog} {A C : Type}
           → Γ ⊢ p ∷ A
           → Γ // C ⊢ lift n p ∷ A
lift-lemma ⊢ℕ = ⊢ℕ
lift-lemma ⊢𝔹 = ⊢𝔹
lift-lemma (⊢+ ⊢p:N ⊢q:N) = let ⊢p:N' = lift-lemma ⊢p:N
                                ⊢q:N' = lift-lemma ⊢q:N
                             in ⊢+ ⊢p:N' ⊢q:N'
lift-lemma (⊢< ⊢p:N ⊢q:N) = {! !}
lift-lemma (⊢if ⊢p:B ⊢p:A ⊢q:A) = {! !}
lift-lemma (⊢pair ⊢p:A ⊢q:B) = {! !}
lift-lemma (⊢proj0 ⊢p:AB) = {! !}
lift-lemma (⊢proj1 ⊢p:AB) = {! !}
lift-lemma ⊢𝟙 = ⊢𝟙
lift-lemma {n} (⊢ax at-head) with dec< 0 n
... | left  x<n = ⊢ax {! !} -- was...
... | right n≤x = ?
lift-lemma (⊢ax (in-tail lookup)) = ?
lift-lemma (⊢app ⊢p:AB ⊢q:A) = {! !}
lift-lemma (⊢abs B⊢p:A) = ⊢abs {! !}

subs-lemma : {Γ : Ctx} {p q : Prog} {C A : Type}
           → Γ // C ⊢ p ∷ A
           → Γ ⊢ q ∷ C
           → Γ ⊢ subs p 0 q ∷ A
subs-lemma ⊢ℕ ⊢q:C = ⊢ℕ
subs-lemma ⊢𝔹 ⊢q:C = ⊢𝔹
subs-lemma (⊢+ C⊢p:N C⊢q:N) ⊢q:C = let ⊢p:N = subs-lemma C⊢p:N ⊢q:C 
                                       ⊢q:N = subs-lemma C⊢q:N ⊢q:C
                                    in ⊢+ ⊢p:N ⊢q:N
subs-lemma (⊢< C⊢p:N C⊢q:N) ⊢q:C = let ⊢p:N = subs-lemma C⊢p:N ⊢q:C 
                                       ⊢q:N = subs-lemma C⊢q:N ⊢q:C
                                    in ⊢< ⊢p:N ⊢q:N
subs-lemma (⊢if C⊢c:B C⊢p:A C⊢q:A) ⊢q:C = let ⊢c:B = subs-lemma C⊢c:B ⊢q:C 
                                              ⊢p:A = subs-lemma C⊢p:A ⊢q:C
                                              ⊢q:A = subs-lemma C⊢q:A ⊢q:C
                                           in ⊢if ⊢c:B ⊢p:A ⊢q:A
subs-lemma (⊢pair C⊢p:A C⊢q:B) ⊢q:C = let ⊢p:A = subs-lemma C⊢p:A ⊢q:C 
                                          ⊢q:B = subs-lemma C⊢q:B ⊢q:C
                                       in ⊢pair ⊢p:A ⊢q:B
subs-lemma (⊢proj0 C⊢p:AB) ⊢q:C = let ⊢p:AB = subs-lemma C⊢p:AB ⊢q:C in ⊢proj0 ⊢p:AB
subs-lemma (⊢proj1 C⊢p:AB) ⊢q:C = let ⊢p:AB = subs-lemma C⊢p:AB ⊢q:C in ⊢proj1 ⊢p:AB
subs-lemma ⊢𝟙 ⊢q:C = ⊢𝟙
subs-lemma (⊢ax at-head) ⊢q:C = ⊢q:C
subs-lemma (⊢ax (in-tail lookup)) ⊢q:C = ⊢ax lookup
subs-lemma (⊢app C⊢p:A⇒B C⊢q:A) ⊢q:C = let ⊢p:A⇒B = subs-lemma C⊢p:A⇒B ⊢q:C 
                                           ⊢q:A   = subs-lemma C⊢q:A   ⊢q:C
                                        in ⊢app ⊢p:A⇒B ⊢q:A
subs-lemma {Γ} {abs p} {q} {C} {A ⇒ B} (⊢abs C⊢p:A) ⊢q:C = g0
  where
        g1 : Γ // A ⊢ subs p 1 (lift 0 q) ∷ B
        g1 = {! !}
        g0 : Γ ⊢ abs (subs p 1 (lift 0 q)) ∷ A ⇒ B
        g0 = ⊢abs g1


-- A B C : Type
-- C⊢p:A : Γ // C // A ⊢ p ∷ B
-- p q : Prog
-- Γ : Ctx
-- ⊢q:C : Γ ⊢ q ∷ C
-- ----------------------------------
-- Goal: Γ ⊢ subs (abs p) 0 q ∷ A ⇒ B

preservation : {Γ : Ctx} {A : Type} {p q : Prog}
             → Γ ⊢ p ∷ A
             → p ↦ q
             → Γ ⊢ q ∷ A
-- add
preservation (⊢+ ⊢p:N ⊢q:N) +-natval = ⊢ℕ
preservation (⊢+ ⊢p:N ⊢q:N) (+-left  p↦p') = let ⊢p':N = preservation ⊢p:N p↦p' in ⊢+ ⊢p':N ⊢q:N
preservation (⊢+ ⊢p:N ⊢q:N) (+-right q↦q') = let ⊢q':N = preservation ⊢q:N q↦q' in ⊢+ ⊢p:N  ⊢q':N
-- compare
preservation (⊢< ⊢p:N ⊢q:N) (<-true x) = ⊢𝔹
preservation (⊢< ⊢p:N ⊢q:N) (<-false x) = ⊢𝔹
preservation (⊢< ⊢p:N ⊢q:N) (<-left  p↦p') = let ⊢p':N = preservation ⊢p:N p↦p' in ⊢< ⊢p':N ⊢q:N
preservation (⊢< ⊢p:N ⊢q:N) (<-right q↦q') = let ⊢q':N = preservation ⊢q:N q↦q' in ⊢< ⊢p:N  ⊢q':N
-- if branching
preservation (⊢if ⊢c:B ⊢p:A ⊢q:A) if-true  = ⊢p:A
preservation (⊢if ⊢c:B ⊢p:A ⊢q:A) if-false = ⊢q:A
preservation (⊢if ⊢c:B ⊢p:A ⊢q:A) (if-cond c↦c') = let ⊢c':B = preservation ⊢c:B c↦c' in ⊢if ⊢c':B ⊢p:A ⊢q:A
-- pair
preservation (⊢pair ⊢p:A ⊢q:B) (pair-left  p↦p') = let ⊢p':A = preservation ⊢p:A p↦p' in ⊢pair ⊢p':A ⊢q:B
preservation (⊢pair ⊢p:A ⊢q:B) (pair-right q↦q') = let ⊢q':B = preservation ⊢q:B q↦q' in ⊢pair ⊢p:A  ⊢q':B
preservation (⊢proj0 ⊢p:AB) (proj0-pair p↦p') = let ⊢p':AB = preservation ⊢p:AB p↦p' in ⊢proj0 ⊢p':AB
preservation (⊢proj0 (⊢pair ⊢p:A ⊢q:B)) pair-fst = ⊢p:A
preservation (⊢proj1 ⊢p:AB) (proj1-pair p↦p') = let ⊢p':AB = preservation ⊢p:AB p↦p' in ⊢proj1 ⊢p':AB
preservation (⊢proj1 (⊢pair ⊢p:A ⊢q:B)) pair-snd = ⊢q:B
-- function
preservation (⊢app ⊢p:A⇒B ⊢q:A) (app-left  p↦p') = let ⊢p':A⇒B = preservation ⊢p:A⇒B p↦p' in ⊢app ⊢p':A⇒B ⊢q:A
preservation (⊢app ⊢p:A⇒B ⊢q:A) (app-right q↦q') = let ⊢q':A   = preservation ⊢q:A   q↦q' in ⊢app ⊢p:A⇒B  ⊢q':A
preservation (⊢app (⊢abs A⊢p:B) ⊢q:A) app-beta = subs-lemma A⊢p:B ⊢q:A

-- preserve : {A : Type} {p q : Prog} → ⊢ p ∷ A → p ↦ q → ⊢ q ∷ A
-- preserve {ℕ} ⊢p:N +-natval = ⊢ℕ
-- preserve {ℕ} (⊢+ ⊢p:N ⊢q:N) (+-left  p↦p') = let ⊢p':N = preserve ⊢p:N p↦p' in ⊢+ ⊢p':N ⊢q:N
-- preserve {ℕ} (⊢+ ⊢p:N ⊢q:N) (+-right q↦q') = let ⊢q':N = preserve ⊢q:N q↦q' in ⊢+ ⊢p:N  ⊢q':N
-- preserve (⊢< ⊢m:N ⊢n:N) (<-true  m<n) = ⊢𝔹
-- preserve (⊢< ⊢m:N ⊢n:N) (<-false n≤m) = ⊢𝔹
-- preserve (⊢< ⊢p:N ⊢q:N) (<-left  p↦p') = let ⊢p':N = preserve ⊢p:N p↦p' in ⊢< ⊢p':N ⊢q:N
-- preserve (⊢< ⊢p:N ⊢q:N) (<-right q↦q') = let ⊢q':N = preserve ⊢q:N q↦q' in ⊢< ⊢p:N  ⊢q':N
-- preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) if-true  = ⊢p:A
-- preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) if-false = ⊢q:A
-- preserve (⊢if ⊢c:B ⊢p:A ⊢q:A) (if-cond c↦c') = let ⊢c':B = preserve ⊢c:B c↦c' in ⊢if ⊢c':B ⊢p:A ⊢q:A
-- preserve (⊢pair ⊢p:A ⊢q:B) (pair-left  p↦p') = let ⊢p':A = preserve ⊢p:A p↦p' in ⊢pair ⊢p':A ⊢q:B
-- preserve (⊢pair ⊢p:A ⊢q:B) (pair-right q↦q') = let ⊢q':B = preserve ⊢q:B q↦q' in ⊢pair ⊢p:A  ⊢q':B
-- preserve {𝟙} {unit} ⊢𝟙 ()
--
-- progress : {A : Type} {p : Prog} → ⊢ p ∷ A → Σ Prog (λ q → p ↦ q) ∨ Value p
-- progress ⊢ℕ = right natV
-- progress ⊢𝔹 = right boolV
-- progress {ℕ} {p +ₑ q} (⊢+ ⊢p:N ⊢q:N) 
--   with progress ⊢p:N
-- ... | left (p' , p↦p') = left (p' +ₑ q , +-left  p↦p')
-- ... | right (natV {m})
--   with progress ⊢q:N
-- ... | left (q' , q↦q') = left (p +ₑ q' , +-right q↦q')
-- ... | right (natV {n}) = left (nat (m + n) , +-natval)
-- progress {𝔹} {p <ₑ q} (⊢< ⊢p:N ⊢q:N)
--   with progress ⊢p:N
-- ... | left (p' , p↦p') = left (p' <ₑ q , <-left  p↦p')
-- ... | right (natV {m})
--   with progress ⊢q:N
-- ... | left (q' , q↦q') = left (p <ₑ q' , <-right q↦q')
-- ... | right (natV {n})
--   with dec< m n
-- ... | left  m<n = left (bool true  , <-true  m<n)
-- ... | right n≤m = left (bool false , <-false n≤m)
-- progress {A} {if c then p else q} (⊢if ⊢c:B ⊢p:A ⊢q:A) 
--   with progress ⊢c:B
-- ... | left (c' , c↦c') = left (if c' then p else q , if-cond c↦c')
-- ... | right (boolV {true} ) = left (p , if-true )
-- ... | right (boolV {false}) = left (q , if-false)
-- progress {⟪ A , B ⟫} {⟨ p , q ⟩} (⊢pair ⊢p:A ⊢q:B)
--   with progress ⊢p:A
-- ... | left (p' , p↦p') = left (⟨ p' , q ⟩ , pair-left   p↦p')
-- ... | right vp
--   with progress ⊢q:B
-- ... | left (q' , q↦q') = left (⟨ p , q' ⟩ , pair-right  q↦q')
-- ... | right vq = right (pairV vp vq)
-- progress {𝟙} {unit} ⊢𝟙 = right unitV
