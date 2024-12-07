-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; pred ; _+_ ; _<_ ; _≤_ ; z<s ; z≤n ; s<s ; s≤s)
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; subst)

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

ctx-len : Ctx → Nat
ctx-len ∅ = zero
ctx-len (Γ // X) = suc (ctx-len Γ)

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
  -- fixed point recursion
  fix : Prog → Prog

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
lift n (fix p) = let p' = lift (suc n) p in fix p'

-- ∅ // T3 // T2 // T1 // T0 ⊢ x0 x1 x2 x3
-- lift0: x1 x2 x3 x4 (T' T0 T1 T2 T3)
-- lift1: x0 x2 x3 x4 (T0 T' T1 T2 T3)
-- lift2: x0 x1 x3 x4 (T0 T1 T' T2 T3)
-- lift3: x0 x1 x2 x4 (T0 T1 T2 T' T3)
-- lift4: x0 x1 x2 x3 (T0 T1 T2 T3 T')

-- a term of the type Insert Γ n X Γ'
-- is the evidence that inserting X at the n-th position of Γ results in Γ'
data Insert : (Γ : Ctx) (n : Nat) (X : Type) (Γ' : Ctx) → Set where
  ins-zero : {Γ : Ctx} {X : Type} → Insert Γ zero X (Γ // X)
  ins-suc  : {Γ : Ctx} {n : Nat} {X Y : Type} {Γ' : Ctx}
           → Insert Γ n X Γ'
           → Insert (Γ // Y) (suc n) X (Γ' // Y)

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
subs (fix p) n r = let n' = suc n
                       r' = lift 0 r
                    in fix (subs p n' r')


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
  app-func  : {p p' q : Prog} → p ↦ p' → p · q ↦ p' · q
  app-args : {p q q' : Prog} → q ↦ q' → p · q ↦ p · q'
  app-beta : {p q : Prog} → (abs p) · q ↦ (subs p 0 q)
  -- unfold a fixed point
  fix-body : {p p' : Prog} → p ↦ p' → fix p ↦ fix p'
  fix-unfold : {p : Prog} → fix p ↦ subs p 0 (fix p)


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
  -- fixed point
  ⊢fix : {Γ : Ctx} {p : Prog} {A : Type} → Γ // A ⊢ p ∷ A → Γ ⊢ fix p ∷ A

data Value where
  unitV : Value unit
  boolV : {b : Bool} → Value (bool b)
  natV : {n : Nat} → Value (nat n)
  pairV : {p q : Prog} → Value p → Value q → Value ⟨ p , q ⟩
  lambdaV : {p : Prog} → Value (abs p)


lookup-lift-lt : {Γ : Ctx} {n : Nat} {Γ' : Ctx} {X : Type} {ins : Insert Γ n X Γ'}
                 {i : Nat} {i<n : i < n} {A : Type}
               → Lookup Γ i A → Lookup Γ' i A
lookup-lift-lt {n = suc n} {ins = ins-suc ins} {i = zero} {i<n = z<s} at-head = at-head
lookup-lift-lt {n = suc n} {ins = ins-suc ins} {i = suc i} {i<n = s<s i<n} (in-tail lookup) =
  in-tail (lookup-lift-lt {n = n} {ins = ins} {i = i} {i<n = i<n} lookup)

lookup-lift-geq : {Γ : Ctx} {n : Nat} {Γ' : Ctx} {X : Type} {ins : Insert Γ n X Γ'}
                  {i : Nat} {n≤i : n ≤ i} {A : Type}
                → Lookup Γ i A → Lookup Γ' (suc i) A
lookup-lift-geq {n = zero} {ins = ins-zero} {i = zero} {n≤i = z≤n} at-head = in-tail at-head
lookup-lift-geq {n = zero} {ins = ins-zero} {i = suc i} {n≤i = z≤n} (in-tail lookup) =
  in-tail (lookup-lift-geq {n = zero} {ins = ins-zero} {i = i} {n≤i = z≤n} lookup)
lookup-lift-geq {n = suc n} {ins = ins-suc ins} {i = suc i} {n≤i = s≤s n≤i} (in-tail lookup) =
  in-tail (lookup-lift-geq {n = n} {ins = ins} {i = i} {n≤i = n≤i} lookup)

lift-lemma : {Γ : Ctx} {n : Nat} {Γ' : Ctx} {X : Type} {ins : Insert Γ n X Γ'}
             {p : Prog} {A : Type}
           → Γ ⊢ p ∷ A
           → Γ' ⊢ lift n p ∷ A
lift-lemma ⊢ℕ = ⊢ℕ
lift-lemma ⊢𝔹 = ⊢𝔹
lift-lemma {ins = ins} (⊢+ ⊢p:N ⊢q:N) =
  let ⊢p:N' = lift-lemma {ins = ins} ⊢p:N
      ⊢q:N' = lift-lemma {ins = ins} ⊢q:N
   in ⊢+ ⊢p:N' ⊢q:N'
lift-lemma {ins = ins} (⊢< ⊢p:N ⊢q:N) =
  let ⊢p:N' = lift-lemma {ins = ins} ⊢p:N
      ⊢q:N' = lift-lemma {ins = ins} ⊢q:N
   in ⊢< ⊢p:N' ⊢q:N'
lift-lemma {ins = ins} (⊢if ⊢c:B ⊢p:A ⊢q:A) =
  let ⊢c:B' = lift-lemma {ins = ins} ⊢c:B
      ⊢p:A' = lift-lemma {ins = ins} ⊢p:A
      ⊢q:A' = lift-lemma {ins = ins} ⊢q:A
   in ⊢if ⊢c:B' ⊢p:A' ⊢q:A'
lift-lemma {ins = ins} (⊢pair ⊢p:A ⊢q:B) =
  let ⊢p:A' = lift-lemma {ins = ins} ⊢p:A
      ⊢q:B' = lift-lemma {ins = ins} ⊢q:B
   in ⊢pair ⊢p:A' ⊢q:B'
lift-lemma {ins = ins} (⊢proj0 ⊢p:AB) = ⊢proj0 (lift-lemma {ins = ins} ⊢p:AB)
lift-lemma {ins = ins} (⊢proj1 ⊢p:AB) = ⊢proj1 (lift-lemma {ins = ins} ⊢p:AB)
lift-lemma {ins = ins} ⊢𝟙 = ⊢𝟙
lift-lemma {ins = ins} (⊢app ⊢p:A⇒B ⊢q:A) =
  let ⊢p:A⇒B' = lift-lemma {ins = ins} ⊢p:A⇒B
      ⊢q:A'   = lift-lemma {ins = ins} ⊢q:A
   in ⊢app ⊢p:A⇒B' ⊢q:A'
lift-lemma {n = n} {ins = ins} {p = var i} (⊢ax lookup) with dec< i n
... | left  i<n = ⊢ax (lookup-lift-lt  {n = n} {ins = ins} {i<n = i<n} lookup)
... | right n≤i = ⊢ax (lookup-lift-geq {n = n} {ins = ins} {n≤i = n≤i} lookup)
lift-lemma {ins = ins} (⊢abs lam) = ⊢abs (lift-lemma {ins = ins-suc ins} lam)
lift-lemma {ins = ins} (⊢fix  mu) = ⊢fix (lift-lemma {ins = ins-suc ins}  mu)

subs-lemma-n : {Γ Γ' : Ctx} {n : Nat} {p q : Prog} {X A : Type}
               {ins : Insert Γ n X Γ'}
             → Γ' ⊢ p ∷ A
             → Γ  ⊢ q ∷ X
             → Γ  ⊢ subs p n q ∷ A
subs-lemma-n {ins = ins} ⊢ℕ ⊢q:X = ⊢ℕ
subs-lemma-n {ins = ins} ⊢𝔹 ⊢q:X = ⊢𝔹
subs-lemma-n {ins = ins} (⊢+ X⊢p:N X⊢q:N) ⊢q:X =
  let ⊢p:N = subs-lemma-n {ins = ins} X⊢p:N ⊢q:X 
      ⊢q:N = subs-lemma-n {ins = ins} X⊢q:N ⊢q:X
   in ⊢+ ⊢p:N ⊢q:N
subs-lemma-n {ins = ins} (⊢< X⊢p:N X⊢q:N) ⊢q:X =
  let ⊢p:N = subs-lemma-n {ins = ins} X⊢p:N ⊢q:X 
      ⊢q:N = subs-lemma-n {ins = ins} X⊢q:N ⊢q:X
   in ⊢< ⊢p:N ⊢q:N
subs-lemma-n {ins = ins} (⊢if X⊢c:B X⊢p:A X⊢q:A) ⊢q:X =
  let ⊢c:B = subs-lemma-n {ins = ins} X⊢c:B ⊢q:X 
      ⊢p:A = subs-lemma-n {ins = ins} X⊢p:A ⊢q:X
      ⊢q:A = subs-lemma-n {ins = ins} X⊢q:A ⊢q:X
   in ⊢if ⊢c:B ⊢p:A ⊢q:A
subs-lemma-n {ins = ins} (⊢pair X⊢p:A X⊢q:B) ⊢q:X =
  let ⊢p:A = subs-lemma-n {ins = ins} X⊢p:A ⊢q:X 
      ⊢q:B = subs-lemma-n {ins = ins} X⊢q:B ⊢q:X
   in ⊢pair ⊢p:A ⊢q:B
subs-lemma-n {ins = ins} (⊢proj0 X⊢p:AB) ⊢q:X = let ⊢p:AB = subs-lemma-n {ins = ins} X⊢p:AB ⊢q:X in ⊢proj0 ⊢p:AB
subs-lemma-n {ins = ins} (⊢proj1 X⊢p:AB) ⊢q:X = let ⊢p:AB = subs-lemma-n {ins = ins} X⊢p:AB ⊢q:X in ⊢proj1 ⊢p:AB
subs-lemma-n {ins = ins} ⊢𝟙 ⊢q:X = ⊢𝟙
-- variable
subs-lemma-n {Γ} {n = n} {p = var m} {q} {ins = ins} (⊢ax lookup) ⊢q:X
  with trichotomy m n
... | tri-= m=n =
  let X=A = matched m=n ins lookup in subst (Γ ⊢ q ∷_) X=A ⊢q:X
  where matched : {m n : Nat} {Γ Γ' : Ctx} {X A : Type}
                → m ≡ n
                → Insert Γ n X Γ'
                → Lookup Γ' m A
                → X ≡ A
        matched {zero} {zero} refl ins-zero at-head = refl
        matched {suc m} {suc n} m=n (ins-suc ins) (in-tail lookup) = matched (cong pred m=n) ins lookup
... | tri-< m<n = ⊢ax (matched m<n ins lookup)
  where matched : {m n : Nat} {Γ Γ' : Ctx} {X A : Type}
                → m < n
                → Insert Γ n X Γ'
                → Lookup Γ' m A
                → Lookup Γ m A
        matched {zero} {suc n} m<n (ins-suc ins) at-head = at-head
        matched {suc m} {suc n} (s<s m<n) (ins-suc ins) (in-tail lookup) = in-tail (matched m<n ins lookup)
... | tri-> m>n = ⊢ax (matched m>n ins lookup)
  where matched : {m n : Nat} {Γ Γ' : Ctx} {X A : Type}
                → n < m
                → Insert Γ n X Γ'
                → Lookup Γ' m A
                → Lookup Γ (pred m) A
        matched {suc m} {zero} n<m ins-zero (in-tail lookup) = lookup
        matched {(suc (suc m))} {suc n} (s<s {_} {_} n<m) (ins-suc ins) (in-tail lookup) = in-tail (matched n<m ins lookup)
-- application
subs-lemma-n {ins = ins} (⊢app X⊢p:A⇒B X⊢q:A) ⊢q:X =
  let ⊢p:A⇒B = subs-lemma-n {ins = ins} X⊢p:A⇒B ⊢q:X 
      ⊢q:A   = subs-lemma-n {ins = ins} X⊢q:A   ⊢q:X
   in ⊢app ⊢p:A⇒B ⊢q:A
-- abstraction
subs-lemma-n {p = abs p} {q} {X} {A ⇒ B} {ins} (⊢abs XA⊢p:B) ⊢q:X =
  let t = lift-lemma {ins = ins-zero} ⊢q:X
   in ⊢abs (subs-lemma-n {ins = ins-suc ins} XA⊢p:B t)
-- fixed point
subs-lemma-n {p = fix p} {q} {X} {A} {ins} (⊢fix XA⊢p:A) ⊢q:X =
  let t = lift-lemma {ins = ins-zero} ⊢q:X
   in ⊢fix (subs-lemma-n {ins = ins-suc ins} XA⊢p:A t)


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
preservation (⊢proj1 ⊢p:AB) (proj1-pair p↦p') = let ⊢p':AB = preservation ⊢p:AB p↦p' in ⊢proj1 ⊢p':AB
preservation (⊢proj0 (⊢pair ⊢p:A ⊢q:B)) pair-fst = ⊢p:A
preservation (⊢proj1 (⊢pair ⊢p:A ⊢q:B)) pair-snd = ⊢q:B
-- function
preservation (⊢app ⊢p:A⇒B ⊢q:A) (app-func p↦p') = let ⊢p':A⇒B = preservation ⊢p:A⇒B p↦p' in ⊢app ⊢p':A⇒B ⊢q:A
preservation (⊢app ⊢p:A⇒B ⊢q:A) (app-args q↦q') = let ⊢q':A   = preservation ⊢q:A   q↦q' in ⊢app ⊢p:A⇒B  ⊢q':A
preservation (⊢app (⊢abs A⊢p:B) ⊢q:A) app-beta = subs-lemma-n {ins = ins-zero} A⊢p:B ⊢q:A
-- fixed point
preservation (⊢fix A⊢p:A) (fix-body p↦p') = let A⊢p':A = preservation A⊢p:A p↦p' in ⊢fix A⊢p':A
preservation (⊢fix A⊢p:A) fix-unfold = subs-lemma-n {ins = ins-zero} A⊢p:A (⊢fix A⊢p:A)

-- The progress property asserts that
-- a cloesd and well-typed term
-- is either a value or can be further reduced
progress : {p : Prog} {A : Type}
         → ∅ ⊢ p ∷ A
         → Σ Prog (λ q → p ↦ q) ∨ Value p
progress ⊢ℕ = right natV
progress ⊢𝔹 = right boolV
progress {p = p +ₑ q} (⊢+ ⊢p:N ⊢q:N) 
  with progress ⊢p:N
... | left (p' , p↦p') = left (p' +ₑ q , +-left  p↦p')
... | right (natV {m})
  with progress ⊢q:N
... | left (q' , q↦q') = left (p +ₑ q' , +-right q↦q')
... | right (natV {n}) = left (nat (m + n) , +-natval)
progress {p = p <ₑ q} (⊢< ⊢p:N ⊢q:N)
  with progress ⊢p:N
... | left (p' , p↦p') = left (p' <ₑ q , <-left  p↦p')
... | right (natV {m})
  with progress ⊢q:N
... | left (q' , q↦q') = left (p <ₑ q' , <-right q↦q')
... | right (natV {n})
  with dec< m n
... | left  m<n = left (bool true  , <-true  m<n)
... | right n≤m = left (bool false , <-false n≤m)
progress {p = if c then p else q} (⊢if ⊢c:B ⊢p:A ⊢q:A) 
  with progress ⊢c:B
... | left (c' , c↦c') = left (if c' then p else q , if-cond c↦c')
... | right (boolV {true} ) = left (p , if-true )
... | right (boolV {false}) = left (q , if-false)
progress {p = ⟨ p , q ⟩} (⊢pair ⊢p:A ⊢q:B)
  with progress ⊢p:A
... | left (p' , p↦p') = left (⟨ p' , q ⟩ , pair-left   p↦p')
... | right vp
  with progress ⊢q:B
... | left (q' , q↦q') = left (⟨ p , q' ⟩ , pair-right  q↦q')
... | right vq = right (pairV vp vq)
progress {p = proj0 p} (⊢proj0 ⊢p:AB)
  with progress ⊢p:AB
... | left (p' , p↦p') = left (proj0 p' , proj0-pair p↦p')
... | right (pairV {p0} {p1} vp0 vp1) = left ( p0 , pair-fst )
progress {p = proj1 p} (⊢proj1 ⊢p:AB)
  with progress ⊢p:AB
... | left (p' , p↦p') = left (proj1 p' , proj1-pair p↦p')
... | right (pairV {p0} {p1} vp0 vp1) = left ( p1 , pair-snd )
progress {p = var i} (⊢ax ())
progress {p = abs p} (⊢abs A⊢p:B) = right lambdaV
progress {p = p · q} (⊢app ⊢p:A⇒B ⊢q:A)
  with progress ⊢p:A⇒B
... | left (p' , p↦p') = left (p' · q , app-func p↦p')
... | right (lambdaV {body}) = left ( subs body 0 q , app-beta )
progress {p = fix p} (⊢fix A⊢p:A) = left ( subs p 0 (fix p) , fix-unfold )
progress {p = unit} ⊢𝟙 = right unitV
