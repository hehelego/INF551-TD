-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

-- 2. Our first proof

open import Data.Product

×-comm : {A B : Set} → (A × B) → (B × A)
×-comm (fst , snd) = snd , fst

-- 3. Implication

id : {A : Set} → A → A
id a = a

K : {A B : Set} → A → B → A
K a b = a

app : {A B : Set} → (A → B) → A → B
app f x = f x

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f y x = f x y

comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp f g x = g (f x)

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g x = f x (g x)

-- 4. Implication

open import Data.Product renaming (_×_ to _∧_)

proj1 : {A B : Set} → (A ∧ B) → A
proj1 (a , b) = a

proj2 : {A B : Set} → (A ∧ B) → B
proj2 (a , b) = b

diag : {A : Set} → A → A ∧ A
diag a = a , a

∧-comm : {A B : Set} → (A ∧ B) → B ∧ A
∧-comm (a , b) = (b , a)

curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f x y = f (x , y)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f (x , y) = f x y

equiv : (A B : Set) → Set
equiv A B = (A → B) ∧ (B → A)

_↔_ : (A B : Set) → Set
A ↔ B = equiv A B

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = curry1 , curry2

impl-and-distrib : {A B C : Set} → (A → B ∧ C) → (A → B) ∧ (A → C)
impl-and-distrib f = (λ { x → proj1 (f x) }) , (λ { x → proj2 (f x) })

-- 5. Disjunction

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left x) f g = f x
or-elim (right y) f g = g y

or-comm : {A B : Set} → (A ∨ B) → B ∨ A
or-comm (left x) = right x
or-comm (right y) = left y


and-or-distrib : {A B C : Set} → (A ∧ (B ∨ C)) → (A ∧ B) ∨ (A ∧ C)
and-or-distrib (x , left y) = left (x , y)
and-or-distrib (x , right z) = right (x , z)

-- 6. Negation

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ t = t → ⊥

contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr a→b ¬b a = ¬b (a→b a)

non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (a , ¬a) = ¬a a

nni : {A : Set} → A → ¬ (¬ A)
nni x f = f x

⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne f = f λ {x → x}

¬-elim : {A B : Set} → ¬ A → A → B
¬-elim ¬a a = ⊥-elim (¬a a)

dm∧ : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
dm∧ (¬a , ¬b) (left a) = ¬a a
dm∧ (¬a , ¬b) (right b) = ¬b b

converse-dm∧ : {A B : Set} → ¬ (A ∨ B) → (¬ A ∧ ¬ B)
converse-dm∧ {A} {B} f = (λ { x → f (left x) }) , (λ { y → f (right y) })

dm∨ : {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
dm∨ (left ¬a) (a , b) = ¬a a
dm∨ (right ¬b) (a , b) = ¬b b

converse'-dm∨ : {A B : Set} → ¬ (A ∧ B) → ¬ ( ¬ (¬ A ∨ ¬ B))
converse'-dm∨ {A} {B} f g = g (left λ { x → g (right λ { y → f (x , y) }) })

-- the converse
-- {A B : Set} → ¬ (A ∧ B) → (¬ A ∨ ¬ B)
-- is equivalent to the law of excluded middle, which is not provable yet irrefutable in Agda.

nnlem : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
nnlem {A} f = f (right λ { x → f (left x) })

-- f : (A or ~A) -> false
-- ----------------------
-- false
-- [apply f]
--
-- f : (A or ~A) -> false
-- ----------------------
-- A or ~A
-- [right]
--
-- f : (A or ~A) -> false
-- ----------------------
-- A -> false
-- [intro x]
--
-- f : (A or ~A) -> false
-- x : A
-- ----------------------
-- false
-- [apply f]
--
-- f : (A or ~A) -> false
-- x : A
-- ----------------------
-- A or ~A
-- [left]
-- 
-- f : (A or ~A) -> false
-- x : A
-- ----------------------
-- A
-- [exact x]

rp : {A : Set} → (A → ¬ A) → ((¬ A) → A) → ⊥
rp {A} f g = f x x
  where
    y : ¬ A
    y = λ { a → f a a }
    x : A
    x = g y

-- 7. Truth

data ⊤ : Set where
  tt : ⊤

ti : {A : Set} → (⊤ → A) → A
ti f = f tt

dmnt : ¬ ⊤ → ⊥
dmnt = ti {⊥}

dmtn : ⊥ → ¬ ⊤
dmtn x tt = x

-- 8. Classical logic

lem nne pierce : Set₁
lem = (A : Set) → A ∨ (¬ A)
nne = (A : Set) → ¬ (¬ A) → A
pierce = (A B : Set) → ((A → B) → A) → A

nne-lem : nne → lem
nne-lem nne-func A = nne-func (A ∨ ¬ A) nnlem

lem-nne' : (A : Set) → (A ∨ ¬ A) → ¬ (¬ A) → A
lem-nne' A (left x) ¬¬a = x
lem-nne' A (right ¬x) ¬¬a = ⊥-elim (¬¬a ¬x)

lem-nne : lem → nne
lem-nne lem-func A = lem-nne' A (lem-func A)

-- Additionally, the pierce law is equivalent to the two others classical logic theorems

pierce-nne : pierce → nne
pierce-nne pierce-func A ¬¬a = pierce-func A ⊥ lemma
  where
    lemma : (A → ⊥) → A
    lemma ¬a = ⊥-elim (¬¬a ¬a)

nne-pierce : nne → pierce
nne-pierce nne-func A B = nne-func (((A → B) → A) → A) pierce-irrefutable
  where
    pierce-irrefutable : ¬ (((A → B) → A) → A) → ⊥
    pierce-irrefutable no-pierce = no-pierce λ { f → f λ { a → ⊥-elim (no-pierce λ { _ → a }) } }

pierce-lem : pierce → lem
pierce-lem pierce-func A = pierce-func (A ∨ ¬ A) ⊥ lemma
 where
   lemma : (A ∨ ¬ A → ⊥) → A ∨ ¬ A
   lemma no-lem = ⊥-elim (nnlem no-lem)

lem-pierce : lem → pierce
lem-pierce lem-func A B f with lem-func A
... | left x = x
... | right ¬x = f λ { x → ⊥-elim (¬x x) }

-- 9. First-order logic (optional)

postulate U : Set

∀-comm : {P : U → U → Set} → ((x : U) → (y : U) → P x y) → ((y : U) → (x : U) → P x y)
∀-comm f y x = f x y

∃-comm : {P : U → U → Set} → ∃ (λ x → ∃ (λ y → P x y)) → ∃ (λ y → ∃ (λ x → P x y))
∃-comm (x , (y , p)) = (y , (x , p))

∀-∨-factorize : {P Q : U → Set} → ((x : U) → P x) ∨ ((x : U) → Q x) → ((x : U) → (P x ∨ Q x))
∀-∨-factorize (left f) x = left (f x)
∀-∨-factorize (right g) x = right (g x)

∀-∧-distrib : {P Q : U → Set} → ((x : U) → P x ∧ Q x) ↔ (((x : U) → P x) ∧ ((x : U) → Q x))
∀-∧-distrib {P} {Q} = proof→ , proof←
  where
    fst : {x : U} → (P x ∧ Q x) → P x
    fst (a , _) = a
    snd : {x : U} → (P x ∧ Q x) → Q x
    snd (_ , b) = b
    proof→ : (((x : U) → P x ∧ Q x) → ((x : U) → P x) ∧ ((x : U) → Q x))
    proof→ f = (λ {x → fst (f x)}) , (λ {x → snd (f x)})
    proof← : (((x : U) → P x) ∧ ((x : U) → Q x) → (x : U) → P x ∧ Q x)
    proof← (f , g) x = (f x , g x)

∃¬→¬∀ : {P Q : U → Set} → ∃ (λ x → ¬ (P x)) → ¬ ((x : U) → P x)
∃¬→¬∀ (x , ¬px) ∀p = ¬px (∀p x)

∀¬→¬∃ : {P Q : U → Set} → ((x : U) → ¬ (P x)) → ¬ (∃ (λ x → P x))
∀¬→¬∃ f (x , px) = f x px

