-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head ; merge)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s m≤n) = m≤n

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc m≤n = s≤s m≤n

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = s≤s (≤s n)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n z≤n = z≤n
≤-trans z≤n (s≤s n≤p) = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
suc m ≤? zero = right z≤n
suc m ≤? suc n with m ≤? n
... | left  m≤n = left  (s≤s m≤n)
... | right n≤m = right (s≤s n≤m)

-- The predicate _<_ takes two terms of type ℕ and gives back a proposition
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

z<s : {m : ℕ} → zero < suc m
z<s = s≤s z≤n

s<s : {m n : ℕ} → m < n → suc m < suc n
s<s = s≤s

<-pred : {m n : ℕ} → (suc m < suc n) → m < n
<-pred (s≤s m<n) = m<n

<s : (n : ℕ) → n < suc n
<s n = ≤-refl (suc n)

<-trans : {m n p : ℕ} → m < n → n < p → m < p
<-trans {m} {n} {p} m<n n<p = ≤-trans m<n (≤-pred (≤-trans n<p (≤s p)))

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (hd ∷ tl) = suc (length tl)

_<len_ : {A : Set} (xs ys : List A) → Set
xs <len ys = length xs < length ys

insert : (z : ℕ) → (xs : List ℕ) → List ℕ
insert z [] = z ∷ []
insert z (x ∷ xs) with z ≤? x
... | left  z≤x = z ∷ (x ∷ xs)
... | right x≤z = x ∷ (insert z xs)

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

test-sort : sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ []) ≡ (1 ∷ 1 ∷ 4 ∷ 8 ∷ 12 ∷ 32 ∷ 45 ∷ [])
test-sort = refl

data _≤*_ : ℕ → List ℕ → Set where
  [] : {z : ℕ} → z ≤* []
  _∷_ : {z x : ℕ} {xs : List ℕ} → z ≤ x → z ≤* xs → z ≤* (x ∷ xs)

data sorted : List ℕ → Set where
  [] : sorted []
  _∷_ : {z : ℕ} {xs : List ℕ} → z ≤* xs → sorted xs → sorted (z ∷ xs)

≤→≤* : {z y : ℕ} {xs : List ℕ} → z ≤ y → y ≤* xs → z ≤* xs
≤→≤* z≤x [] = []
≤→≤* {z} {y} {x ∷ xs} z≤y (y≤x ∷ y≤*xs) = let z≤x   = ≤-trans z≤y y≤x
                                              z≤*xs = ≤→≤* z≤y y≤*xs
                                           in z≤x ∷ z≤*xs

ins-≤* : {z y : ℕ} {xs : List ℕ} → z ≤ y → z ≤* xs → z ≤* insert y xs
ins-≤* z≤y [] = z≤y ∷ []
ins-≤* {z} {y} {x ∷ xs} z≤y (z≤x ∷ z≤*xs)
  with y ≤? x
... | left  y≤x = let z≤*x∷xs = z≤x ∷ z≤*xs
                   in z≤y ∷ z≤*x∷xs
... | right x≤y = let z≤*ins-y-xs = ins-≤* z≤y z≤*xs in z≤x ∷ z≤*ins-y-xs


insert-sorting : (z : ℕ) → (xs : List ℕ) → sorted xs → sorted (insert z xs)
insert-sorting z [] [] = [] ∷ []
insert-sorting z (x ∷ xs) sort-x∷xs@(x≤*xs ∷ sort-xs)
  with z ≤? x
... | left  z≤x = let z≤*xs   = ≤→≤* z≤x x≤*xs
                      z≤*x∷xs = z≤x ∷ z≤*xs
                   in z≤*x∷xs ∷ sort-x∷xs
... | right x≤z = let x≤*ins-z-xs = ins-≤* x≤z x≤*xs in x≤*ins-z-xs ∷ (insert-sorting z xs sort-xs)

-- sorted (insert z (x ∷ xs) ) | right x≤z
-- sorted (x ∷ insert z xs)

sort-sorting : (xs : List ℕ) → sorted (sort xs)
sort-sorting [] = []
sort-sorting (x ∷ xs) = let xs'        = sort xs
                            sorted-xs' = sort-sorting xs
                         in insert-sorting x xs' sorted-xs'

-- the correctness specification is not strong enough
-- the missing condition: the output should be a permutation of the input list
f : List ℕ → List ℕ
f xs = []
f-sorting : (l : List ℕ) → sorted (f l)
f-sorting l = []


-- A term of the Sorted set is
-- 1. Either an empty list nil
-- 2. Or the concatenation of an element x and another sorted list xs such that x is no greater than the head of xs
interleaved mutual
  data Sorted : Set
  head : ℕ → Sorted → ℕ

  data Sorted where
    nil : Sorted
    cons : (x : ℕ) (xs : Sorted) (ord : x ≤ head x xs) → Sorted

  head y nil = y
  head y (cons x xs ord) = x

-- See https://agda.readthedocs.io/en/v2.6.3/language/mutual-recursion.html
interleaved mutual
    insert' : (z : ℕ) → Sorted → Sorted
    insert'-lemma : (z y : ℕ) (xs : Sorted) (z≤y : z ≤ y) (z≤hd : z ≤ head z xs) → z ≤ head z (insert' y xs)

    insert' z nil = cons z nil (≤-refl z)
    insert' z l@(cons x xs x≤hd)
      with z ≤? x
    ... | left  z≤x = cons z l z≤x
    ... | right x≤z = let xs'   = insert' z xs
                          x≤hd' = insert'-lemma x z xs x≤z x≤hd
                       in cons x xs' x≤hd'

    insert'-lemma z y nil z≤y z≤hd = z≤y
    insert'-lemma z y (cons x xs x≤hd) z≤y z≤hd
      with y ≤? x
    ... | left  y≤x = z≤y
    ... | right x≤y = z≤hd

sort' : List ℕ → Sorted
sort' [] = nil
sort' (x ∷ xs) = insert' x (sort' xs)

test-sort' : Sorted
test-sort' = sort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

split : {A : Set} → List A → List A × List A
split [] = ([] , [])
split (x ∷ []) = ((x ∷ []) , [])
split (x ∷ y ∷ xs) = let (l , r) = split xs in (x ∷ l , y ∷ r)

test-split : split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ []) ≡ (4 ∷ 45 ∷ 32 ∷ 1 ∷ [] , 1 ∷ 8 ∷ 12 ∷ [])
test-split = refl

{-# TERMINATING #-}
merge : List ℕ → List ℕ → List ℕ
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys)
  with x ≤? y
... | left  x≤y = x ∷ merge xs (y ∷ ys)
... | right y≤x = y ∷ merge (x ∷ xs) ys

test-merge : merge (1 ∷ 4 ∷ 32 ∷ 45 ∷ []) (1 ∷ 8 ∷ 12 ∷ []) ≡ (1 ∷ 1 ∷ 4 ∷ 8 ∷ 12 ∷ 32 ∷ 45 ∷ [])
test-merge = refl

{-# TERMINATING #-}
mergesort : List ℕ → List ℕ
mergesort [] = []
mergesort (x ∷ []) = x ∷ []
mergesort xs@(x0 ∷ x1 ∷ rest) = let (l , r) = split xs in merge (mergesort l) (mergesort r)

test-mergesort : mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ []) ≡ (1 ∷ 1 ∷ 4 ∷ 8 ∷ 12 ∷ 32 ∷ 45 ∷ [])
test-mergesort = refl


-- Consistency of the system can be broken if the termination checking is disabled.
-- The following definition proves everything.
--
-- {-# TERMINATING #-}
-- inconsistency : {l : Agda.Primitive.Level} (A : Set l) → A
-- inconsistency A = inconsistency A

split-fst-decr : {A : Set} (x y : A) (l : List A) → fst (split (x ∷ y ∷ l)) <len (x ∷ y ∷ l)
split-fst-decr x y [] = <s 1
split-fst-decr x y (e ∷ []) = <s 2
split-fst-decr x y (x' ∷ y' ∷ l) = let IH       = split-fst-decr x' y' l
                                       IH'      = s<s (s<s IH)
                                       len-fst  = length (fst (split l))
                                       len-fst' = 2 + length (fst (split l))
                                    in <-trans (<s len-fst') IH'

split-snd-decr : {A : Set} (x y : A) (l : List A) → snd (split (x ∷ y ∷ l)) <len (x ∷ y ∷ l)
split-snd-decr x y [] = <s 1
split-snd-decr x y (e ∷ []) = s<s z<s
split-snd-decr x y (x' ∷ y' ∷ l) = let IH       = split-snd-decr x' y' l
                                       IH'      = s<s (s<s IH)
                                       len-snd  = length (snd (split l))
                                       len-snd' = 2 + length (snd (split l))
                                    in <-trans (<s len-snd') IH'

merge-fuel : (m n : ℕ) (xs ys : List ℕ) → length xs ≡ m → length ys ≡ n → List ℕ
merge-fuel 0 n [] ys lx=m ly=n = ys
merge-fuel m 0 xs [] lx=m ly=n = xs
merge-fuel (suc m) (suc n) (x ∷ xs) (y ∷ ys) lx=m ly=n
  with x ≤? y
... | left  x≤y = x ∷ merge-fuel m (suc n) xs (y ∷ ys) (cong pred lx=m) ly=n
... | right y≤x = y ∷ merge-fuel (suc m) n (x ∷ xs) ys lx=m (cong pred ly=n)

merge' : (xs ys : List ℕ) → List ℕ
merge' xs ys = let m = length xs
                   n = length ys
                in merge-fuel m n xs ys refl refl

test-merge' : merge' (1 ∷ 4 ∷ 32 ∷ 45 ∷ []) (1 ∷ 8 ∷ 12 ∷ []) ≡ (1 ∷ 1 ∷ 4 ∷ 8 ∷ 12 ∷ 32 ∷ 45 ∷ [])
test-merge' = refl

merge'-[]-ys : (ys : List ℕ) → merge' [] ys ≡ ys
merge'-[]-ys [] = refl
merge'-[]-ys (y ∷ ys) = let IH = merge'-[]-ys ys in cong (y ∷_) IH

merge'-xs-[] : (xs : List ℕ) → merge' xs [] ≡ xs
merge'-xs-[] [] = refl
merge'-xs-[] (x ∷ xs) = refl

merge'-≤*-fuel : (m n : ℕ) (z : ℕ) (xs ys : List ℕ) (m=lx : m ≡ length xs) (n=ly : n ≡ length ys)
               → z ≤* xs → z ≤* ys → z ≤* merge' xs ys
merge'-≤*-fuel zero n z [] ys m=lx n=ly z≤*xs z≤*ys =
  let =ys = sym (merge'-[]-ys ys) in subst (z ≤*_) =ys z≤*ys
merge'-≤*-fuel m zero z xs [] m=lx n=ly z≤*xs z≤*ys =
  let =xs = sym (merge'-xs-[] xs) in subst (z ≤*_) =xs z≤*xs
merge'-≤*-fuel (suc m) (suc n) z (x ∷ xs) (y ∷ ys) m=lx n=ly (z≤x ∷ z≤*xs) (z≤y ∷ z≤*ys)
  with x ≤? y
... | left  x≤y = let m=lx' = cong pred m=lx
                      IH = merge'-≤*-fuel m (suc n) z xs (y ∷ ys) m=lx' n=ly
                                          z≤*xs (z≤y ∷ z≤*ys)
                   in z≤x ∷ IH
... | right y≤x = let n=ly' = cong pred n=ly
                      IH = merge'-≤*-fuel (suc m) n z (x ∷ xs) ys m=lx n=ly'
                                          (z≤x ∷ z≤*xs) z≤*ys
                   in z≤y ∷ IH

merge'-≤* : (z : ℕ) {xs ys : List ℕ} → z ≤* xs → z ≤* ys → z ≤* merge' xs ys
merge'-≤* z {xs} {ys} z≤*xs z≤*ys = let m = length xs
                                        n = length ys
                                     in merge'-≤*-fuel m n z xs ys refl refl z≤*xs z≤*ys

merge'-sorted-fuel : (m n : ℕ) (xs ys : List ℕ) → length xs ≡ m → length ys ≡ n
                   → sorted xs → sorted ys → sorted (merge' xs ys)
merge'-sorted-fuel zero n [] ys refl n=ly sorted-xs sorted-ys =
  let =ys = merge'-[]-ys ys       in subst sorted =ys sorted-ys
merge'-sorted-fuel m zero xs [] m=lx refl sorted-xs sorted-ys =
  let =xs = sym (merge'-xs-[] xs) in subst sorted =xs sorted-xs
merge'-sorted-fuel (suc m) (suc n) (x ∷ xs) (y ∷ ys) m=lx n=ly
                   (x≤*xs ∷ sorted-xs) (y≤*ys ∷ sorted-ys)
  with x ≤? y
... | left  x≤y = let IH = merge'-sorted-fuel m (suc n) xs (y ∷ ys)
                              (cong pred m=lx) n=ly
                              sorted-xs (y≤*ys ∷ sorted-ys)
                      y≤*y∷ys = (≤-refl y) ∷ y≤*ys
                      x≤*merge = merge'-≤* x x≤*xs (≤→≤* x≤y y≤*y∷ys)
                   in x≤*merge ∷ IH
... | right y≤x = let IH = merge'-sorted-fuel (suc m) n (x ∷ xs) ys
                              m=lx (cong pred n=ly)
                              (x≤*xs ∷ sorted-xs) sorted-ys
                      x≤*x∷xs = (≤-refl x) ∷ x≤*xs
                      y≤*merge = merge'-≤* y (≤→≤* y≤x x≤*x∷xs) y≤*ys
                   in y≤*merge ∷ IH

merge'-sorted : (xs ys : List ℕ) → sorted xs → sorted ys → sorted (merge' xs ys)
merge'-sorted xs ys sorted-xs sorted-ys = let m = length xs
                                              n = length ys
                                           in merge'-sorted-fuel m n xs ys refl refl sorted-xs sorted-ys

mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel n [] len≤n = []
mergesort-fuel n (x ∷ []) len≤n = (x ∷ [])
mergesort-fuel (suc n) xs@(x ∷ y ∷ tl) len≤n =
  let (l , r) = split xs
      liml = split-fst-decr x y tl
      limr = split-snd-decr x y tl
   in merge' (mergesort-fuel n l (≤-pred (≤-trans liml len≤n)))
             (mergesort-fuel n r (≤-pred (≤-trans limr len≤n)))

-- providing more fuel than then minimum required amount will not affect the output
mergesort-fuel-consistent : (m n : ℕ) → (l : List ℕ) → (len≤m : length l ≤ m) → (len≤n : length l ≤ n)
                          → mergesort-fuel m l len≤m ≡ mergesort-fuel n l len≤n
mergesort-fuel-consistent m n [] len≤m len≤n = refl
mergesort-fuel-consistent m n (x ∷ []) len≤m len≤n = refl
mergesort-fuel-consistent (suc m) (suc n) xs@(x ∷ y ∷ tl) len≤m len≤n =
  let (l , r) = split xs
      liml   = split-fst-decr x y tl
      limr   = split-snd-decr x y tl

      llen≤m = ≤-pred (≤-trans liml len≤m)
      rlen≤m = ≤-pred (≤-trans limr len≤m)
      llen≤n = ≤-pred (≤-trans liml len≤n)
      rlen≤n = ≤-pred (≤-trans limr len≤n)

      fst-IH = mergesort-fuel-consistent m n l llen≤m llen≤n
      snd-IH = mergesort-fuel-consistent m n r rlen≤m rlen≤n

   in cong₂ merge' fst-IH snd-IH


mergesort' : List ℕ → List ℕ
mergesort' l = let n = length l in mergesort-fuel n l (≤-refl n)

test-mergesort' : mergesort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ []) ≡ (1 ∷ 1 ∷ 4 ∷ 8 ∷ 12 ∷ 32 ∷ 45 ∷ [])
test-mergesort' = refl

mergesort-sorting-fuel : (n : ℕ) (l : List ℕ) (len≤n : length l ≤ n) → sorted (mergesort-fuel n l len≤n)
mergesort-sorting-fuel n [] len≤n = []
mergesort-sorting-fuel n (x ∷ []) len≤n = [] ∷ []
mergesort-sorting-fuel (suc n) xs@(x ∷ y ∷ tl) len≤n =
  let
    (x∷l , y∷r) = split xs
    lenl = length x∷l
    lenr = length y∷r

    liml = split-fst-decr x y tl
    limr = split-snd-decr x y tl

    liml≤n = ≤-pred (≤-trans liml len≤n)
    limr≤n = ≤-pred (≤-trans limr len≤n)

    merge-l  = mergesort-fuel n x∷l liml≤n
    merge-r  = mergesort-fuel n y∷r limr≤n

    IHl = mergesort-sorting-fuel n x∷l liml≤n
    IHr = mergesort-sorting-fuel n y∷r limr≤n

    correct : sorted (merge' merge-l merge-r)
    correct = merge'-sorted merge-l merge-r IHl IHr

    output= : merge' merge-l merge-r ≡ mergesort-fuel (suc n) xs len≤n
    output= = mergesort-fuel-consistent (suc n) (suc n) xs len≤n len≤n

    ok : sorted (mergesort-fuel (suc n) xs len≤n)
    ok = subst sorted output= correct
  in ok

mergesort-sorting : (l : List ℕ) → sorted (mergesort' l)
mergesort-sorting l = let n = length l
                       in mergesort-sorting-fuel n l (≤-refl n)


-- well-founded relation


Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- x is accessible if-and-only-if forall y such that y < x, y is accessible.
-- Base case: x is accessible when forall (y : A) ¬ (y < x) or equivalently, x is the minimum element of A
data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (_<_ : Rel A) → Set
WellFounded {A} _<_ = (x : A) → Acc _<_ x

≤-< : {m n : ℕ} → (m ≤ n) → m ≡ n ∨ m < n
≤-< {zero} {zero} z≤n = left refl
≤-< {zero} {suc n} z≤n = right z<s
≤-< {suc m} {suc n} (s≤s m≤n)
  with ≤-< m≤n
... | left  m=n = left  (cong suc m=n)
... | right m<n = right (s<s m<n)

<-last : {m n : ℕ} → (m < suc n) → m ≡ n ∨ m < n
<-last {m} {n} m<sn
  with ≤-< m<sn
... | left  sm=sn = left (cong pred sm=sn)
... | right sm<sn = right (<-pred sm<sn)

wfNat-lim : (n : ℕ) (x : ℕ) → (x≤n : x ≤ n) → Acc {ℕ} _<_ x
wfNat-lim n zero z≤n = acc λ { y () }
wfNat-lim (suc n) (suc x) (s≤s x≤n) = acc g
  where g : (m : ℕ) → (m<sn : m < suc x) → Acc {ℕ} _<_ m
        g m m<sn with <-last m<sn
        ...        | left  m=n = let m≤n = subst (_≤ n) (sym m=n) x≤n
                                  in wfNat-lim n m m≤n
        ...        | right m<n = let m≤n = ≤-trans (≤-pred m<sn) x≤n
                                  in wfNat-lim n m m≤n

wfNat : WellFounded {ℕ} _<_
wfNat n = wfNat-lim n n (≤-refl n)

-- well-founded induction version of mergesort
mergesort-wf : (l : List ℕ) → Acc {ℕ} _<_ (length l) → List ℕ
mergesort-wf [] ac = []
mergesort-wf (x ∷ []) ac = x ∷ []
mergesort-wf xs@(x ∷ y ∷ tl) (acc get-acc) = let (l , r) = split xs
                                                 l<n = split-fst-decr x y tl
                                                 r<n = split-snd-decr x y tl
                                                 acc-l = get-acc (length l) l<n
                                                 acc-r = get-acc (length r) r<n
                                              in merge' (mergesort-wf l acc-l) (mergesort-wf r acc-r)

-- proving the correctness of the well-founded induction version
mergesort-wf-sorting : (l : List ℕ) → (ac : Acc {ℕ} _<_ (length l)) → sorted (mergesort-wf l ac)
mergesort-wf-sorting [] ac = []
mergesort-wf-sorting (x ∷ []) ac = [] ∷ []
mergesort-wf-sorting xs@(x ∷ y ∷ tl) (acc get-acc) = let (l , r) = split xs
                                                         l<n = split-fst-decr x y tl
                                                         r<n = split-snd-decr x y tl
                                                         acc-l = get-acc (length l) l<n
                                                         acc-r = get-acc (length r) r<n
                                                      in merge'-sorted (mergesort-wf l acc-l)
                                                                       (mergesort-wf r acc-r)
                                                                       (mergesort-wf-sorting l acc-l)
                                                                       (mergesort-wf-sorting r acc-r)

mergesort'' : List ℕ → List ℕ
mergesort'' l = let n = length l in mergesort-wf l (wfNat n)

mergesort''-sorting : (l : List ℕ) → sorted (mergesort'' l)
mergesort''-sorting l = let n = length l in mergesort-wf-sorting l (wfNat n)


-- Prove that insertion sort only permutate the input list and never add/remove/modify any element.

-- xs ~ ys if-and-only-if ys is a permutation of xs
data _~_ {A : Set} : List A → List A → Set where
  ~-nil : [] ~ []
  ~-drop : (x : A) {l l' : List A} → l ~ l' → (x ∷ l) ~ (x ∷ l')
  ~-swap : (x y : A) (l : List A) → (x ∷ y ∷ l) ~ (y ∷ x ∷ l)
  ~-trans : {l l' l'' : List A} → l ~ l' → l' ~ l'' → l ~ l''

~-refl : {A : Set} {l : List A} → l ~ l
~-refl {A} {[]} = ~-nil
~-refl {A} {x ∷ l} = ~-drop x (~-refl {A} {l})

~-sym : {A : Set} {l l' : List A} → l ~ l' → l' ~ l
~-sym ~-nil = ~-nil
~-sym (~-drop x l~l') = ~-drop x (~-sym l~l')
~-sym (~-swap x y l) = ~-swap y x l
~-sym (~-trans l~l' l~l'') = ~-trans (~-sym l~l'') (~-sym l~l')


-- (z ∷ x ∷ l) ~ (x ∷ z ∷ l) ~ (x ∷ (insert z l))
insert-~ : (x : ℕ) (l : List ℕ) → (x ∷ l) ~ (insert x l)
insert-~ z [] = ~-refl
insert-~ z (x ∷ [])
  with z ≤? x
... | left  z≤x = ~-refl
... | right x≤z = ~-swap z x []
insert-~ z (x ∷ l)
  with z ≤? x
... | left  z≤x = ~-refl
... | right x≤z = let IH = insert-~ z l
                      z:x:l~x:z:l = ~-swap z x l
                      x:z:l~x:ins-z-l = ~-drop x IH
                   in ~-trans z:x:l~x:z:l x:z:l~x:ins-z-l

-- (x ∷ l)  ~ insert x l
-- (x ∷ l') ~ insert x l'
-- l ~ l' ⊢ (x ∷ l) ~ (x ∷ l')
~-insert : (x : ℕ) {l l' : List ℕ} → l ~ l' → insert x l ~ insert x l'
~-insert x {l} {l'} l~l' = let x:l~ins   = insert-~ x l
                               ins~x:l   = ~-sym x:l~ins
                               x:l~x:l'  = ~-drop x l~l'
                               x:l'~ins' = insert-~ x l'
                            in ~-trans ins~x:l (~-trans x:l~x:l' x:l'~ins')

-- ⊢ (x ∷ l) ~ insert x l
-- l ~ sort l ⊢ insert x l ~ insert x (sort l)
sort-~ : (l : List ℕ) → l ~ (sort l)
sort-~ [] = ~-nil
sort-~ (x ∷ l) = let IH = sort-~ l
                  in ~-trans (insert-~ x l) (~-insert x IH)
