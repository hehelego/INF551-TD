data _≡_ : {A : Set} → A → A → Set where
  refl : {A : Set} (x : A) → x ≡ x

J : {A : Set}
    (P : (x y : A) (x=y : x ≡ y) → Set)
    (r : (t : A) → P t t (refl t))
    (x y : A) (x=y : x ≡ y)
    → P x y x=y
J P r .x .x (refl x) = r x

cong : {A B : Set} (f : A → B) (x y : A) → x ≡ y → f x ≡ f y
cong {A} f x y x=y = J P r x y x=y
  where
    P : (s t : A) → s ≡ t → Set
    P s t s=t = f s ≡ f t
    r : (t : A) → P t t (refl t)
    r t = refl (f t)


sym : {A : Set} (x y : A) → x ≡ y → y ≡ x
sym {A} x y x=y = J P r x y x=y
  where
    P : (s t : A) → s ≡ t → Set
    P s t s=t = t ≡ s
    r : (t : A) → P t t (refl t)
    r t = refl t

trans : {A : Set} (x y z : A) → x ≡ y → y ≡ z → x ≡ z
trans {A} x y z x=y y=z = J P r x y x=y y=z
  where 
    P : (s t : A) (s=t : s ≡ t) → Set
    P s t s=t = t ≡ z → s ≡ z
    r : (t : A) → P t t (refl t)
    r t t=z = t=z



