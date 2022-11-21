{-# OPTIONS --cubical #-}

module StencilRules where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)

id : {T : Set} → T → T
id t = t

map : {A B : Set} → ∀ {n} (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

join : {n m : ℕ} {A : Set} → Vec (Vec A n) m → Vec A (m · n)
join {n} {zero} [] = []
join {n} {suc m} (xs ∷ xss) = xs ++ (join xss)


take : (n : ℕ) → {m : ℕ} → {A : Set} → Vec A (n + m) → Vec A n
take zero xs = []
take (suc n) {m} (x ∷ xs) = x ∷ (take n {m} xs)

drop : (n : ℕ) → {m : ℕ} → {A : Set} → Vec A (n + m) → Vec A m
drop zero xs = xs
drop (suc n) (x ∷ xs) = drop n xs

eq-comm-+ : {A : Set} (n m : ℕ) → Vec A (n + m) ≡ Vec A (m + n)
eq-comm-+ {A} n m = cong (Vec A) (+-comm n m)

eq-slide : (n sz sp : ℕ) → sz + suc (sp + n · suc sp) ≡ suc (sp + (sz + n · suc sp))
eq-slide n sz sp = sz + suc (sp + n · suc sp)
  ≡⟨ cong (sz +_) (+-assoc 1 sp (n · suc sp)) ⟩
    sz + (suc sp + n · suc sp)
  ≡⟨ +-assoc sz (suc sp) (n · suc sp) ⟩
    sz + suc sp + n · suc sp
  ≡⟨ cong (_+ n · suc sp) (+-comm sz (suc sp)) ⟩
    suc sp + sz + n · suc sp
  ≡⟨ cong (suc) (sym (+-assoc sp sz  (n · suc sp))) ⟩
    suc (sp + (sz + n · suc sp))
  ∎

eq-tiling : (n m sz sp : ℕ) → sz + n · suc sp + m · suc (n + sp + n · sp) ≡ sz + (n + m · suc n) · suc sp
eq-tiling n zero sz sp =  (+-zero (sz + n · suc sp)) ∙ cong (λ y → sz + y · suc sp) (sym (+-zero n))
eq-tiling zero (suc m) sz sp =  cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)
                             ∙  cong (λ x → sz + suc x) (cong₂ _+_ (+-zero sp) (cong₂ _·_ (sym (·-identityʳ m)) (cong suc (+-zero sp) ))) --
eq-tiling (suc n) (suc m) sz sp = {!!} -- sz + n · suc sp + suc (n + sp + n · sp + m · suc (n + sp + n · sp))
  -- ≡⟨⟩
  --  {!!}

{-
eq-tiling' : (n m sz sp : ℕ) → sz + n · suc sp + m · suc (n + sp + n · sp) ≡ sz + (n + m · suc n) · suc sp
eq-tiling' n m sz sp = sym (sz + (n + m · suc n) · suc sp
  ≡⟨ cong (sz +_) (sym (·-distribʳ n (m · suc n) (suc sp))) ⟩
    sz + (n · suc sp + m · suc n · suc sp)
  ≡⟨⟩
    {!!})
-}


map-take : {A B : Set} {n : ℕ} → (sz : ℕ) → (f : A → B) → (xs : Vec A (sz + n)) → map f (take sz xs) ≡ take sz (map f xs)
map-take zero f xs = refl
map-take (suc sz) f (x ∷ xs) = cong (f x ∷_) (map-take sz f xs)

map-drop : {A B : Set} {n : ℕ} → (sp : ℕ) → (f : A → B) → (xs : Vec A (sp + n)) → map f (drop sp xs) ≡ drop sp (map f xs)
map-drop zero f xs = refl
map-drop (suc sp) f (x ∷ xs) = map-drop sp f xs

++-[] : {n : ℕ} → {A : Set} → (xs : Vec A n) → xs ++ [] ≡ subst (Vec A) (λ i → +-zero n (~ i)) xs
++-[] {zero} {A} [] = sym (isSet-subst {A = ℕ} {B = Vec A} isSetℕ (λ i → zero) [])
++-[] {suc n} {A} (x ∷ xs) = sym (subst (Vec A) (λ i → suc (+-zero n (~ i))) (x ∷ xs)
  ≡⟨ substCommSlice (Vec A) (λ l → Vec A (suc l)) (λ _ → x ∷_) (λ i → +-zero n (~ i)) xs ⟩
    x ∷ (subst (Vec A) (λ i → +-zero n (~ i)) xs)
  ≡⟨ cong (x ∷_) (sym (++-[] xs))⟩
    refl)

slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {A : Set} → Vec A (sz + n · (suc sp)) → Vec (Vec A sz) (suc n)
slide {zero} sz sp {A} xs = subst (Vec A) (+-comm sz zero) xs ∷ []
slide {suc n} sz sp {A} xs = take sz xs ∷ slide {n} sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs))

slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {A B : Set} →
                     (f : A → B) → (xs : Vec A (sz + n · (suc sp))) →
                     map (map f) (slide {n} sz sp xs) ≡ slide {n} sz sp (map f xs)
slideBeforeMapMapF {zero} sz sp {A} {B} f xs = map (map f) (subst (Vec A) (+-zero sz) xs ∷ [])
  ≡⟨ cong (λ y → y ∷ []) (sym (substCommSlice (Vec A) (Vec B) (λ n → map f) (+-zero sz) xs)) ⟩
    refl
slideBeforeMapMapF {suc n} sz sp {A} {B} f xs = map f (take sz xs) ∷ map (map f) (slide sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs)))
  ≡⟨ cong (λ y → y ∷ map (map f) (slide sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs)))) (map-take sz f xs) ⟩
    take sz (map f xs) ∷ map (map f) (slide sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs)))
  ≡⟨ cong (λ y → take sz (map f xs) ∷ y) (slideBeforeMapMapF {n} sz sp f ((drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs))))⟩
    take sz (map f xs) ∷ slide sz sp (map f (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs)))
  ≡⟨ cong (λ y → take sz (map f xs) ∷ slide sz sp y) (map-drop (suc sp) f ((subst (Vec A) (eq-slide n sz sp) xs)) )⟩
    take sz (map f xs) ∷ slide sz sp (drop (suc sp) (map f (subst (Vec A) (eq-slide n sz sp) xs)))
  ≡⟨ cong (λ y → take sz (map f xs) ∷ y) (cong (λ y → slide sz sp y) (cong (λ y → drop (suc sp) y) (sym (substCommSlice (Vec A) (Vec B) (λ n → map f) (eq-slide n sz sp) xs)))) ⟩
    refl

slide-take-drop : {n m : ℕ} → {A : Set} → (sz sp : ℕ) → (xs : Vec A (sz + n · suc sp + suc (n + sp + n · sp + m · suc (n + sp + n · sp)))) →
  slide {n} sz sp (take (sz + n · suc sp) xs) ++ slide sz sp
    (subst (Vec A) (eq-tiling n m sz sp)
     (drop (suc (n + sp + n · sp))
      (subst (Vec A) (eq-slide m (sz + n · suc sp) (n + sp + n · sp))
       xs)))
    ≡ slide sz sp (subst (Vec A) (eq-tiling n (suc m) sz sp) xs)
slide-take-drop {zero} {m} {A} sz sp xs = subst (Vec A) (+-zero sz) (take (sz + zero) xs) ∷
    slide sz sp (subst (Vec A) (eq-tiling zero m sz sp) (drop (suc (sp + zero)) (subst (Vec A) (eq-slide m (sz + zero) (sp + zero)) xs)))
  ≡⟨ cong₂ _∷_ (substCommSlice (λ i →  (Vec A (i + _))) (Vec A) (λ n → take n) (+-zero sz) xs) refl ⟩
    take sz (subst (λ x → Vec A (x + suc (sp + zero + m · suc (sp + zero))))  (+-zero sz)  xs) ∷
    slide sz sp (subst (Vec A) (eq-tiling zero m sz sp) (drop (suc (sp + zero)) (subst (Vec A) (eq-slide m (sz + zero) (sp + zero)) xs)))
  ≡⟨⟩
    take sz (subst (Vec A) (cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)) xs) ∷
    slide sz sp (subst (Vec A) (eq-tiling zero m sz sp) (drop (suc (sp + zero)) (subst (Vec A) (eq-slide m (sz + zero) (sp + zero)) xs)))
  ≡⟨ cong₂ _∷_ (constSubstCommSlice (λ a → Vec A (sz + suc a)) (Vec A sz) (λ _ → take sz)
     (cong₂ _+_ (+-zero sp) (cong₂ _·_ (sym (·-identityʳ m)) (cong suc (+-zero sp) ))) ((subst (Vec A) (cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)) xs))) refl ⟩
    take sz (subst (Vec A) (cong (λ x → sz + suc x) (cong₂ _+_ (+-zero sp) (cong₂ _·_ (sym (·-identityʳ m)) (cong suc (+-zero sp) )))) (subst (Vec A) (cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)) xs)) ∷
    slide sz sp (subst (Vec A) (eq-tiling zero m sz sp) (drop (suc (sp + zero)) (subst (Vec A) (eq-slide m (sz + zero) (sp + zero)) xs)))
  ≡⟨ cong₂ _∷_ (cong (take sz)
     (sym (substComposite (Vec A) (cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)) (cong (λ x → sz + suc x) (cong₂ _+_ (+-zero sp) (cong₂ _·_ (sym (·-identityʳ m)) (cong suc (+-zero sp) )))) xs))) refl ⟩
    take sz (subst (Vec A) (eq-tiling zero (suc m) sz sp) xs) ∷
    slide sz sp (subst (Vec A) (eq-tiling zero m sz sp) (drop (suc (sp + zero)) (subst (Vec A) (eq-slide m (sz + zero) (sp + zero)) xs)))
  ≡⟨⟩
    {!!}


slide-take-drop {suc n} {m} {A} sz sp xs = {!!}

slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : Vec A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))


slideJoin {n} {zero} {A} sz sp xs = slide sz sp (subst (Vec A) (eq-tiling n zero sz sp) xs)
  ≡⟨ cong (λ y → slide {n + zero} sz sp y) (substComposite (Vec A) (+-zero (sz + n · suc sp)) (λ i₁ → sz + +-zero n (~ i₁) · suc sp) xs) ⟩
    slide sz sp (subst (Vec A) (λ i₁ → sz + +-zero n (~ i₁) · suc sp) (subst (Vec A) (+-zero (sz + n · suc sp)) xs))
  ≡⟨ sym (substCommSlice (λ l → Vec A (sz + l · (suc sp))) (λ l → Vec (Vec A sz) (suc l)) (λ _ → slide sz sp) (λ i → +-zero n (~ i)) (subst (Vec A) (+-zero (sz + n · suc sp)) xs)) ⟩
    subst (λ l → Vec (Vec A sz) (suc l)) (λ i → +-zero n (~ i)) (slide sz sp (subst (Vec A) (+-zero (sz + n · suc sp)) xs))
  ≡⟨ sym (++-[] (slide sz sp (subst (Vec A) (+-zero (sz + n · suc sp)) xs))) ⟩
    refl
slideJoin {n} {suc m} {A} sz sp xs = sym ( slide sz sp (take (sz + n · suc sp) xs) ++
    join (map (slide {n} sz sp) (slide {m} (sz + n · suc sp) (n + sp + n · sp) (drop (suc (n + sp + n · sp)) (subst (Vec A) (eq-slide m (sz + n · suc sp) (n + sp + n · sp)) xs))))
  ≡⟨ cong (slide sz sp (take (sz + n · suc sp) xs) ++_)
     (sym (slideJoin {n} {m} {A} sz sp (drop (suc (n + sp + n · sp)) (subst (Vec A) (eq-slide m (sz + n · suc sp) (n + sp + n · sp)) xs)))) ⟩
    {!!})

tiling : {n m : ℕ} → {A B : Set} → (sz sp : ℕ) → (f : Vec A sz → Vec B sz) →
         (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
         join (map (λ (tile : Vec A (sz + n · (suc sp))) →
         map f (slide {n} sz sp tile)) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs)) ≡ map f (slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs))
tiling = ?
