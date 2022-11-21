{-# OPTIONS --cubical #-}

module StencilRules where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Arithmetic using (eq-tiling; eq-slide)
open import Primitives
import Cubical.Data.Equality as Eq
import FinVec as Fv

map-++ : {n m : ℕ} → {s t : Set} → (f : s → t) → (xs₁ : Vec s n) → (xs₂ : Vec s m) →
         map f (xs₁ ++ xs₂) ≡ map f xs₁ ++ map f xs₂
map-++ f [] xs₂ = refl
map-++ f (x ∷ xs₁) xs₂ = cong (f x  ∷_) (map-++ f xs₁ xs₂)

joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
                 (f : s → t) → (xs : Vec (Vec s n) m) →
                 map f (join xs) ≡ join (map (map f) xs)
joinBeforeMapF f [] = refl
joinBeforeMapF f (xs ∷ xs₁) =
    map f (xs ++ join (xs₁))
  ≡⟨ map-++ f xs (join xs₁) ⟩
    map f xs ++ map f (join xs₁)
  ≡⟨ cong (map f xs ++_) (joinBeforeMapF f xs₁) ⟩
    refl

mapMapFBeforeJoin : {s : Set} → {t : Set} → {m n : ℕ} →
                    (f : s → t) → (xs : Vec (Vec s n) m) →
                    join (map (map f) xs) ≡ map f (join xs)
mapMapFBeforeJoin f xs = sym (joinBeforeMapF f xs)

eq-comm-+ : {A : Set} (n m : ℕ) → Vec A (n + m) ≡ Vec A (m + n)
eq-comm-+ {A} n m = cong (Vec A) (+-comm n m)

map' : {A B : Set} → ∀ {n} (f : A → B) → Vec A n → Vec B n
map' {A = A} {B = B} {n = n} f = transport (λ i → Fv.Vec≡VecRep {A = A} n (~ i) → Fv.Vec≡VecRep {A = B} n (~ i)) (Fv.map f)

transportUAop : (A B : Set)  {C D : Set → Set} → (e : ∀ T → C T ≃ D T) (f : C A → C B) (x : D A)
               → transport (λ i → ua (e A) i → ua (e B) i) f x ≡ equivFun (e B) (f (invEq (e A) x))
transportUAop A B e f x i = transportRefl (equivFun (e B) (f (invEq (e A) (transportRefl x i)))) i


map'≡map : {A B : Set} → {n : ℕ} → (f : A → B) → (xs : Vec A n) → map' f xs ≡ map f xs
map'≡map f [] = refl
map'≡map {A} {B} {n = suc n} f (x ∷ xs) = map' f (x ∷ xs)
  ≡⟨ transportUAop {!!} {!!} (λ T → (invEquiv (Fv.Vec≃VecRep _))) (Fv.map f) (x ∷ xs) ⟩
    {!!}

{- eq-tiling : (n m sz sp : ℕ) → sz + n · suc sp + m · suc (n + sp + n · sp) ≡ sz + (n + m · suc n) · suc sp
eq-tiling n zero sz sp =  (+-zero (sz + n · suc sp)) ∙ cong (λ y → sz + y · suc sp) (sym (+-zero n))
eq-tiling zero (suc m) sz sp =  cong (λ x → x + suc (sp + zero + m · suc (sp + zero))) (+-zero sz)
                             ∙  cong (λ x → sz + suc x) (cong₂ _+_ (+-zero sp) (cong₂ _·_ (sym (·-identityʳ m)) (cong suc (+-zero sp) ))) --
eq-tiling (suc n) (suc m) sz sp = {!!} -} -- sz + n · suc sp + suc (n + sp + n · sp + m · suc (n + sp + n · sp))
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

eq-slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs) Eq.≡
            join (map (λ (tile : Vec A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))

eq-slideJoin {n} {m} {A} sz sp xs = Eq.ap {!!} (Fv.eq-slideJoin {n} {m} {A} sz sp (Fv.Vec→VecRep xs))


slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : Vec A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))

slideJoin {n} {m} sz sp xs = Eq.eqToPath (eq-slideJoin {n} {m} sz sp xs)
{- slideJoin {n} {zero} {A} sz sp xs = slide sz sp (subst (Vec A) (eq-tiling n zero sz sp) xs)
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
    {!!}) -}

map-λ : {n m : ℕ} → {s t : Set} → (sz : ℕ) → (sp : ℕ) → (f : Vec s sz → Vec t sz) →
          (xs : Vec s (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
          map (λ (tile : Vec s (sz + n · (suc sp))) →
          map f (slide {n} sz sp tile)) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs) ≡
          map (map f) ((map (λ (tile : Vec s (sz + n · (suc sp))) →
          slide {n} sz sp tile)) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
map-λ {n} {zero} sz sp f xs = refl
map-λ {n} {suc m} {A} sz sp f xs =  map f (slide sz sp (take (sz + n · suc sp) xs)) ∷
      map (λ tile → map f (slide sz sp tile)) (slide (sz + n · suc sp) (n + sp + n · sp)
      (drop (suc (n + sp + n · sp)) (subst (Vec A) (eq-slide m (sz + n · suc sp) (n + sp + n · sp)) xs)))
  ≡⟨ cong (map f (slide sz sp (take (sz + n · suc sp) xs)) ∷_) (map-λ sz sp f (drop (suc (n + sp + n · sp))
     (subst (Vec A) (eq-slide m (sz + n · suc sp) (n + sp + n · sp)) xs))) ⟩
    refl


tiling : {n m : ℕ} → {A B : Set} → (sz sp : ℕ) → (f : Vec A sz → Vec B sz) →
         (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
         join (map (λ (tile : Vec A (sz + n · (suc sp))) →
         map f (slide {n} sz sp tile)) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs)) ≡ map f (slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs))
tiling {n} {m} {A} sz sp f xs = join (map (λ tile → map f (slide {n} sz sp tile)) (slide {m} (sz + n · suc sp) (n + sp + n · sp) xs))
  ≡⟨ cong join (map-λ {n} {m} sz sp f xs) ⟩
     join (map (map f) (map (slide {n} sz sp) (slide {m} (sz + n · suc sp) (n + sp + n · sp) xs)))
  ≡⟨ mapMapFBeforeJoin f (map (slide {n} sz sp) (slide {m} (sz + n · suc sp) (n + sp + n · sp) xs)) ⟩
     map f (join (map (slide {n} sz sp) (slide {m} (sz + n · suc sp) (n + sp + n · sp) xs)))
  ≡⟨ cong (map f) (sym (slideJoin {n} {m} {A} sz sp xs)) ⟩
    refl
