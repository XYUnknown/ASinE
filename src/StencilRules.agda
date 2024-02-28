{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module StencilRules where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv using ( funExtDep )
open import Arithmetic using (eq-tiling; eq-slide)
open import Cubical.Data.Empty as Empty using (⊥; rec)

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

{-
map' : {A B : Set} → ∀ {n} (f : A → B) → Vec A n → Vec B n
map' {A = A} {B = B} {n = n} f = transport (λ i → Fv.Vec≡VecRep {A = A} n (~ i) → Fv.Vec≡VecRep {A = B} n (~ i)) (Fv.map f)
-}

{-
transportUAop : (A B : Set)  {C D : Set → Set} → (e : ∀ T → C T ≃ D T) (f : C A → C B) (x : D A)
               → transport (λ i → ua (e A) i → ua (e B) i) f x ≡ equivFun (e B) (f (invEq (e A) x))
transportUAop A B e f x i = transportRefl (equivFun (e B) (f (invEq (e A) (transportRefl x i)))) i

map'≡map : {A B : Set} → {n : ℕ} → (f : A → B) → (xs : Vec A n) → map' f xs ≡ map f xs
map'≡map f [] = refl
map'≡map {A} {B} {n = suc n} f (x ∷ xs) = map' f (x ∷ xs)
  ≡⟨⟩
    {!!}
-}

-- Interface
{-
record VecStr (A : ℕ → Type) : Type where
  field
    []ᵛ : A 0
    _++ᵛ_ : {n m : ℕ} →  A n → A m → A (n + m)
-}


lemma1 : {A B : Set} → ∀ {n} (f : A → B) →
  ({x₀ : Vec A n} {x₁ : Fv.VecRep A n} → equivFun (Fv.Vec≃VecRep n) x₀ ≡ x₁ → equivFun (Fv.Vec≃VecRep n) (map f x₀) ≡ Fv.map f x₁) →
  PathP (λ i → Fv.Vec≡VecRep {A = A} n i → Fv.Vec≡VecRep {A = B} n i) (map f) (Fv.map f)
lemma1 {n = n} f hyp = funExtDep (λ {x₀} p i → ua-glue (Fv.Vec≃VecRep n) i (λ { (i = i0) → map f x₀ }) (inS (hyp (λ j → ua-unglue (Fv.Vec≃VecRep n) j (p j)) i)))

lemma2 : {A B : Set} → ∀ {n} (f : A → B) →
  ({x₀ : Vec A n} → equivFun (Fv.Vec≃VecRep n) (map f x₀) ≡ Fv.map f (equivFun (Fv.Vec≃VecRep n) x₀)) →
  ({x₀ : Vec A n} {x₁ : Fv.VecRep A n} → equivFun (Fv.Vec≃VecRep n) x₀ ≡ x₁ → equivFun (Fv.Vec≃VecRep n) (map f x₀) ≡ Fv.map f x₁)
lemma2 {n = n} f hyp {x₀} p = transp (λ i → equivFun (Fv.Vec≃VecRep n) (map f x₀) ≡ Fv.map f (p i)) i0 hyp

lemma3 : {A B : Set} → ∀ {n} (f : A → B) →
  (x₀ : Vec A n) → equivFun (Fv.Vec≃VecRep n) (map f x₀) ≡ Fv.map f (equivFun (Fv.Vec≃VecRep n) x₀)
lemma3 {n = .zero} f [] = funExt λ f → Empty.rec (¬Fin0 f)
lemma3 {n = suc n'} f (x ∷ x₀) = funExt λ { (zero , snd₁) → refl ; (suc i , snd₁) → cong (λ h → h (i , pred-≤-pred snd₁)) (lemma3 {n = n'} f x₀) }

mapVec≡mapVecRep : {A B : Set} → ∀ {n} (f : A → B) →
  PathP (λ i → Fv.Vec≡VecRep {A = A} n i → Fv.Vec≡VecRep {A = B} n i) (map f) (Fv.map f)
mapVec≡mapVecRep {n = n} f = lemma1 {n = n} f (lemma2 f (lemma3 f _))


lemma-join1 : {A : Set} → ∀ {n m} →
  ({x₀ : Vec (Vec A n) m} {x₁ : Fv.VecRep (Fv.VecRep A n) m} → equivFun (Fv.Vec≃VecRep2D n m) x₀ ≡ x₁ → equivFun (Fv.Vec≃VecRep (m · n)) (join x₀) ≡  Fv.join x₁) →
  PathP (λ i → Fv.Vec≡VecRep2D {A = A} n m i → Fv.Vec≡VecRep {A = A} (m · n) i) join Fv.join
lemma-join1 {A} {n = n} {m = m} hyp = funExtDep λ {x₀} p i → ua-glue (Fv.Vec≃VecRep {A = A} (m · n)) i (λ { (i = i0) → join x₀ })
     (inS (hyp {x₀} (λ j → ua-unglue (Fv.Vec≃VecRep2D {A = A} n m) j (p j)) i))

lemma-join2 : {A : Set} → ∀ {n m} →
  ({x₀ : Vec (Vec A n) m} → equivFun (Fv.Vec≃VecRep (m · n)) (join x₀) ≡ Fv.join (equivFun (Fv.Vec≃VecRep2D n m) x₀)) →
  ({x₀ : Vec (Vec A n) m} {x₁ : Fv.VecRep (Fv.VecRep A n) m} → equivFun (Fv.Vec≃VecRep2D n m) x₀ ≡ x₁ → equivFun (Fv.Vec≃VecRep (m · n)) (join x₀) ≡ Fv.join x₁)
lemma-join2 {n = n} {m = m} hyp {x₀} p  = transp (λ i → equivFun (Fv.Vec≃VecRep (m · n)) (join x₀) ≡ Fv.join (p i)) i0 hyp

lemma-join3 : {A : Set} → ∀ {n m} →
  (x₀ : Vec (Vec A n) m) → equivFun (Fv.Vec≃VecRep (m · n)) (join x₀) ≡ Fv.join (equivFun (Fv.Vec≃VecRep2D n m) x₀)
lemma-join3 {n = n} {m = .zero} [] = funExt λ f → Empty.rec (¬Fin0 f)
lemma-join3 {n = n} {m = suc m'} (x ∷ x₀) = funExt goal
  where
  goal : (x₁ : Fin (suc m' · n)) → (equivFun (Fv.Vec≃VecRep (suc m' · n)) (join (x ∷ x₀)) x₁) ≡ (Fv.join (equivFun (Fv.Vec≃VecRep2D n (suc m')) (x ∷ x₀)) x₁)
  goal (zero , snd) = {!!}
  goal (suc fst₁ , snd) = {!!}


joinVec≡joinVecRep : {A : Set} → ∀ {n m} → PathP (λ i → Fv.Vec≡VecRep2D {A = A} n m i → Fv.Vec≡VecRep {A = A} (m · n) i) (join) (Fv.join)
joinVec≡joinVecRep {n = n} {m = m} = lemma-join1 (lemma-join2 (lemma-join3 {n = n} {m = m} _))


slideVec≡slideVecRep : {A : Set} → ∀ {n} → (sz sp : ℕ) → PathP (λ i → Fv.Vec≡VecRep {A = A} (sz + n · (suc sp)) i → Fv.Vec≡VecRep2D {A = A} sz (suc n) i) (slide sz sp) (Fv.slide sz sp)
slideVec≡slideVecRep {n = n} sz sp = {!!}

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


map-id : {A : Set} → ∀ {n} →
  ((xs : Fv.VecRep A n) → Fv.map {n = n} (λ x → x) xs ≡ xs) →
  (xs : Vec A n) → map {n = n} (λ x → x) xs ≡ xs
map-id {A = A} {n = n} hyp =
  transp (λ i → (xs : Fv.Vec≡VecRep {A = A} n (~ i)) → mapVec≡mapVecRep (λ x → x) (~ i) xs ≡ xs) i0 hyp

{-
slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : Vec A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))

slideJoin {n} {m} sz sp xs = {!!}
-}

slideJoinTrans : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) →
            (
             (xs : Fv.VecRep A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
              Fv.slide {n + m · (suc n)} sz sp (subst (Fv.VecRep A) (eq-tiling n m sz sp) xs) ≡
              Fv.join (Fv.map (λ (tile : Fv.VecRep A (sz + n · (suc sp))) → Fv.slide {n} sz sp tile) (Fv.slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
            ) →
            (xs : Vec A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (Vec A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : Vec A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
slideJoinTrans {n} {m} {A} sz sp hyp = {!!}

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
  ≡⟨ cong (map f) (sym (slideJoinTrans {n} {m} {A} sz sp (Fv.slideJoin {n} {m} {A} sz sp) xs)) ⟩
    refl
