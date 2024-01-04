{-# OPTIONS --cubical #-}
module Example where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (∃; Σ-cong'; Σ≡Prop)
open import Cubical.Data.Empty as Empty using (⊥; rec)
import Cubical.Data.Equality as Eq
open import Arithmetic using (eq-tiling)

VecRep : Set → ℕ → Set
VecRep A n = Fin n → A

lookup : ∀ {n} {A : Set} → Fin n → Vec A n → A
lookup {zero} fin [] with ¬Fin0 fin
...                       | ()
lookup {suc n} (zero , snd) (x ∷ xs) = x
lookup {suc n} (suc fst , snd) (x ∷ xs) = lookup {n} (fst , (pred-≤-pred snd)) xs

order-irrelevant : {A : Set} {a : ℕ}{xs : VecRep A a}{i j : ℕ}{p₁ : i < a}{p₂ : j < a} → i ≡ j → xs (i , p₁) ≡ xs (j , p₂)
order-irrelevant {A}{a}{xs}{i}{j}{p₁}{p₂} e = cong (λ x → xs x) (Σ≡Prop (λ _ → isProp≤) e)

Vec→VecRep : {A : Set} {n : ℕ} → Vec A n → VecRep A n
Vec→VecRep xs f = lookup f xs

VecRep→Vec : {A : Set} {n : ℕ} → VecRep A n → Vec A n
VecRep→Vec {n = zero} xs = []
VecRep→Vec {n = suc n} xs = xs fzero ∷ VecRep→Vec λ x → xs (fsuc x)


VecRep→Vec→VecRep : {A : Set} {n : ℕ} (xs : VecRep A n) → Vec→VecRep (VecRep→Vec xs) ≡ xs
VecRep→Vec→VecRep {n = zero} xs = funExt λ f → Empty.rec (¬Fin0 f)
VecRep→Vec→VecRep {n = suc n} xs = funExt goal
  where
  goal : (f : Fin (suc n)) → Vec→VecRep (xs fzero ∷ VecRep→Vec (λ x → xs (fsuc x))) f ≡ xs f
  goal (zero , snd) = lookup (zero , snd) (xs fzero ∷ VecRep→Vec (λ x → xs (fsuc x)))
    ≡⟨ order-irrelevant {xs = xs} refl ⟩
      refl
  goal (suc fst , snd) = lookup (suc fst , snd) (xs fzero ∷ VecRep→Vec (λ x → xs (fsuc x)))
    ≡⟨⟩
      Vec→VecRep (VecRep→Vec (λ x → xs (fsuc x))) (fst , pred-≤-pred snd)
    ≡⟨ cong (λ y → y (fst , pred-≤-pred snd) ) (VecRep→Vec→VecRep (λ x → xs (fsuc x))) ⟩
       xs (fsuc (fst , pred-≤-pred snd))
    ≡⟨ order-irrelevant {xs = xs} refl ⟩
      refl

Vec→VecRep→Vec : {A : Set} {n : ℕ} (xs : Vec A n) → VecRep→Vec (Vec→VecRep xs) ≡ xs
Vec→VecRep→Vec {n = zero}  [] = refl
Vec→VecRep→Vec {n = suc n} (x ∷ xs) = lookup fzero (x ∷ xs) ∷ VecRep→Vec (λ x₁ → Vec→VecRep (x ∷ xs) (fsuc x₁))
  ≡⟨⟩
    x ∷ VecRep→Vec (λ x₁ → Vec→VecRep (x ∷ xs) (fsuc x₁))
  ≡⟨ cong (λ y → x ∷ VecRep→Vec y) (funExt λ xs₁ → Vec→VecRep (x ∷ xs) (fsuc xs₁)
    ≡⟨⟩
      lookup (fsuc xs₁) (x ∷ xs)
    ≡⟨⟩
      lookup (fst xs₁ , pred-≤-pred (snd (fsuc xs₁))) xs
    ≡⟨ order-irrelevant {xs = Vec→VecRep xs} refl ⟩
      lookup xs₁ xs
    ≡⟨⟩
      Vec→VecRep xs xs₁
    ≡⟨⟩
      refl) ⟩
     x ∷ VecRep→Vec (Vec→VecRep xs)
    ≡⟨ cong (x ∷_) (Vec→VecRep→Vec xs) ⟩
      refl

VecIsoVecRep : {A : Set} → (n : ℕ) → Iso (Vec A n) (VecRep A n)
VecIsoVecRep n = iso Vec→VecRep VecRep→Vec VecRep→Vec→VecRep Vec→VecRep→Vec

Vec≃VecRep : {A : Set} → (n : ℕ) → Vec A n ≃ VecRep A n
Vec≃VecRep n = isoToEquiv (VecIsoVecRep n)

Vec≡VecRep : {A : Set} → (n : ℕ) → Vec A n ≡ VecRep A n
Vec≡VecRep n = ua (Vec≃VecRep n)


mapVec : {A B : Set} → ∀ {n} (f : A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

mapVecRep : {A B : Set} → ∀ {n} (f : A → B) → VecRep A n → VecRep B n
mapVecRep f xs = λ idx → f (xs idx)

mapVec' : {A B : Set} → ∀ {n} (f : A → B) → Vec A n → Vec B n
mapVec' {A = A} {B = B} {n = n} f = transport (λ i → Vec≡VecRep {A = A} n (~ i) → Vec≡VecRep {A = B} n (~ i)) (mapVecRep f)

transportLem : (A B : Set)  {C D : Set → Set} → (e : ∀ T → C T ≃ D T) (f : C A → C B) (x : D A)
               → transport (λ i → ua (e A) i → ua (e B) i) f x ≡ equivFun (e B) (f (invEq (e A) x))
transportLem A B e f x i = transportRefl (equivFun (e B) (f (invEq (e A) (transportRefl x i)))) i

mapVec'≡mapVec : {A B : Set} → {n : ℕ} → (f : A → B) → (xs : Vec A n) → mapVec' f xs ≡ mapVec f xs
mapVec'≡mapVec f [] = refl
mapVec'≡mapVec {A} {B} {n = suc n} f (x ∷ xs) = mapVec' f (x ∷ xs)
  ≡⟨ transportLem {!!} {!!} (λ T → (invEquiv (Vec≃VecRep _))) (mapVecRep f) (x ∷ xs) ⟩
    {!!}
