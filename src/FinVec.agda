{-# OPTIONS --cubical #-}

module FinVec where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)

VecRep : Set → ℕ → Set
VecRep A n = Fin n → A

_·f_ : {n : ℕ} → Fin n → (m : ℕ) → Fin (n · (suc m))
_·f_ {n} (fst , snd) m = fst · (suc m) , <-·sk snd

eq-tiling : (n m sz sp : ℕ) → sz + n · suc sp + m · suc (n + sp + n · sp) ≡ sz + (n + m · suc n) · suc sp
eq-tiling n m sz sp = sz + n · suc sp + m · suc (n + sp + n · sp)
  ≡⟨ cong (λ y → sz + n · suc sp + m · suc (y + n · sp)) (+-comm n sp) ⟩
    sz + n · suc sp + m · (suc sp + n + n · sp)
  ≡⟨ cong (λ y → sz + n · suc sp + m · y) (sym (+-assoc (suc sp) n (n · sp))) ⟩
    sz + n · suc sp + m · (suc sp + (n + n · sp))
  ≡⟨ cong (λ y → sz + n · suc sp + m · (suc sp + y)) (sym (·-suc n sp)) ⟩
    sz + n · suc sp + m · (suc sp + n · suc sp)
  ≡⟨ cong (λ y → sz + n · suc sp + m · (suc sp + y)) (·-comm n (suc sp)) ⟩
    sz + n · suc sp + m · (suc sp + suc sp · n)
  ≡⟨ cong₂ (λ y z → sz + y + z) (·-comm n (suc sp)) (·-comm m (suc sp + suc sp · n)) ⟩
    sz + suc sp · n + (suc sp + suc sp · n) · m
  ≡⟨ cong (λ y → sz + suc sp · n + y) (sym (·-distribʳ (suc sp) (suc sp · n) m)) ⟩
    sz + suc sp · n + (suc sp · m + suc sp · n · m)
  ≡⟨ sym (+-assoc sz (suc sp · n) (suc sp · m + suc sp · n · m)) ⟩
    sz + (suc sp · n + (suc sp · m + suc sp · n · m))
  ≡⟨ cong (sz +_) (+-assoc (suc sp · n) (suc sp · m) (suc sp · n · m)) ⟩
    sz + (suc sp · n + suc sp · m + suc sp · n · m)
  ≡⟨ cong (λ y → sz + (y + suc sp · n · m)) (·-distribˡ (suc sp) n m) ⟩
    sz + (suc sp · (n + m) + suc sp · n · m)
  ≡⟨ cong (λ y → sz + (suc sp · (n + m) + y)) (sym (·-assoc (suc sp) n m)) ⟩
    sz + (suc sp · (n + m) + suc sp · (n · m))
  ≡⟨ cong (sz +_) (·-distribˡ (suc sp) (n + m) (n · m)) ⟩
    sz + suc sp · (n + m + n · m)
  ≡⟨ cong (sz +_ ) (·-comm (suc sp) (n + m + n · m)) ⟩
    sz + (n + m + n · m) · suc sp
  ≡⟨ cong (λ y → sz + y · suc sp) (sym (+-assoc n m (n · m))) ⟩
    sz + (n + (m + n · m)) · suc sp
  ≡⟨ cong (λ y → sz + (n + (m + y)) · suc sp) (·-comm n m) ⟩
    sz + (n + (m + m · n)) · suc sp
  ≡⟨ cong (λ y → sz + (n + y) · suc sp) (sym (·-suc m n)) ⟩
    refl


map : {A B : Set} → ∀ {n} (f : A → B) → VecRep A n → VecRep B n
map f xs = λ idx → f (xs idx)

join : {n m : ℕ} {A : Set} → VecRep (VecRep A n) m → VecRep A (m · n)
join {n} {m} xs idx = let p = Iso.inv (equivToIso factorEquiv) idx in xs (fst p) (snd p)

take : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A n
take n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inl idx))

drop : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A m
drop n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inr idx))

slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {A : Set} → VecRep A (sz + n · (suc sp)) → VecRep (VecRep A sz) (suc n)
slide {n} sz sp xs (fst₁ , snd₁) (fst₂ , snd₂) = xs (fst₂ + fst₁ · (suc sp) , <-+-≤ snd₂ (≤-·k (pred-≤-pred snd₁)))

slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : VecRep A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (VecRep A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : VecRep A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
slideJoin {n} {m} {A} sz sp xs = {!!}
