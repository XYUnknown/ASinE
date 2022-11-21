{-# OPTIONS --cubical #-}

module Arithmetic where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

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
