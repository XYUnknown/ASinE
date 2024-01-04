{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Primitives where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)
open import Arithmetic using (eq-slide)


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

slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {A : Set} → Vec A (sz + n · (suc sp)) → Vec (Vec A sz) (suc n)
slide {zero} sz sp {A} xs = subst (Vec A) (+-comm sz zero) xs ∷ []
slide {suc n} sz sp {A} xs = take sz xs ∷ slide {n} sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs))
