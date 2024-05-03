{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open Lift
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma using (∃; Σ-cong'; Σ≡Prop)
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Empty
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_; ++-assoc)
open import Cubical.Data.Fin.Recursive
open Isos
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as Empty using (⊥; rec)
open import Cubical.Data.Fin renaming (Fin to FinA)
open import Cubical.Data.Fin.Properties
open import Arithmetic using (eq-slide)

private
  variable
    n m o : ℕ
    T : Type
    ℓ ℓ' : Level
    A B : Type ℓ

-- missing properties of Vec
++-zero : ∀ (xs : Vec A n) → PathP (λ i → Vec A (+-zero n i)) (xs ++ []) xs
++-zero [] = refl
++-zero (x ∷ xs) i = x ∷ ++-zero xs i

-- The arithmetic representation of vec
VecRepA : Type ℓ → ℕ → Type ℓ
VecRepA A n = FinA n → A

lookup : ∀ {n : ℕ} → FinA n → Vec A n → A
lookup {n = zero} fin [] with ¬Fin0 fin
...                       | ()
lookup {n = suc n} (zero , snd) (x ∷ xs) = x
lookup {n = suc n} (suc fst , snd) (x ∷ xs) = lookup {n = n} (fst , (pred-≤-pred snd)) xs 


order-irrelevant : {A : Type ℓ} {a : ℕ}{xs : VecRepA A a}{i j : ℕ}{p₁ : i < a}{p₂ : j < a} → i ≡ j → xs (i , p₁) ≡ xs (j , p₂)
order-irrelevant {A = A}{a = a}{xs = xs}{i = i}{j = j}{p₁ = p₁}{p₂ = p₂} e = cong (λ x → xs x) (Σ≡Prop (λ _ → isProp≤) e)


Vec→VecRepA : {A : Type ℓ} {n : ℕ} → Vec A n → VecRepA A n
Vec→VecRepA xs f = lookup f xs

VecRepA→Vec : {A : Type ℓ} {n : ℕ} → VecRepA A n → Vec A n
VecRepA→Vec {n = zero} xs = []
VecRepA→Vec {n = suc n} xs = xs fzero ∷ VecRepA→Vec λ x → xs (fsuc x)

VecRepA→Vec→VecRepA : {A : Type ℓ} {n : ℕ} (xs : VecRepA A n) → Vec→VecRepA (VecRepA→Vec xs) ≡ xs
VecRepA→Vec→VecRepA {n = zero} xs = funExt λ f → Empty.rec (¬Fin0 f)
VecRepA→Vec→VecRepA {n = suc n} xs = funExt goal
  where
  goal : (f : FinA (suc n)) → Vec→VecRepA (xs fzero ∷ VecRepA→Vec (λ x → xs (fsuc x))) f ≡ xs f
  goal (zero , snd) = lookup (zero , snd) (xs fzero ∷ VecRepA→Vec (λ x → xs (fsuc x)))
    ≡⟨ order-irrelevant {xs = xs} refl ⟩
      refl
  goal (suc fst , snd) = lookup (suc fst , snd) (xs fzero ∷ VecRepA→Vec (λ x → xs (fsuc x)))
    ≡⟨⟩
      Vec→VecRepA (VecRepA→Vec (λ x → xs (fsuc x))) (fst , pred-≤-pred snd)
    ≡⟨ cong (λ y → y (fst , pred-≤-pred snd) ) (VecRepA→Vec→VecRepA (λ x → xs (fsuc x))) ⟩
       xs (fsuc (fst , pred-≤-pred snd))
    ≡⟨ order-irrelevant {xs = xs} refl ⟩
      refl

Vec→VecRepA→Vec : {A : Type ℓ} {n : ℕ} (xs : Vec A n) → VecRepA→Vec (Vec→VecRepA xs) ≡ xs
Vec→VecRepA→Vec {n = zero}  [] = refl
Vec→VecRepA→Vec {n = suc n} (x ∷ xs) = lookup fzero (x ∷ xs) ∷ VecRepA→Vec (λ x₁ → Vec→VecRepA (x ∷ xs) (fsuc x₁))
  ≡⟨⟩
    x ∷ VecRepA→Vec (λ x₁ → Vec→VecRepA (x ∷ xs) (fsuc x₁))
  ≡⟨ cong (λ y → x ∷ VecRepA→Vec y) (funExt λ xs₁ → Vec→VecRepA (x ∷ xs) (fsuc xs₁)
    ≡⟨⟩
      lookup (fsuc xs₁) (x ∷ xs)
    ≡⟨⟩
      lookup (fst xs₁ , pred-≤-pred (snd (fsuc xs₁))) xs
    ≡⟨ order-irrelevant {xs = Vec→VecRepA xs} refl ⟩
      lookup xs₁ xs
    ≡⟨⟩
      Vec→VecRepA xs xs₁
    ≡⟨⟩
      refl) ⟩
     x ∷ VecRepA→Vec (Vec→VecRepA xs)
    ≡⟨ cong (x ∷_) (Vec→VecRepA→Vec xs) ⟩
      refl

VecIsoVecRepA : Iso (Vec A n) (VecRepA A n)
VecIsoVecRepA = iso Vec→VecRepA VecRepA→Vec VecRepA→Vec→VecRepA Vec→VecRepA→Vec

Vec≃VecRepA :  Vec A n ≃ VecRepA A n
Vec≃VecRepA {n = n} = isoToEquiv (VecIsoVecRepA)

Vec≡VecRepA : Vec A n ≡ VecRepA A n
Vec≡VecRepA {n = n} = ua (Vec≃VecRepA)

-- operations for Vec
map : (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

uncons : Vec A (suc n) → A × Vec A n
uncons (x ∷ xs) = x , xs

-- operations for VecRepA
+-suc-zero : ∀ n → n + suc 0 ≡ suc n
+-suc-zero n = n + suc 0
 ≡⟨ +-suc n 0 ⟩
 suc (n + 0)
 ≡⟨ cong suc (+-zero n) ⟩
 refl

zero-< : 0 < suc n
zero-< {n} = n , +-suc-zero n

headᵃ : VecRepA A (suc n) → A
headᵃ xs = xs (zero , zero-<)

tailᵃ : VecRepA A (suc n) → VecRepA A n
tailᵃ xs (fst , snd) = xs (suc fst , suc-≤-suc snd)

[]ᵃ : VecRepA A zero
[]ᵃ idx with ¬Fin0 idx
... | ()

_∷ᵃ_ : A → VecRepA A n → VecRepA A (suc n)
(x ∷ᵃ xs) (zero , snd) = x
(x ∷ᵃ xs) (suc fst , snd) = xs (fst , pred-≤-pred snd)

unconsᵃ : VecRepA A (suc n) →  A × (VecRepA A n)
unconsᵃ xs = headᵃ xs , tailᵃ xs

mapᵃ : (f : A → B) → VecRepA A n → VecRepA B n
mapᵃ f xs = λ idx → f (xs idx)

record VecStr (A : Type ℓ) (V : ℕ → Type ℓ) : Type ℓ where
  field
    -- primitive operations for vectors (i.e. constructors and eliminators for Vec)
    -- these are the operations we need to implement for each vector representation
    []ᵛ : V 0
    consᵛ : A → V n → V (suc n)
    unconsᵛ : V (suc n) → A × V n

  -- now we can define vector operations in terms of the primitives
  -- we will get the concrete definitions for each representation for free!

  _++ᵛ_ : V n → V m → V (n + m)
  _++ᵛ_ {zero} xs ys = ys
  _++ᵛ_ {suc n} xs ys with unconsᵛ xs
  ... | x , xs = consᵛ x (xs ++ᵛ ys)

  splitAtᵛ : (n : ℕ) → V (n + m) → V n × V m
  splitAtᵛ zero xs = []ᵛ , xs
  splitAtᵛ (suc n) xs with unconsᵛ xs
  ... | x , xs with splitAtᵛ n xs
  ... | ys , zs = (consᵛ x ys) , zs

  replicateᵛ : (n : ℕ) → A → V n
  replicateᵛ zero x = []ᵛ
  replicateᵛ (suc n) x = consᵛ x (replicateᵛ n x)

  repeatᵛ : (m : ℕ) → V n → V (m · n)
  repeatᵛ zero xs = []ᵛ
  repeatᵛ (suc m) xs = xs ++ᵛ repeatᵛ m xs

-- We implement the str with two representations of vectors
Vec-str : {A : Type ℓ} → VecStr A (Vec A)
VecStr.[]ᵛ (Vec-str) = []
VecStr.consᵛ (Vec-str) = _∷_
VecStr.unconsᵛ (Vec-str) = uncons

VecRepA-str : {A : Type ℓ} → VecStr A (VecRepA A)
VecStr.[]ᵛ VecRepA-str = []ᵃ
VecStr.consᵛ VecRepA-str = _∷ᵃ_
VecStr.unconsᵛ VecRepA-str = unconsᵃ

