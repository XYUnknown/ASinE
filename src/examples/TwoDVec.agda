{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_; ++-assoc)
open import Cubical.Data.Fin.Recursive
open import Cubical.Relation.Nullary

private
  variable
    n m o : ℕ
    ℓ ℓ' : Level
    A B : Type ℓ

-- Alternative vector representation

VecRep : (A : Type ℓ) → ℕ → Type ℓ
VecRep A n = Fin n → A

-- Isomorphism

toRep : ∀ {n} → Vec A n → VecRep A n
toRep [] = λ ()
toRep (x ∷ xs) = λ { zero → x
                   ; (suc n) → toRep xs n }

fromRep : ∀ {n} → VecRep A n → Vec A n
fromRep {n = zero} xs = []
fromRep {n = suc n} xs = xs zero ∷ (fromRep (λ x → xs (suc x)))

toRep-fromRep : ∀ {n} (xs : VecRep A n) → toRep (fromRep xs) ≡ xs
toRep-fromRep {n = zero} xs i ()
toRep-fromRep {n = suc n} xs i zero = xs zero
toRep-fromRep {n = suc n} xs i (suc m) = toRep-fromRep {n = n} (λ n → xs (suc n)) i m

fromRep-toRep : ∀ {n} (xs : Vec A n) → fromRep (toRep xs) ≡ xs
fromRep-toRep [] = refl
fromRep-toRep (x ∷ xs) i = x ∷ fromRep-toRep xs i

Iso-Vec-VecRep : ∀ {n} → Iso (Vec A n) (VecRep A n)
Iso-Vec-VecRep = iso toRep fromRep toRep-fromRep fromRep-toRep

Vec≃VecRep : Vec A n ≃ VecRep A n
Vec≃VecRep = isoToEquiv Iso-Vec-VecRep

Vec≡VecRep : Vec A n ≡ VecRep A n
Vec≡VecRep = ua Vec≃VecRep

-- operations for Vec

uncons : Vec A (suc n) → A × Vec A n
uncons (x ∷ xs) = x , xs

-- operations for VecRep

[]ʳ : VecRep A zero
[]ʳ = λ ()

consʳ : A → VecRep A n → VecRep A (suc n)
consʳ x xs zero = x
consʳ x xs (suc i) = xs i

headʳ : VecRep A (suc n) → A
headʳ xs = xs zero

tailʳ : VecRep A (suc n) → VecRep A n
tailʳ xs x = xs (suc x)

unconsʳ : VecRep A (suc n) → A × (VecRep A n)
unconsʳ xs = headʳ xs , tailʳ xs

-- classifying structure

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

-- We can define operations on 2 dimensional vectors, and again we will get the
-- concrete definitions for free. Note how we need to be careful how we set up our types
-- here keep the universe levels in check, i.e. we cant paramitise V₁/V₂ (our polymorphic
-- vector parameter) on the type of the container.

module Vec₂Str (A : Type ℓ) {V₁ : ℕ → Type ℓ} {V₂ : ℕ → ℕ → Type ℓ}
  (S₁ : VecStr A V₁) (S₂ : (m : ℕ) → VecStr (V₁ m) (V₂ m)) where

  divideᵛ : V₁ (m · n) → V₂ n m
  divideᵛ {zero} {n} xs = VecStr.[]ᵛ (S₂ n)
  divideᵛ {suc m} {n} xs with VecStr.splitAtᵛ S₁ n xs
  ... | ys , zs = VecStr.consᵛ (S₂ n) ys (divideᵛ zs)

-- Now we provide concrete definitions for the primitive operations for each vector
-- implementation

Vec-str : {A : Type ℓ} → VecStr A (Vec A)
VecStr.[]ᵛ (Vec-str) = []
VecStr.consᵛ (Vec-str) = _∷_
VecStr.unconsᵛ (Vec-str) = uncons

VecRep-str : {A : Type ℓ} → VecStr A (VecRep A)
VecStr.[]ᵛ VecRep-str = []ʳ
VecStr.consᵛ VecRep-str = consʳ
VecStr.unconsᵛ VecRep-str = unconsʳ

-- We never defined a concrete definition for _++_ for either Vec or VecRep, but now we
-- have access to all the operations we defined on the VecStr module for any vector
-- representation!

module _ {A : Type ℓ} where
  -- _++ʳ_ : VecRep A n → VecRep A m → VecRep A (n + m)
  _++ʳ_ = VecStr._++ᵛ_ (VecRep-str {A = A})

-- Form a minmal connect graph of structure identity proofs for each vector implementation
-- i.e. we are free to do this proof for any two representations, so long as there is a
-- chain of proofs from any one representation to the other

toRep-[] : toRep {A = A} [] ≡ []ʳ
toRep-[] = refl

toRep-cons : ∀ x (xs : Vec A n) → toRep (x ∷ xs) ≡ consʳ x (toRep xs)
toRep-cons x xs i zero = x
toRep-cons x xs i (suc n) = toRep xs n

VecStrEq : PathP (λ i → VecStr A (λ n → Vec≡VecRep {A = A} {n} i)) Vec-str VecRep-str
VecStr.[]ᵛ (VecStrEq {A = A} i) = ua-gluePath (Vec≃VecRep {A = A} {0}) {x = []} (toRep-[] {A = A}) i
VecStr.consᵛ (VecStrEq {A = A} i) {n} = λ x → ua→ {e = Vec≃VecRep {A = A} {n}} {f₁ = consʳ x} (λ xs →
  ua-gluePath (Vec≃VecRep {A = A} {suc n}) {x = x ∷ xs} (toRep-cons x xs)) i
VecStr.unconsᵛ (VecStrEq {A = A} i) {n} =
  ua→ {e = Vec≃VecRep {A = A} {suc n}} {B = λ i → A × (Vec≡VecRep i) } {f₀ = uncons} {f₁ = unconsʳ}
    (λ { (x ∷ xs) j → x , ua-gluePath (Vec≃VecRep {A = A} {n}) {x = xs} refl j }) i

-- Now we can do the same for proofs, first the specification

record vec-proofs
  (A : Type ℓ) {V₁ : ℕ → Type ℓ} {V₂ : ℕ → ℕ → Type ℓ}
  (S₁ : VecStr A V₁) (S₂ : (m : ℕ) → VecStr (V₁ m) (V₂ m)) : Type ℓ where
  open VecStr S₁
  open Vec₂Str A S₁ S₂

  field
    split-++ : ∀ {n m} (xs : V₁ n) (ys : V₁ m) → splitAtᵛ n (xs ++ᵛ ys) ≡ (xs , ys)

    rep-div-rep : ∀ {n} (xs : V₁ n)
      → divideᵛ (repeatᵛ m xs) ≡ VecStr.replicateᵛ (S₂ n) m xs

-- Now we need to give the proofs for a single representation. Note that you could divide
-- the record above into smaller specs, then you are free to choose the representation that
-- is easiest to prove a given (set of) properties. But every properties need only have a
-- single concrete proof.

vec-proofs-Vec : vec-proofs A Vec-str λ n → Vec-str
vec-proofs-Vec {A = A} = record { split-++ = split-++ ; rep-div-rep = rep-div-rep }
  where
  open VecStr (Vec-str {A = A})

  split-++ : ∀ {n m} (xs : Vec A n) (ys : Vec A m) → splitAtᵛ n (xs ++ᵛ ys) ≡ (xs , ys)
  split-++ [] ys = refl
  split-++ {n = suc n} (x ∷ xs) ys with splitAtᵛ n (xs ++ᵛ ys) | split-++ xs ys
  ... | xs₁ , xs₂ | p = λ i → (x ∷ proj₁ (p i)) , proj₂ (p i)

  rep-div-rep : {m n : ℕ} (xs : Vec A n) →
      Vec₂Str.divideᵛ A Vec-str (λ n₁ → Vec-str) (repeatᵛ m xs) ≡
      VecStr.replicateᵛ Vec-str m xs
  rep-div-rep {zero} xs = refl
  rep-div-rep {suc m} {n} xs with splitAtᵛ n (xs ++ᵛ repeatᵛ m xs) | split-++ xs (repeatᵛ m xs)
  ... | xs₁ , xs₂ | q = λ i → (proj₁ (q i)) ∷ lemma i
    where
    lemma : Vec₂Str.divideᵛ A Vec-str (λ n₁ → Vec-str) xs₂ ≡ VecStr.replicateᵛ Vec-str m xs
    lemma = cong (Vec₂Str.divideᵛ A Vec-str (λ n₁ → Vec-str)) (cong proj₂ q)
          ∙ rep-div-rep xs

-- Now we can transport to get proofs for all the properties for any representation for free!

vec-proofs-VecRep : vec-proofs A VecRep-str λ n → VecRep-str
vec-proofs-VecRep {A = A} = transport (λ i → vec-proofs A (VecStrEq i) λ m → VecStrEq i) vec-proofs-Vec

-- In summary:
--
-- We have n vector types: Vec₁, Vec₂, ..., Vec_n
--
-- For each type we have implementations for [], cons and uncons
--
-- n - 1 structure identity proofs of the form VecStr Vecᵢ ≡ VecStr Vecⱼ such that any
-- representation Vec_k there is a chain of proofs to an arbitary representation Vecᵤ:
-- VecStr Vec_k ≡ VecStr Vec_l, VecStr Vec_l ≡ VecStr Vec_m, ..., ≡ VecStr Vecᵤ
-- i.e. a connected acyclic graph
--
-- Now, for any vector operation we define on Vecᵢ, we can get an equivalent operation on
-- Vecⱼ for free via transport
--
-- Likewise, for an property of vectors, given a proof for one representation, we can get
-- a proof for all other representations via transport
