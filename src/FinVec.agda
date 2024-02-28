{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module FinVec where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
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

-- Isomorphism
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

Vec≃VecRep2D : {A : Set} → (n m : ℕ) → Vec (Vec A n) m ≃ VecRep (VecRep A n) m
Vec≃VecRep2D {A} n m = cong≃ (λ T → Vec T m) (Vec≃VecRep n)  ∙ₑ  Vec≃VecRep m -- pathToEquiv (Vec≡VecRep2D n m)

Vec≡VecRep2D : {A : Set} → (n m : ℕ) → Vec (Vec A n) m ≡ VecRep (VecRep A n) m
Vec≡VecRep2D {A} n m = ua (Vec≃VecRep2D n m)
{-
Vec (Vec A n) m
  ≡⟨ cong (λ T → Vec T m) (Vec≡VecRep n) ⟩
    Vec (VecRep A n) m
  ≡⟨ Vec≡VecRep {A = VecRep A n} m ⟩
    refl
-}

VecRepIsoVec : {A : Set} → (n : ℕ) → Iso (VecRep A n) (Vec A n)
VecRepIsoVec n = iso VecRep→Vec Vec→VecRep Vec→VecRep→Vec VecRep→Vec→VecRep

VecRep≃Vec : {A : Set} → (n : ℕ) → VecRep A n ≃ Vec A n
VecRep≃Vec n = isoToEquiv (VecRepIsoVec n)

VecRep≡Vec : {A : Set} → (n : ℕ) → VecRep A n ≡ Vec A n
VecRep≡Vec n = ua (VecRep≃Vec n)

VecRep≡Vec2D : {A : Set} → (n m : ℕ) → VecRep (VecRep A n) m ≡ Vec (Vec A n) m
VecRep≡Vec2D {A} n m = VecRep (VecRep A n) m
  ≡⟨ cong (λ T → VecRep T m) (VecRep≡Vec n) ⟩
    VecRep (Vec A n) m
  ≡⟨ VecRep≡Vec m ⟩
    refl

VecRep≃Vec2D : {A : Set} → (n m : ℕ) → VecRep (VecRep A n) m ≃ Vec (Vec A n) m
VecRep≃Vec2D n m = pathToEquiv (VecRep≡Vec2D n m)

_·f_ : {n : ℕ} → Fin n → (m : ℕ) → Fin (n · (suc m))
_·f_ {n} (fst , snd) m = fst · (suc m) , <-·sk snd

ord₁ : ∀{m n i} → i < m · n → (i / n) < m
ord₁ {m}{zero}{i} p with ¬-<-zero (subst (i <_)  (sym (0≡m·0 m)) p)
... | ()
ord₁ {m}{suc n}{i} p = mm<m
  where
    mm = i / suc n
    nn = i % suc n

    nmmoddiv : mm · suc n + nn ≡ i
    nmmoddiv = moddiv _ (suc n)
    nn<n : nn < suc n
    nn<n = n%sk<sk i _

    nmsnd : mm · suc n + nn < suc n · m
    nmsnd = subst (λ l → l < suc n · m) (sym nmmoddiv) (subst (i <_) (·-comm m (suc n)) p)
    mm·sn<m·sn : mm · suc n < m · suc n
    mm·sn<m·sn =
      mm · suc n      ≤<⟨ nn , +-comm nn (mm · suc n) ⟩
      mm · suc n + nn <≡⟨ nmsnd ⟩
      suc n · m       ≡⟨ ·-comm (suc n) m ⟩
      m · suc n       ∎ where open <-Reasoning
    mm<m : mm < m
    mm<m = <-·sk-cancel mm·sn<m·sn

ord₂' : ∀{n i} → n > 0 → i % n < n
ord₂' {zero} p with ¬m<m p
... | ()
ord₂' {suc n}{i} p = n%sk<sk i n


ord₂ : ∀{m n i} → i < m · n → i % n < n
ord₂ {n}{zero}{i} p with ¬-<-zero (subst (i <_)  (sym (0≡m·0 n)) p)
... | ()
ord₂ {m}{suc n}{i} p = n%sk<sk i n

order-lemma : ∀{m n i} → i < m · n → n > 0
order-lemma {m}{zero}{i} p with ¬-<-zero (subst (i <_) (sym (0≡m·0 m)) p)
... | ()
order-lemma {m}{suc n} p = suc-≤-suc (zero-≤)

-- Primitives
map : {A B : Set} → ∀ {n} (f : A → B) → VecRep A n → VecRep B n
map f xs = λ idx → f (xs idx)

join : {n m : ℕ} {A : Set} → VecRep (VecRep A n) m → VecRep A (m · n)
join {n} {m} xs (i , p) = xs (i / n , ord₁ p ) ( i % n , ord₂ {m}{n} p )

take : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A n
take n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inl idx))

drop : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A m
drop n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inr idx))

slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {A : Set} → VecRep A (sz + n · (suc sp)) → VecRep (VecRep A sz) (suc n)
slide {n} sz sp xs (fst₁ , snd₁) (fst₂ , snd₂) = xs (fst₂ + fst₁ · (suc sp) , <-+-≤ snd₂ (≤-·k {fst₁}{n} (pred-≤-pred snd₁)))

subst-VecRep-to-Fin : {A : Set} {a b : ℕ}{eq : a ≡ b}{xs : VecRep A a}
      → subst (VecRep A) eq xs ≡ xs ∘ (subst Fin (sym eq))
subst-VecRep-to-Fin {A}{a}{b}{e}{xs} i x = transportRefl (xs (transp (λ j → Fin (e (~ j))) i0 x)) i

lemma : {A : Set} {a b : ℕ}{eq : a ≡ b}{xs : VecRep A a}{i : ℕ}{p : i < b} → subst (VecRep A) eq xs (i , p) ≡ xs (i , subst (i <_) (sym eq) p)
lemma {A}{a}{b}{e}{xs}{i}{p} =
   (subst (VecRep A) e xs) (i , p)
   ≡⟨ cong (λ x -> x (i , p)) (subst-VecRep-to-Fin {eq = e}{xs = xs}) ⟩
   xs (subst Fin (sym e) (i , p))
   ≡⟨ cong xs (substCommSlice (i <_) Fin (λ a p′ → i , p′) (sym e) p) ⟩
   xs (i , subst (i <_) (sym e) p) ∎


expansion : ∀ (n m : ℕ) → suc (n + m + n · m) ≡ suc n · suc m
expansion n m = cong suc (
    n + m + n · m
    ≡⟨ cong (_+ n · m) (+-comm n m) ⟩
    m + n + n · m
    ≡⟨ sym (+-assoc m n (n · m)) ⟩
    m + (n + n · m)
    ≡⟨ cong (m +_) (cong (n +_) (·-comm n m)) ⟩
    m + suc m · n
    ≡⟨ cong (m +_) (·-comm (suc m) n) ⟩
    m + n · suc m ∎)

arithmetic : ∀ (f₁ f₂ sp n : ℕ) → f₂ + f₁ · (suc sp) ≡ (f₂ + (f₁ % suc n) · (suc sp) ) + (f₁ / suc n) · (suc (n + sp + n · sp) )
arithmetic f₁ f₂ sp n = sym (
  f₂ + (f₁ % suc n) · (suc sp) + (f₁ / suc n) · suc (n + sp + n · sp)
  ≡⟨ cong (λ x → f₂ + (f₁ % suc n) · (suc sp) + (f₁ / suc n) · x) (expansion n sp) ⟩
  f₂ + (f₁ % suc n) · (suc sp) + (f₁ / suc n) · (suc n · suc sp)
  ≡⟨ sym (+-assoc f₂ ((f₁ % suc n) · (suc sp)) ((f₁ / suc n) · (suc n · suc sp))) ⟩
  f₂ + ((f₁ % suc n) · (suc sp) + (f₁ / suc n) · (suc n · suc sp))
  ≡⟨ cong (f₂ +_) (cong ((f₁ % suc n) · (suc sp) +_) (·-assoc (f₁ / suc n) (suc n) (suc sp))) ⟩
  f₂ + ((f₁ % suc n) · (suc sp) + ((f₁ / suc n) · suc n) · suc sp)
  ≡⟨ cong (f₂ +_) (·-distribʳ (f₁ % suc n) ((f₁ / suc n) · suc n) (suc sp)) ⟩
  f₂ + ((f₁ % suc n) + ((f₁ / suc n) · suc n)) · suc sp
  ≡⟨ cong (f₂ +_) (cong (_· suc sp) (+-comm (f₁ % suc n) _)) ⟩
  f₂ + (((f₁ / suc n) · suc n) + (f₁ % suc n)) · suc sp
  ≡⟨ cong (f₂ +_) (cong (_· suc sp)  (moddiv f₁ (suc n))) ⟩
  f₂ + f₁ · (suc sp) ∎)


slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : VecRep A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (VecRep A) (eq-tiling n m sz sp) xs) ≡
            join (map (λ (tile : VecRep A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
slideJoin {n} {m} {A} sz sp xs = funExt λ { idx₁@(f₁ , s₁) → funExt λ { idx₂@(f₂ , s₂) →
      slide {n + m · (suc n)} sz sp (subst (VecRep A) (eq-tiling n m sz sp) xs) (f₁ , s₁) (f₂ , s₂)
      ≡⟨⟩
      subst (VecRep A) (eq-tiling n m sz sp) xs (f₂ + f₁ · (suc sp) , <-+-≤ s₂ (≤-·k (pred-≤-pred s₁)))
      ≡⟨ lemma {eq = eq-tiling n m sz sp}{xs}{f₂ + f₁ · suc sp}{<-+-≤ s₂ (≤-·k (pred-≤-pred s₁))} ⟩
      xs (f₂ + f₁ · (suc sp) , subst (f₂ + f₁ · (suc sp) <_) (sym  (eq-tiling n m sz sp)) (<-+-≤ s₂ (≤-·k (pred-≤-pred s₁))))
      ≡⟨ order-irrelevant {xs = xs} (arithmetic f₁ f₂ sp n ) ⟩
      xs ((f₂ + (f₁ % suc n) · (suc sp) ) + (f₁ / suc n) · (suc (n + sp + n · sp) ), <-+-≤ (<-+-≤ s₂ (≤-·k (pred-≤-pred ( ord₂ {suc m}{suc n} s₁))))
      (≤-·k {f₁ / suc n }{m} (pred-≤-pred (ord₁ s₁))))
      ≡⟨⟩
      slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs (f₁ / suc n , ord₁ s₁ ) (f₂ + (f₁ % suc n) · (suc sp) , <-+-≤ s₂ (≤-·k (pred-≤-pred ( ord₂ {suc m}{suc n} s₁))))
      ≡⟨⟩
      slide  {n} sz sp (slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs (f₁ / suc n , ord₁ s₁ )) ( f₁ % suc n , ord₂ {suc m}{suc n} s₁) idx₂
      ≡⟨⟩
      join (map (slide  {n} sz sp) (slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs)) idx₁ idx₂
      ≡⟨⟩ refl } }

eq-slideJoin : {n m : ℕ} → {A : Set} → (sz : ℕ) → (sp : ℕ) → (xs : VecRep A (sz + n · (suc sp) + m · suc (n + sp + n · sp))) →
            slide {n + m · (suc n)} sz sp (subst (VecRep A) (eq-tiling n m sz sp) xs) Eq.≡
            join (map (λ (tile : VecRep A (sz + n · (suc sp))) → slide {n} sz sp tile) (slide {m} (sz + n · (suc sp)) (n + sp + n · sp) xs))
eq-slideJoin {n} {m} sz sp xs = Eq.pathToEq (slideJoin {n} {m} sz sp xs)

{-
splitFin : {n : ℕ} → (m : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
splitFin zero fin = inr fin
splitFin (suc m) (zero , snd) = inl 0
splitFin (suc m) (suc fst , snd) with splitFin m (fst , (pred-≤-pred snd))
... | inl (fst₁ , snd₂) = inl (suc fst₁ , suc-≤-suc snd₂)
... | inr j = inr j

[]ʳ : {A : Set} → VecRep A zero
[]ʳ x  with ¬Fin0 x
...     | ()

_++ʳ_ : {A : Set} → {n m : ℕ} →  VecRep A n → VecRep A m → VecRep A (n + m)
_++ʳ_ {n = n} {m} xs ys x with splitFin n x
... | inl m = xs m
... | inr m = ys m


tailʳ : {A : Set} → {n : ℕ} → VecRep A (suc n) → VecRep A n
tailʳ xs (fst , snd) = xs (suc fst , suc-≤-suc snd)

tailʳ-++ʳ : {A : Set} → {n m : ℕ} → ∀ (xs : VecRep A (suc n)) (ys : VecRep A m) → tailʳ (xs ++ʳ ys) ≡ tailʳ xs ++ʳ ys
tailʳ-++ʳ {n = n} xs ys i x with splitFin n x
... | inl m = {!xs ?!}
... | inr m = {!ys ?!}
-}
