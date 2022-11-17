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
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (∃; Σ-cong'; Σ≡Prop)
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

join : {n m : ℕ} {A : Set} → VecRep (VecRep A n) m → VecRep A (m · n)
join {n} {m} xs (i , p) = xs (i / n , ord₁ p ) ( i % n , ord₂ {m}{n} p )

take : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A n
take n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inl idx))

drop : (n : ℕ) → {m : ℕ} → {A : Set} → VecRep A (n + m) → VecRep A m
drop n {m} xs idx = xs (Iso.inv (Fin+≅Fin⊎Fin n m) (inr idx))

slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {A : Set} → VecRep A (sz + n · (suc sp)) → VecRep (VecRep A sz) (suc n)
slide {n} sz sp xs (fst₁ , snd₁) (fst₂ , snd₂) = xs (fst₂ + fst₁ · (suc sp) , <-+-≤ snd₂ (≤-·k {fst₁}{n} (pred-≤-pred snd₁)))

order-irrelevant : {A : Set} {a : ℕ}{xs : VecRep A a}{i j : ℕ}{p₁ : i < a}{p₂ : j < a} → i ≡ j → xs (i , p₁) ≡ xs (j , p₂)
order-irrelevant {A}{a}{xs}{i}{j}{p₁}{p₂} e = cong (λ x → xs x) (Σ≡Prop (λ _ → isProp≤) e)

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
  ≡⟨ cong (f₂ +_) (cong ((f₁ % suc n) · (suc sp) +_) (·-assoc (f₁ / suc n) (suc n) (suc sp)))  ⟩ 
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
      xs ((f₂ + (f₁ % suc n) · (suc sp) ) + (f₁ / suc n) · (suc (n + sp + n · sp) ), <-+-≤ (<-+-≤ s₂ (≤-·k (pred-≤-pred ( ord₂ {suc m}{suc n} s₁)))) (≤-·k {f₁ / suc n }{m} (pred-≤-pred (ord₁ s₁))))
      ≡⟨⟩ 
      slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs (f₁ / suc n , ord₁ s₁ ) (f₂ + (f₁ % suc n) · (suc sp) , <-+-≤ s₂ (≤-·k (pred-≤-pred ( ord₂ {suc m}{suc n} s₁))))
      ≡⟨⟩
      slide  {n} sz sp (slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs (f₁ / suc n , ord₁ s₁ )) ( f₁ % suc n , ord₂ {suc m}{suc n} s₁) idx₂
      ≡⟨⟩
      join (map (slide  {n} sz sp) (slide  {m} (sz + n · suc sp) (n + sp + n · sp) xs)) idx₁ idx₂ 
      ≡⟨⟩ refl } }
  
