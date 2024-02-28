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
    A B T : Type

-- missing properties of Vec
++-zero : ∀ (xs : Vec A n) → PathP (λ i → Vec A (+-zero n i)) (xs ++ []) xs
++-zero [] = refl
++-zero (x ∷ xs) i = x ∷ ++-zero xs i


-- The arithmetic representation of vec
VecRepA : Set → ℕ → Set
VecRepA A n = FinA n → A

lookup : ∀ {n} {A : Set} → FinA n → Vec A n → A
lookup {zero} fin [] with ¬Fin0 fin
...                       | ()
lookup {suc n} (zero , snd) (x ∷ xs) = x
lookup {suc n} (suc fst , snd)  (x ∷ xs) = lookup {n} (fst , (pred-≤-pred snd)) xs

order-irrelevant : {A : Set} {a : ℕ}{xs : VecRepA A a}{i j : ℕ}{p₁ : i < a}{p₂ : j < a} → i ≡ j → xs (i , p₁) ≡ xs (j , p₂)
order-irrelevant {A}{a}{xs}{i}{j}{p₁}{p₂} e = cong (λ x → xs x) (Σ≡Prop (λ _ → isProp≤) e)

Vec→VecRepA : {A : Set} {n : ℕ} → Vec A n → VecRepA A n
Vec→VecRepA xs f = lookup f xs

VecRepA→Vec : {A : Set} {n : ℕ} → VecRepA A n → Vec A n
VecRepA→Vec {n = zero} xs = []
VecRepA→Vec {n = suc n} xs = xs fzero ∷ VecRepA→Vec λ x → xs (fsuc x)

VecRepA→Vec→VecRepA : {A : Set} {n : ℕ} (xs : VecRepA A n) → Vec→VecRepA (VecRepA→Vec xs) ≡ xs
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

Vec→VecRepA→Vec : {A : Set} {n : ℕ} (xs : Vec A n) → VecRepA→Vec (Vec→VecRepA xs) ≡ xs
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

-- VecRepA helpers
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

-- operations for Vec
map : (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

join : Vec (Vec A n) m → Vec A (m · n)
join [] = []
join (x ∷ xs) = x ++ join xs

take : (n : ℕ) → {m : ℕ} → {A : Set} → Vec A (n + m) → Vec A n
take zero xs = []
take (suc n) {m} (x ∷ xs) = x ∷ (take n {m} xs)

drop : (n : ℕ) → {m : ℕ} → {A : Set} → Vec A (n + m) → Vec A m
drop zero xs = xs
drop (suc n) (x ∷ xs) = drop n xs

slide : (sz : ℕ) → (sp : ℕ) → Vec A (sz + n · (suc sp)) → Vec (Vec A sz) (suc n)
slide {A = A} {n = zero} sz sp xs = subst (Vec A) (+-comm sz zero) xs ∷ []
slide  {A = A} {n = suc n} sz sp xs = take sz xs ∷ slide sz sp (drop (suc sp) (subst (Vec A) (eq-slide n sz sp) xs))

-- operations for VecRepA

tailᵃ : VecRepA A (suc n) → VecRepA A n
tailᵃ xs (fst , snd) = xs (suc fst , suc-≤-suc snd)

[]ᵃ : VecRepA A zero
[]ᵃ idx with ¬Fin0 idx
... | ()

_∷ᵃ_ : A → VecRepA A n → VecRepA A (suc n)
(x ∷ᵃ xs) (zero , snd) = x
(x ∷ᵃ xs) (suc fst , snd) = xs (fst , pred-≤-pred snd)

_++ᵃ_ : VecRepA A n → VecRepA A m → VecRepA A (n + m)
_++ᵃ_ {n = n} {m = m} xs ys idx with Iso.fun (Fin+≅Fin⊎Fin n m) idx
... | inl a = xs a
... | inr a = ys a

mapᵃ : (f : A → B) → VecRepA A n → VecRepA B n
mapᵃ f xs = λ idx → f (xs idx)

joinᵃ : VecRepA (VecRepA A n) m → VecRepA A (m · n)
joinᵃ {n = n} {m = m} xs (i , p) = xs (i / n , ord₁ p ) ( i % n , ord₂ {m}{n} p )

slideᵃ : (sz : ℕ) → (sp : ℕ) → VecRepA A (sz + n · (suc sp)) → VecRepA (VecRepA A sz) (suc n)
slideᵃ {n = n} sz sp xs (fst₁ , snd₁) (fst₂ , snd₂) = xs (fst₂ + fst₁ · (suc sp) , <-+-≤ snd₂ (≤-·k {fst₁}{n} (pred-≤-pred snd₁)))


-- structure of vecs
record VecStr (V : Type → ℕ → Type) : Type₁ where
  field
    []ᵛ : V T 0
    _++ᵛ_ : V T n → V T m → V T (n + m)
    mapᵛ : (f : A → B) → V A n → V B n
    joinᵛ : V (V T n) m → V T (m · n)
    slideᵛ : (sz : ℕ) → (sp : ℕ) → V T (sz + n · (suc sp)) → V (V T sz) (suc n)

Vec-str : VecStr (Vec)
VecStr.[]ᵛ Vec-str = []
VecStr._++ᵛ_ Vec-str = _++_
VecStr.mapᵛ Vec-str = map
VecStr.joinᵛ Vec-str = join
VecStr.slideᵛ Vec-str = slide


VecRepA-str : VecStr (VecRepA)
VecStr.[]ᵛ VecRepA-str = []ᵃ
VecStr._++ᵛ_ VecRepA-str = _++ᵃ_
VecStr.mapᵛ VecRepA-str = mapᵃ
VecStr.joinᵛ VecRepA-str = joinᵃ
VecStr.slideᵛ VecRepA-str = slideᵃ

-- lemmas for the str eq
iso-fun-eq : (idx : FinA (suc n)) → Iso.fun (Fin+≅Fin⊎Fin 0 (suc n)) idx ≡ inr idx
iso-fun-eq (fst , snd) with fst ≤? 0
... | inl fst<0 with ¬-<-zero fst<0
iso-fun-eq (fst , snd) | inl fst<0 | ()
iso-fun-eq (fst , snd) | inr fst≥0 = refl


toRepA-map : (f : A → B) → (xs : Vec A n) → Vec→VecRepA (map f xs) ≡ mapᵃ f (Vec→VecRepA xs)
toRepA-map f [] i idx with ¬Fin0 idx
... | ()
toRepA-map f (x ∷ xs) i (zero , snd) = f x
toRepA-map f (x ∷ xs) i (suc fst , snd) = toRepA-map f xs i (fst , pred-≤-pred snd)

[]++ᵃ : (xs : VecRepA A n) → (Vec→VecRepA []) ++ᵃ xs ≡ xs
[]++ᵃ {n = zero} xs i idx with ¬Fin0 idx
... | ()
[]++ᵃ {n = suc n} xs i idx with Iso.fun (Fin+≅Fin⊎Fin 0 (suc n)) idx | iso-fun-eq idx
... | inl a | p with ¬Fin0 a
[]++ᵃ {n = suc n} xs i idx | inl a | p | ()
[]++ᵃ {n = suc n} xs i idx | inr a | p with ⊎Path.encode (inr a) (inr idx) p
... | goal = xs (Lift.lower goal i)

∷≡∷ᵃ : (x : A) → (xs : Vec A n) → Vec→VecRepA (x ∷ xs) ≡ x ∷ᵃ Vec→VecRepA xs
∷≡∷ᵃ x xs i (zero , snd) = x
∷≡∷ᵃ x xs i (suc fst , snd) = (Vec→VecRepA xs) (fst , pred-≤-pred snd)

iso-fun-inl-eq : (idx₁ : FinA n) → (idx₂ : FinA (n + m)) → Iso.fun (Fin+≅Fin⊎Fin n m) idx₂ ≡ inl idx₁ → fst idx₂ ≡ fst idx₁
iso-fun-inl-eq {n = n} {m = m} idx₁ idx₂ equ with (fst idx₂) ≤? n
... | inl a with ⊎Path.encode _ _ equ
iso-fun-inl-eq {n = n} {m = m} idx₁ idx₂ equ | inl a | p = cong fst (Lift.lower p)
iso-fun-inl-eq {n = n} {m = m} idx₁ idx₂ equ | inr a with ⊎Path.encode _ _ equ
... | ()

iso-fun-inr-eq : (idx₁ : FinA m) → (idx₂ : FinA (n + m)) → Iso.fun (Fin+≅Fin⊎Fin n m) idx₂ ≡ inr idx₁ → fst idx₂ ≥ n
iso-fun-inr-eq {m = m} {n = n} idx₁ idx₂ equ with (fst idx₂) ≤? n
... | inl a with ⊎Path.encode _ _ equ
iso-fun-inr-eq {m = m} {n = n} idx₁ idx₂ equ | inl a | ()
iso-fun-inr-eq {m = m} {n = n} idx₁ idx₂ equ | inr a with ⊎Path.encode _ _ equ
... | p = a

iso-fun-inr-eq-m : (idx₁ : FinA m) → (idx₂ : FinA (n + m)) → Iso.fun (Fin+≅Fin⊎Fin n m) idx₂ ≡ inr idx₁ → fst idx₁ ≡ fst idx₂ ∸ n
iso-fun-inr-eq-m {m = m} {n = n} idx₁ idx₂ equ with (fst idx₂) ≤? n
... | inl a with ⊎Path.encode _ _ equ
iso-fun-inr-eq-m {m = m} {n = n} idx₁ idx₂ equ | inl a | ()
iso-fun-inr-eq-m {m = m} {n = n} idx₁ idx₂ equ | inr a with ⊎Path.encode _ _ equ
... | p = subst (λ x → fst x ≡ fst idx₂ ∸ n) (Lift.lower p) refl

subgoal : (xs : VecRepA A n) → (ys : VecRepA A m) → (fst : ℕ) → (snd : fst < n + m) → (snd' : fst < n) → (xs ++ᵃ ys) (fst , snd) ≡ xs (fst , snd')
subgoal {n = n}{m = m} xs ys fst snd snd' with Iso.fun (Fin+≅Fin⊎Fin n m) (fst , snd) | inspect (Iso.fun (Fin+≅Fin⊎Fin n m)) (fst , snd)
... | inl a | [ p ]ᵢ with w ← iso-fun-inl-eq a (fst , snd) p = order-irrelevant {xs = xs} (sym w)
... | inr a | [ p ]ᵢ with w ← iso-fun-inr-eq a (fst , snd) p with () <- <-asym snd' w

goal : (x : A) → (xs : VecRepA A n) → (ys : VecRepA A m) → (fst fstₐ : ℕ) →
       (snd : fst < suc (n + m)) → (sndₐ : fstₐ < suc n) →
       (q : fst ≡ fstₐ) → (x ∷ᵃ (xs ++ᵃ ys)) (fst , snd) ≡ (x ∷ᵃ xs) (fstₐ , sndₐ)
goal {n = n} x xs ys zero fstₐ snd sndₐ q = sym ((x ∷ᵃ xs) (fstₐ , sndₐ)
   ≡⟨ order-irrelevant {xs = x ∷ᵃ xs} {p₂ = subst (_< suc n) (sym q) sndₐ} (sym q) ⟩
     refl)
goal {n = n} x xs ys (suc fst) fstₐ snd sndₐ q = sym ((x ∷ᵃ xs) (fstₐ , sndₐ)
   ≡⟨ order-irrelevant {xs = x ∷ᵃ xs} {p₂ = subst (_< suc n) (sym q) sndₐ} (sym q) ⟩
     (x ∷ᵃ xs) (suc fst , subst (_< suc n) (sym q) sndₐ)
   ≡⟨⟩
     xs (fst , pred-≤-pred (subst (_< suc n) (sym q) sndₐ))
   ≡⟨ sym (subgoal xs ys fst _ _) ⟩
    (xs ++ᵃ ys) (fst , pred-≤-pred snd) ∎)

subgoalᵣ : (xs : VecRepA A n) → (ys : VecRepA A m) → (fst fstₐ : ℕ) → (snd : suc fst < suc (n + m)) → (sndₐ : fstₐ < m) →
           (ord : n < suc fst) → (v : fstₐ ≡ suc fst ∸ suc n) →
           (xs ++ᵃ ys) (fst , pred-≤-pred snd) ≡ ys (fstₐ , sndₐ)
subgoalᵣ {n = n} {m = m} xs ys fst fstₐ snd sndₐ ord v with Iso.fun (Fin+≅Fin⊎Fin n m) (fst , pred-≤-pred snd) | inspect (Iso.fun (Fin+≅Fin⊎Fin n m)) (fst , pred-≤-pred snd)
... | inl (fst₁ , snd₁) | [ p ]ᵢ with w ← iso-fun-inl-eq (fst₁ , snd₁) (fst , pred-≤-pred snd) p with () ← <-asym ord (subst (λ x → suc x ≤ n) (sym w) snd₁)
... | inr (fst₁ , snd₁) | [ p ]ᵢ with w ← iso-fun-inr-eq-m (fst₁ , snd₁) (fst , pred-≤-pred snd) p = order-irrelevant {xs = ys} (w ∙ sym v)

goalᵣ : (x : A) → (xs : VecRepA A n) → (ys : VecRepA A m) → (fst fstₐ : ℕ) → (snd : fst < suc (n + m)) → (sndₐ : fstₐ < m) →
      (w : n < fst) → (v : fstₐ ≡ fst ∸ suc n) → ys (fstₐ , sndₐ) ≡ (x ∷ᵃ (xs ++ᵃ ys)) (fst , snd)
goalᵣ x xs ys zero fstₐ snd sndₐ w v with () ← ¬-<-zero w
goalᵣ x xs ys (suc fst) fstₐ snd sndₐ w v = ys (fstₐ , sndₐ)
    ≡⟨ sym (subgoalᵣ xs ys fst fstₐ snd sndₐ w v) ⟩
      (xs ++ᵃ ys) (fst , pred-≤-pred snd)
    ∎


lem₁ : (x : A) → (xs : VecRepA A n) → (ys : VecRepA A m) → (x ∷ᵃ xs) ++ᵃ ys ≡ x ∷ᵃ (xs ++ᵃ ys)
lem₁ {n = n} {m = m} x xs ys i idx with Iso.fun (Fin+≅Fin⊎Fin (suc n) m) idx | inspect (Iso.fun (Fin+≅Fin⊎Fin (suc n) m)) idx
... | inl a | [ p ]ᵢ with iso-fun-inl-eq a idx p
lem₁ {n = n} {m = m} x xs ys i (fst , snd) | inl (fstₐ , sndₐ) | [ p ]ᵢ | q = sym (goal x xs ys fst fstₐ snd sndₐ q) i
lem₁ {n = n} {m = m} x xs ys i idx | inr a | [ p ]ᵢ with iso-fun-inr-eq a idx p | iso-fun-inr-eq-m a idx p
lem₁ {n = n} {m = m} x xs ys i (fst , snd) | inr (fstₐ , sndₐ) | [ p ]ᵢ | w | v = goalᵣ x xs ys fst fstₐ snd sndₐ w v i

toRepA-++ : (xs : Vec A n) → (ys : Vec A m) → Vec→VecRepA xs ++ᵃ Vec→VecRepA ys ≡ Vec→VecRepA (xs ++ ys)
toRepA-++ [] ys = []++ᵃ (Vec→VecRepA ys)
toRepA-++ (x ∷ xs) ys i (zero , snd) = x
toRepA-++ (x ∷ xs) ys i (suc fst , snd) = lemma i
  where
  lemma = (Vec→VecRepA (x ∷ xs) ++ᵃ Vec→VecRepA ys) (suc fst , snd)
             ≡⟨ cong (λ y → (y ++ᵃ Vec→VecRepA ys) (suc fst , snd)) (∷≡∷ᵃ x xs) ⟩
             ((x ∷ᵃ (Vec→VecRepA xs)) ++ᵃ Vec→VecRepA ys) (suc fst , snd)
             ≡⟨ cong (λ y → y  (suc fst , snd)) (lem₁ x (Vec→VecRepA xs) (Vec→VecRepA ys)) ⟩
             (Vec→VecRepA xs ++ᵃ Vec→VecRepA ys) (fst , pred-≤-pred snd)
             ≡⟨ cong (λ y → y (fst , pred-≤-pred snd)) (toRepA-++ xs ys) ⟩
             Vec→VecRepA (xs ++ ys) (fst , pred-≤-pred snd)
             ≡⟨⟩
             Vec→VecRepA (x ∷ xs ++ ys) (suc fst , snd) ∎

toRepA-join : (xs : Vec (Vec A n) m) → joinᵃ (mapᵃ Vec→VecRepA (Vec→VecRepA xs)) ≡ Vec→VecRepA (join xs)
toRepA-join = {!!}

toRepA-slide : (sz sp : ℕ) (xs : Vec A (sz + n · (suc sp))) → (slideᵃ {n = n} sz sp (Vec→VecRepA xs)) ≡ Vec→VecRepA (map Vec→VecRepA (slide sz sp xs))
toRepA-slide = {!!}

-- Structural equality of vec and vec-rep-a
VecAStrEq : PathP (λ i → VecStr (λ T n → Vec≡VecRepA {T} {n} i)) Vec-str VecRepA-str
VecStr.[]ᵛ (VecAStrEq i) {T} = transp ((λ j → Vec≡VecRepA {T} {0} (i ∨ ~ j))) i []ᵃ
VecStr._++ᵛ_ (VecAStrEq i) {T} {n} {m} = ua→ {e = Vec≃VecRepA} {f₁ = _++ᵃ_} (λ xs →
      ua→ {e = Vec≃VecRepA {T} {m}} (λ ys →
      ua-gluePath (Vec≃VecRepA {T} {n + m}) {x = xs ++ ys} (sym (toRepA-++ xs ys)))) i
VecStr.mapᵛ (VecAStrEq i) {A} {B} {n} f = ua→ {e = Vec≃VecRepA} {f₁ = mapᵃ f} (λ xs → ua-gluePath (Vec≃VecRepA {B} {n}) {x = map f xs} (toRepA-map f xs)) i
VecStr.joinᵛ (VecAStrEq i) {T} {n} {m} xs = glue (λ { (i = i0) → join xs
                                                   ; (i = i1) → joinᵃ xs})
                                                (hcomp (λ j → λ { (i = i0) → toRepA-join xs j
                                                                ; (i = i1) → joinᵃ xs})
                                                (joinᵃ (mapᵃ (unglue (i ∨ ~ i)) (unglue (i ∨ ~ i) xs))))

-- WIP: This is not working becasue somehow we cannot deal with the inner dimension created by slide
-- I need a better understanding of hcomp
VecStr.slideᵛ (VecAStrEq i) {T} {n} sz sp xs = glue (λ { (i = i0) → slide sz sp xs
                                                 ; (i = i1) → slideᵃ {n = n} sz sp xs})
                                                 (hcomp ( (λ j → λ { (i = i0) → {!mapᵃ VecRepA→Vec (toRepA-slide {n = n} sz sp xs j)!}
                                                                ; (i = i1) → slideᵃ sz sp xs})) {!slideᵃ {n = n} sz sp (unglue (i ∨ ~ i) xs)!} )

