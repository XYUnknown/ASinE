{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Empty
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_; ++-assoc)
open import Cubical.Data.Fin.Recursive
open import Cubical.Relation.Nullary

private
  variable
    n m o : ℕ
    A B T : Type

-- missing properties of Vec

++-zero : ∀ (xs : Vec A n) → PathP (λ i → Vec A (+-zero n i)) (xs ++ []) xs
++-zero [] = refl
++-zero (x ∷ xs) i = x ∷ ++-zero xs i

-- personally, I have never ran into any issue with recursive fin in cubical

VecRep : (A : Type) → ℕ → Type
VecRep A n = Fin n → A

-- this is 56 lines for Vec!
-- also, Vec is atleast hlevel 2, VecRep doesn't have to be

isOfHLevelVecRep : (n : HLevel) → isOfHLevel n A → isOfHLevel n (VecRep A m)
isOfHLevelVecRep n hA = isOfHLevelΠ n λ _ → hA

isSetVecRep : isSet A → isSet (VecRep A n)
isSetVecRep setA = isOfHLevelVecRep 2 setA

-- VecRep→Vec→VecRep could be alot simpler:

toRep : ∀ {A n} → Vec A n → VecRep A n
toRep [] = λ ()
toRep (x ∷ xs) = λ { zero → x
                   ; (suc n) → toRep xs n }

fromRep : ∀ {A n} → VecRep A n → Vec A n
fromRep {n = zero} xs = []
fromRep {n = suc n} xs = xs zero ∷ (fromRep (λ x → xs (suc x)))

toRep-fromRep : ∀ {A n} (xs : VecRep A n) → toRep (fromRep xs) ≡ xs
toRep-fromRep {n = zero} xs i ()
toRep-fromRep {n = suc n} xs i zero = xs zero
toRep-fromRep {n = suc n} xs i (suc m) = toRep-fromRep {n = n} (λ n → xs (suc n)) i m

fromRep-toRep : ∀ {A n} (xs : Vec A n) → fromRep (toRep xs) ≡ xs
fromRep-toRep [] = refl
fromRep-toRep (x ∷ xs) i = x ∷ fromRep-toRep xs i

Iso-Vec-VecRep : ∀ {A n} → Iso (Vec A n) (VecRep A n)
Iso-Vec-VecRep = iso toRep fromRep toRep-fromRep fromRep-toRep

Vec≃VecRep : Vec A n ≃ VecRep A n
Vec≃VecRep = isoToEquiv Iso-Vec-VecRep

Vec≡VecRep : Vec A n ≡ VecRep A n
Vec≡VecRep = ua Vec≃VecRep

Vec2D≡VecRep : Vec (Vec A n) m ≡ VecRep (VecRep A n) m
Vec2D≡VecRep {A} {n} {m} = Vec (Vec A n) m
  ≡⟨ cong (λ T → Vec T m) (Vec≡VecRep) ⟩
    Vec (VecRep A n) m
  ≡⟨ Vec≡VecRep ⟩
    refl

Vec2D≃VecRep : Vec (Vec A n) m ≃ VecRep (VecRep A n) m
Vec2D≃VecRep = pathToEquiv (Vec2D≡VecRep)

-- subst lemma from zulip

subst-VecRep : {A : Set} {a b : ℕ} (eq : a ≡ b) (xs : VecRep A a) (n : Fin b)
    → subst (VecRep A) eq xs n ≡ xs (subst Fin (sym eq) n)
subst-VecRep eq xs n = transportRefl (xs (subst Fin (sym eq) n))

-- operations for Vec
map : (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

join : Vec (Vec A n) m → Vec A (m · n)
join [] = []
join (x ∷ xs) = x ++ join xs

-- operations for VecRep
tailʳ : VecRep A (suc n) → VecRep A n
tailʳ xs x = xs (suc x)

[]ʳ : VecRep A zero
[]ʳ = λ ()

_++ʳ_ : VecRep A n → VecRep A m → VecRep A (n + m)
_++ʳ_ {n = n} {m} xs ys x with split n x
... | inl m = xs m
... | inr m = ys m

mapʳ : (f : A → B) → VecRep A n → VecRep B n
mapʳ f xs idx = f (xs idx)

joinʳ : VecRep (VecRep A n) m → VecRep A (m · n)
joinʳ {A} {n} {suc m} xs idx with split n idx
... | inl x = xs zero x
... | inr x = joinʳ (tailʳ xs) x

-- properties

tailʳ-++ʳ : ∀ (xs : VecRep A (suc n)) (ys : VecRep A m) → tailʳ (xs ++ʳ ys) ≡ tailʳ xs ++ʳ ys
tailʳ-++ʳ {n = n} xs ys i x with split n x
... | inl m = xs (suc m)
... | inr m = ys m

-- structure of vecs defined in terms of [] and ++

record VecStr (V : Type → ℕ → Type) : Type₁ where
  field
    []ᵛ : V T 0
    _++ᵛ_ : V T n → V T m → V T (n + m)
    mapᵛ : (f : A → B) → V A n → V B n
    joinᵛ : V (V T n) m → V T (m · n)

Vec-str : VecStr (Vec)
VecStr.[]ᵛ Vec-str = []
VecStr._++ᵛ_ Vec-str = _++_
VecStr.mapᵛ Vec-str = map
VecStr.joinᵛ Vec-str = join

VecRep-str : VecStr (VecRep)
VecStr.[]ᵛ VecRep-str = []ʳ
VecStr._++ᵛ_ VecRep-str = _++ʳ_
VecStr.mapᵛ VecRep-str = mapʳ
VecStr.joinᵛ VecRep-str = joinʳ

-- structure identity

toRep-++ : ∀ (xs : Vec A n) (ys : Vec A m) → toRep xs ++ʳ toRep ys ≡ toRep (xs ++ ys)
toRep-++ [] ys = refl
toRep-++ (x ∷ xs) ys i zero = x
toRep-++ (_∷_ {n} x xs) ys i (suc o) = lemma i
  where
  lemma =
    (toRep (x ∷ xs) ++ʳ toRep ys) (suc o)    ≡⟨⟩
    tailʳ (toRep (x ∷ xs) ++ʳ toRep ys) o    ≡⟨ cong (λ a → a o) (tailʳ-++ʳ (toRep (x ∷ xs)) (toRep ys)) ⟩
    (tailʳ (toRep (x ∷ xs)) ++ʳ toRep ys) o  ≡⟨⟩
    (toRep xs ++ʳ toRep ys) o                ≡⟨ cong (λ a → a o) (toRep-++ xs ys) ⟩
    (toRep (xs ++ ys)) o                     ≡⟨⟩
    toRep ((x ∷ xs) ++ ys) (suc o)           ∎

toRep-map : (f : A → B) → (xs : Vec A n) → toRep (map f xs) ≡ mapʳ f (toRep xs)
toRep-map f (x ∷ xs) i zero = f x
toRep-map f (x ∷ xs) i (suc idx) = toRep-map f xs i idx


VecStrEq : PathP (λ i → VecStr (λ T n → Vec≡VecRep {T} {n} i)) Vec-str VecRep-str
VecStr.[]ᵛ (VecStrEq i) {T} = transp (λ j → Vec≡VecRep {T} {0} (i ∨ ~ j)) i λ ()
VecStr._++ᵛ_ (VecStrEq i) {T} {n} {m} = ua→ {e = Vec≃VecRep} {f₁ = _++ʳ_} (λ xs →
      ua→ {e = Vec≃VecRep {T} {m}} (λ ys →
      ua-gluePath (Vec≃VecRep {T} {n + m}) {x = xs ++ ys} (sym (toRep-++ xs ys)))) i
VecStr.mapᵛ (VecStrEq i) {A} {B} {n} f = ua→ {e = Vec≃VecRep} {f₁ = mapʳ f} (λ xs → ua-gluePath (Vec≃VecRep {B} {n}) {x = map f xs} (toRep-map f xs)) i
VecStr.joinᵛ (VecStrEq i) {T} {n} {m} xs = {!!} {- glue (λ { (i = i0) → join xs
                                                   ; (i = i1) → joinʳ xs})
                                                (hcomp (λ j → λ { (i = i0) → {!!} j
                                                                ; (i = i1) → joinʳ xs})
                                                (joinʳ (unglue (i ∨ ~ i) {!xs!}))) -}

-- this is nice but the inlined def is probably easier to read and understand

-- VecStr._++ᵛ_ (VecStrEq {A = A} i) {n} {m} xs ys = glue (λ { (i = i0) → xs ++ ys
--                                                           ; (i = i1) → xs ++ʳ ys})
--                                                        (hcomp (λ j → λ { (i = i0) → toRep-++ xs ys j
--                                                                        ; (i = i1) → xs ++ʳ ys
--                                                                        })
--                                                        ((unglue (i ∨ ~ i) xs) ++ʳ unglue (i ∨ ~ i) ys))

{-

For VecStr._++ᵛ_, we have arguments binary function on the type Vec≡VecRep i
Vec≡VecRep is defined in terms of ua, which is intern defined interms of Glue types
So Vec≡VecRep i is actually the type:

Glue VecRep (λ { (i = i0) → (Vec , Vec≃VecRep)
               ; (i = i1) → (VecRep , idEquiv VecRep) })

i = i0 ⊢ xs ++ ys
i = i1 ⊢ xs ++ʳ ys

Left hand of Glue square applys first projection of Vec≃VecRep which is toRep
Right hand side is idEquiv, so nothing to do here
Base - unglue gives us an element VecRep that is toRep xs (xs : Vec) on the left and xs on the right (xs : VecRep)

-}

-- now we can define propositions in terms of the abstract structure

record ++-zero-str {V} (S : VecStr V) : Type₁ where
  open VecStr S
  field
    proof : (xs : V T n) → PathP (λ i → V T (+-zero n i)) (xs ++ᵛ []ᵛ) xs

++-zero-str-Vec : ++-zero-str (Vec-str)
++-zero-str.proof ++-zero-str-Vec = ++-zero

-- and transport it to our desired type

++ʳ-zero : ∀ {n} (xs : VecRep A n) → PathP (λ i → VecRep A (+-zero n i)) (xs ++ʳ []ʳ) xs
++ʳ-zero {A = A} = ++-zero-str.proof (transp (λ i → ++-zero-str (VecStrEq i)) i0 ++-zero-str-Vec)

-- another example with assoc

record ++-assoc-str {V} (S : VecStr V) : Type₁ where
  open VecStr S
  field
    proof : ∀ {n m o} (xs : V T n) (ys : V T m) (zs : V T o)
          → PathP (λ i → V T (+-assoc n m o i)) (xs ++ᵛ (ys ++ᵛ zs)) ((xs ++ᵛ ys) ++ᵛ zs)

++-assoc-str-Vec : ++-assoc-str (Vec-str)
++-assoc-str.proof ++-assoc-str-Vec xs ys zs i = ++-assoc xs ys zs (~ i) -- assoc is the wrong way round in std lib!

++ʳ-assoc : ∀ {n m o} (xs : VecRep A n) (ys : VecRep A m) (zs : VecRep A o)
          → PathP (λ i → VecRep A (+-assoc n m o i)) (xs ++ʳ (ys ++ʳ zs)) ((xs ++ʳ ys) ++ʳ zs)
++ʳ-assoc {A = A} = ++-assoc-str.proof (transp (λ i → ++-assoc-str (VecStrEq i)) i0 ++-assoc-str-Vec)

-- this is good if you want to consider many vector reprensentations, but if you only ever consider 2, then
-- just transporting might be simpler (no glue mess)

_++ʳ⁼_ : ∀ {n m} (xs : VecRep A n) (ys : VecRep A m) → VecRep A (n + m)
_++ʳ⁼_ {A = A} {n = n} {m} = transport (λ i → Vec≡VecRep {A} {n} i → Vec≡VecRep {A} {m} i → Vec≡VecRep {A} {n + m} i) _++_

++ʳ→++ʳ⁼ : ∀ {n m} (xs : VecRep A n) (ys : VecRep A m) → xs ++ʳ ys ≡ xs ++ʳ⁼ ys
++ʳ→++ʳ⁼ xs ys = cong₂ _++ʳ_ (sym (transportRefl xs)) (sym (transportRefl ys))
               ∙ lemma {xs = transport refl xs}
               ∙ sym (transportRefl _)
  where
    lemma : ∀ {xs : VecRep A n} {ys : VecRep A m} → xs ++ʳ ys ≡ toRep (fromRep xs ++ fromRep ys)
    lemma {xs = xs} {ys} = cong₂ _++ʳ_ (sym (toRep-fromRep xs)) (sym (toRep-fromRep ys))
                         ∙ toRep-++ (fromRep xs) (fromRep ys)

-- the reason why transportRefl keeps popping up is transport can compute for simple closed types, but in the
-- general case it doesnt (and VecRep hits that)
