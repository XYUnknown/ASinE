{-# OPTIONS --cubical #-}

module HeterogeneousEq where
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_)
open import Primitives

eq-distribʳ-· : {A : Set} (n m o : ℕ) → Vec A ((n + m) · o) ≡ Vec A (n · o + m · o)
eq-distribʳ-· {A} n m o = cong (Vec A) (sym (·-distribʳ n m o))

eq-assoc-· : {A : Set} (n m o : ℕ) → Vec A (o · (m · n)) ≡ Vec A (o · m · n)
eq-assoc-· {A} n m o = cong (Vec A) (·-assoc o m n)

eq-assoc-+ : {A : Set} (n m o : ℕ) → Vec A (o + (m + n)) ≡ Vec A (o + m + n)
eq-assoc-+ {A} n m o = cong (Vec A) (+-assoc o m n)

++-assoc : {n m o : ℕ} → {A : Set} → (xs : Vec A n) → (ys : Vec A m) → (zs : Vec A o) →
           (λ i → (eq-assoc-+ {A} o m n) (~ i)) [ (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs) ]
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = congP (λ i → λ y → x ∷ y) (++-assoc xs ys zs)

join-++ : {n m o : ℕ} → {A : Set} → (xs₁ : Vec (Vec A o) n) → (xs₂ : Vec (Vec A o) m) →
          PathP (λ i → (eq-distribʳ-· {A} n m o) (~ i)) (join xs₁ ++ join xs₂ ) (join (xs₁ ++ xs₂))
join-++ [] xs₂ = refl
join-++ {suc n} {m} {o} {A} (xs₁ ∷ xs₂) xs₃ =
  compPathP' {B = Vec A} {p = sym (+-assoc o (n · o) (m · o))} {q = cong (o +_) (·-distribʳ n m o)}
  (++-assoc xs₁ (join xs₂) (join xs₃))
  (congP (λ i ys → xs₁ ++ ys) (join-++ xs₂ xs₃))


-- n m o : ℕ
-- A : Type
-- xsss : Vec (Vec (Vec A o) m ) n
-- Rule : join (map join xsss) == (join (join xsss))
mapJoinBeforeJoin : {n m o : ℕ} {A : Set} → (xsss : Vec (Vec (Vec A o) m) n)
  → PathP (λ i → (eq-assoc-· {A} o m n) i) (join (map join xsss)) (join (join xsss))
mapJoinBeforeJoin [] = refl
mapJoinBeforeJoin {suc n} {m} {o} {A} (xss ∷ xsss) =
  compPathP' {_} {ℕ} {_} {m · o + n · (m · o)} {m · o + n · m · o} {(m + n · m) · o} {B = Vec A}
  {p = cong (m · o +_) (·-assoc n m o)} {q = ·-distribʳ m (n · m) o}
  (congP (λ i yss → (join xss) ++ yss) (mapJoinBeforeJoin xsss)) (join-++ xss (join xsss))

-- n m o : ℕ
-- A : Type
-- xsss : Vec (Vec (Vec A o) m ) n
-- Rule : (join (join xsss)) == join (map join xsss)
joinBeforeJoin : {n m o : ℕ} {A : Set} → (xsss : Vec (Vec (Vec A o) m) n)
  → PathP (λ i → (eq-assoc-· {A} o m n) (~ i)) (join (join xsss)) (join (map join xsss))
joinBeforeJoin xsss = symP (mapJoinBeforeJoin xsss)

map-++ : {n m : ℕ} → {s t : Set} → (f : s → t) → (xs₁ : Vec s n) → (xs₂ : Vec s m) →
         map f (xs₁ ++ xs₂) ≡ map f xs₁ ++ map f xs₂
map-++ f [] xs₂ = refl
map-++ f (x ∷ xs₁) xs₂ = cong (f x  ∷_) (map-++ f xs₁ xs₂)


-- Old propositional eq
joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
                 (f : s → t) → (xs : Vec (Vec s n) m) →
                 map f (join xs) ≡ join (map (map f) xs)
joinBeforeMapF f [] = refl
joinBeforeMapF f (xs ∷ xs₁) =
    map f (xs ++ join (xs₁))
  ≡⟨ map-++ f xs (join xs₁) ⟩
    map f xs ++ map f (join xs₁)
  ≡⟨ cong (map f xs ++_) (joinBeforeMapF f xs₁) ⟩
    refl

mapMapFBeforeJoin : {s : Set} → {t : Set} → {m n : ℕ} →
                    (f : s → t) → (xs : Vec (Vec s n) m) →
                    join (map (map f) xs) ≡ map f (join xs)
mapMapFBeforeJoin f xs = sym (joinBeforeMapF f xs)
