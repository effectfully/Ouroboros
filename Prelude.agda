module Ouroboros.Prelude where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Data.Nat

cong₃ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
          {D : ∀ {x} {y : B x} -> C y -> Set δ} {x y v w s t}
      -> (f : ∀ x -> (y : B x) -> (z : C y) -> D z)
      -> x ≅ y -> v ≅ w -> s ≅ t -> f x v s ≅ f y w t
cong₃ f refl refl refl = refl

irefl : ∀ {ι α} {I : Set ι} {i j}
      -> (A : I -> Set α) -> (x : ∀ {i} -> A i) -> i ≅ j -> x {i} ≅ x {j}
irefl A x refl = refl

irefl² : ∀ {ι₁ ι₂ α} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂} {i₁ i₂ j₁ j₂}
       -> (A : ∀ i₁ -> I₂ i₁ -> Set α)
       -> (x : ∀ {i₁ i₂} -> A i₁ i₂) -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> x {i₁} {i₂} ≅ x {j₁} {j₂}
irefl² A x refl refl = refl

isubst : ∀ {ι α β} {I : Set ι} {i j : I}
         (A : I -> Set α) {x : A i} {y : A j}
       -> (B : ∀ {k} -> A k -> Set β) -> i ≅ j -> x ≅ y -> B x -> B y
isubst A C refl refl = id

icong : ∀ {ι α β} {I : Set ι} {i j : I}
        (A : I -> Set α) {B : ∀ {k} -> A k -> Set β} {x : A i} {y : A j}
      -> (f : ∀ {k} -> (x : A k) -> B x) -> i ≅ j -> x ≅ y -> f x ≅ f y
icong A f refl refl = refl

icong² : ∀ {ι₁ ι₂ α β} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
         (A : ∀ i₁ -> I₂ i₁ -> Set α) {B : ∀ {i₁ i₂} -> A i₁ i₂ -> Set β}
         {i₁ i₂ j₁ j₂} {x : A i₁ i₂} {y : A j₁ j₂}
       -> (f : ∀ {i₁ i₂} -> (x : A i₁ i₂) -> B x)
       -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> x ≅ y -> f x ≅ f y
icong² A f refl refl refl = refl

icong³ : ∀ {ι₁ ι₂ ι₃ α β} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
         {I₃ : ∀ {i₁} -> I₂ i₁ -> Set ι₃}
         (A : ∀ i₁ -> (i₂ : I₂ i₁) -> I₃ i₂ -> Set α)
         {B : ∀ {i₁ i₂ i₃} -> A i₁ i₂ i₃ -> Set β}
         {i₁ i₂ i₃ j₁ j₂ j₃} {x : A i₁ i₂ i₃} {y : A j₁ j₂ j₃}
       -> (f : ∀ {i₁ i₂ i₃} -> (x : A i₁ i₂ i₃) -> B x)
       -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> i₃ ≅ j₃ -> x ≅ y -> f x ≅ f y
icong³ A f refl refl refl refl = refl

icong₂ : ∀ {ι α β γ} {I : Set ι}
         (A : I -> Set α) {B : ∀ {k} -> A k -> Set β}
         {C : ∀ {k} {x : A k} -> B x -> Set γ}
         {i j} {x : A i} {y : A j} {v w}
       -> (f : ∀ {k} -> (x : A k) -> (y : B x) -> C y)
       -> i ≅ j -> x ≅ y -> v ≅ w -> f x v ≅ f y w
icong₂ A f refl refl refl = refl

icong²₂ : ∀ {ι₁ ι₂ α β γ} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂}
          (A : ∀ i₁ -> I₂ i₁ -> Set α) {B : ∀ {i₁ i₂} -> A i₁ i₂ -> Set β}
          {C : ∀ {i₁ i₂} {x : A i₁ i₂} -> B x -> Set γ}
          {i₁ i₂ j₁ j₂} {x : A i₁ i₂} {y : A j₁ j₂} {v w}
        -> (f : ∀ {i₁ i₂} -> (x : A i₁ i₂) -> (y : B x) -> C y)
        -> i₁ ≅ j₁ -> i₂ ≅ j₂ -> x ≅ y -> v ≅ w -> f x v ≅ f y w
icong²₂ A f refl refl refl refl = refl

unsubst : ∀ {ι α β} {I : Set ι} {i j : I}
        -> (A : I -> Set α) {B : ∀ {k} -> A k -> Set β} {x : A i}
        -> (f : ∀ {k} -> (x : A k) -> B x)
        -> (i≅j : i ≅ j) {y : B (subst A i≅j x)}
        -> f (subst A i≅j x) ≅ y
        -> f x ≅ y
unsubst A f refl r = r

cong-subst-removable : ∀ {ι α β} {I : Set ι} {i j : I}
                     -> (A : I -> Set α) {B : ∀ {k} -> A k -> Set β} {x : A i}
                     -> (f : ∀ {k} -> (x : A k) -> B x)
                     -> (i≅j : i ≅ j)
                     -> f x ≅ f (subst A i≅j x)
cong-subst-removable A f refl = refl

subst-addable-both : ∀ {ι κ α} {I : Set ι} {K : Set κ} {i j : I} {k l : K}
                   -> (A : I -> Set α)
                   -> (C : K -> Set α)
                   -> (i≅j : i ≅ j)
                   -> (k≅l : k ≅ l)
                   -> (x : A i)
                   -> (z : C k)
                   -> x ≅ z
                   -> subst A i≅j x ≅ subst C k≅l z
subst-addable-both A C refl refl x z = id

cong-subst-addable-both : ∀ {ι κ α β γ} {I : Set ι} {K : Set κ} {i j : I} {k l : K}
                        -> (A : I -> Set α) {B : ∀ {i} -> A i -> Set β}
                        -> (C : K -> Set γ) {D : ∀ {k} -> C k -> Set β}
                        -> (f : ∀ {i} -> (x : A i) -> B x)
                        -> (h : ∀ {k} -> (z : C k) -> D z)
                        -> (i≅j : i ≅ j)
                        -> (k≅l : k ≅ l)
                        -> (x : A i)
                        -> (z : C k)
                        -> f x ≅ h z
                        -> f (subst A i≅j x) ≅ h (subst C k≅l z)
cong-subst-addable-both A C f h refl refl x z = id

data Fin : ℕ -> Set where
  zero : ∀ {n} -> Fin n
  suc  : ∀ {n} -> Fin n -> Fin (suc n)

toℕ : ∀ {n} -> Fin n -> ℕ
toℕ  zero   = 0
toℕ (suc i) = suc (toℕ i)

_+F_ : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (toℕ i + m)
zero    +F j = j
(suc i) +F j = suc (i +F j)

inject₁ : ∀ {n} -> Fin n -> Fin (suc n)
inject₁  zero   = zero
inject₁ (suc i) = suc (inject₁ i)

rearrange : ∀ {n m} -> (i : Fin n) -> Fin (toℕ i + m)
rearrange  zero   = zero
rearrange (suc i) = suc (rearrange i)

predⁿ : ∀ n -> Fin n -> ℕ
predⁿ  n       zero   = n
predⁿ (suc n) (suc i) = suc (predⁿ n i)

minus-rearrange : ∀ {n m} (i : Fin n)
                -> m ≅ toℕ i + m ∸ toℕ (rearrange {m = m} i)
minus-rearrange  zero   = refl
minus-rearrange (suc i) = minus-rearrange i

inject₁-rearrange : ∀ {n m} (i : Fin n) (j : Fin m) 
                  ->   ℕ.suc (toℕ i + m ∸ toℕ (rearrange {m = m} i))
                     ≅ suc (toℕ i + m) ∸ toℕ (inject₁ (rearrange {m = m} i))
inject₁-rearrange  zero   j = refl
inject₁-rearrange (suc i) j = inject₁-rearrange i j

rearrange-by : ∀ {n m} -> (i : Fin n) -> Fin m -> Fin (toℕ i + m ∸ toℕ (rearrange {m = m} i))
rearrange-by = subst Fin ∘ minus-rearrange

plus-minus-rearrange : ∀ {n m} (i : Fin n) {j : Fin m}
                     ->   toℕ i + m ∸ toℕ (i +F j)
                        ≅ toℕ i + m ∸ toℕ (rearrange {m = m} i) ∸ toℕ (rearrange-by i j)
plus-minus-rearrange  zero   = refl
plus-minus-rearrange (suc i) = plus-minus-rearrange i
