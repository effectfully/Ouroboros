{-# OPTIONS --no-termination-check #-}

module Ouroboros.Full.Sketch where

open import Function as F hiding (_∋_)
open import Relation.Binary.HeterogeneousEquality as H hiding (subst; [_])
open import Data.Nat

open import Ouroboros.Prelude

infixl 2 _,_
infixr 2 _Π_
infix  1 _∋_ _⊢_

data Con : ℕ -> Set
data Type {n} (Γ : Con n) : Set
data _∋_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set
data _⊢_ {n} (Γ : Con n) : Type Γ -> Set

data Con where
  ε : Con 0
  _,_ : ∀ {n} (Γ : Con n) -> Type Γ -> Con (suc n)

rdrop : ∀ {n} -> (i : Fin n) -> Con n -> Con (n ∸ toℕ i)
rdrop  zero     Γ      = Γ
rdrop (suc n)  (Γ , σ) = rdrop n Γ

data Type {n} Γ where
  type : Type Γ
  _Π_  : (σ : Type Γ) -> Type (Γ , σ) -> Type Γ
  ↑    : Γ ⊢ type     -> Type Γ

rlookup : ∀ {n} i (Γ : Con (suc n)) -> Type (rdrop (suc i) Γ)
rlookup  zero   (Γ , σ) = σ
rlookup (suc i) (Γ , σ) = rlookup i Γ

rinsert : ∀ {n} i (Γ : Con n) -> Type (rdrop i Γ) -> Con (suc n)
Weaken : ∀ {n} i {Γ : Con n} {σ} -> Type Γ -> Type (rinsert i Γ σ)
weaken : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ⊢ τ -> rinsert i Γ σ ⊢ Weaken i τ

rinsert  zero    Γ      τ = Γ , τ
rinsert (suc i) (Γ , σ) τ = rinsert i Γ τ , Weaken i σ

Weaken i  type   = type
Weaken i (σ Π τ) = Weaken i σ Π Weaken (suc i) τ
Weaken i (↑ t)   = ↑ (weaken i t)

Pop : ∀ {n} {Γ : Con n} {σ} -> Type Γ -> Type (Γ , σ)
Pop = Weaken zero

instantiate : ∀ {n} i (Γ : Con (suc n)) -> rdrop (suc i) Γ ⊢ rlookup i Γ -> Con (predⁿ n i)
Subst : ∀ {n} i {Γ : Con (suc n)}
      -> Type Γ -> (s : rdrop (suc i) Γ ⊢ rlookup i Γ) -> Type (instantiate i Γ s)
subst : ∀ {n} i {Γ : Con (suc n)} {τ}
      -> Γ ⊢ τ  -> (s : rdrop (suc i) Γ ⊢ rlookup i Γ) -> instantiate i Γ s ⊢ Subst i τ s

instantiate  zero   (Γ , σ) s = Γ
instantiate (suc i) (Γ , σ) s = instantiate i Γ s , Subst i σ s

Subst i  type   s = type
Subst i (σ Π τ) s = Subst i σ s Π Subst (suc i) τ s
Subst i (↑ t)   s = ↑ (subst i t s)

_[_] : ∀ {n} {Γ : Con n} {σ} -> Type (Γ , σ) -> Γ ⊢ σ -> Type Γ
_[_] = Subst zero

postulate
  Pop-Weaken : ∀ {n} {i : Fin n} {Γ : Con n} {σ : Type Γ} {τ υ}
             -> Pop {σ = Weaken i τ} (Weaken i {σ = υ} σ) ≅ Weaken (suc i) (Pop {σ = τ} σ)
  Pop-[] : ∀ {n} {Γ : Con n} {σ : Type Γ} {τ} {s}
         -> σ ≅ Pop {σ = τ} σ [ s ]
  Pop-Subst : ∀ {n} {i : Fin n} {Γ : Con (suc n)} {σ : Type Γ} {τ}
              {s : rdrop (suc i) Γ ⊢ rlookup i Γ}
            -> Pop {σ = Subst i τ s} (Subst i σ s) ≅ Subst (suc i) (Pop {σ = τ} σ) s
  Weaken-[] : ∀ {n} {i : Fin n} {Γ : Con n} {σ : Type Γ} {τ υ} {x : Γ ⊢ σ}
            -> Weaken (suc i) {σ = υ} τ [ weaken i x ] ≅ Weaken i {σ = υ} (τ [ x ])
  Subst-[] : ∀ {n} {i : Fin n} {Γ : Con (suc n)} {σ : Type Γ} {τ}
             {x : Γ ⊢ σ} {s : rdrop (suc i) Γ ⊢ rlookup i Γ}
           -> Subst (suc i) τ s [ subst i x s ] ≅ Subst i (τ [ x ]) s

data _∋_ where
  vz  : ∀ {n} {Γ : Con n} {σ}   -> Γ , σ ∋ Pop σ
  vs_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ     ∋ σ     -> Γ , τ ∋ Pop σ

weaken-var : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ∋ τ -> rinsert i Γ σ ∋ Weaken i τ
weaken-var  zero             j     = vs j
weaken-var (suc i)  {Γ , σ}  vz    = H.subst (_∋_ _) Pop-Weaken
                                       vz
weaken-var (suc i)  {Γ , σ} (vs v) = H.subst (_∋_ _) Pop-Weaken
                                      (vs (weaken-var i v))

data _⊢_ {n} Γ where
  ƛ_   : ∀ {σ τ} -> Γ , σ ⊢ τ -> Γ ⊢ σ Π τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ Π τ -> (x : Γ ⊢ σ) -> Γ ⊢ τ [ x ]
  ↓    :             Type Γ   -> Γ ⊢ type
  var  : ∀ {σ}   -> Γ ∋ σ    -> Γ ⊢ σ

weaken i (ƛ b)   = ƛ (weaken (suc i) b)
weaken i (f · x) = H.subst (_⊢_ _) Weaken-[]
                    (weaken i f · weaken i x)
weaken i (↓ σ)   = ↓ (Weaken i σ)
weaken i (var v) = var (weaken-var i v)

pop : ∀ {n} {Γ : Con n} {σ τ} -> Γ ⊢ τ -> Γ , σ ⊢ Pop τ
pop = weaken zero

subst-var : ∀ {n} i {Γ : Con (suc n)} {τ}
          -> Γ ∋ τ -> (x : rdrop (suc i) Γ ⊢ rlookup i Γ) -> instantiate i Γ x ⊢ Subst i τ x
subst-var  zero    vz    s = H.subst (_⊢_ _) Pop-[]
                               s
subst-var  zero   (vs v) s = H.subst (_⊢_ _) Pop-[]
                              (var v)
subst-var (suc i)  vz    s = H.subst (_⊢_ _) Pop-Subst
                              (var vz)
subst-var (suc i) (vs v) s = H.subst (_⊢_ _) Pop-Subst
                              (pop (subst-var i v s))

subst i (ƛ b)   s = ƛ (subst (suc i) b s)
subst i (f · x) s = H.subst (_⊢_ _) Subst-[]
                     (subst i f s · subst i x s)
subst i (↓ σ)   s = ↓ (Subst i σ s)
subst i (var v) s = subst-var i v s
