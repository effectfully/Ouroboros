{-# OPTIONS --no-termination-check #-}

-- I have no idea what I am doing.

module Ouroboros.Weakening.Experimental where

open import Function hiding (_∋_)
open import Relation.Binary.HeterogeneousEquality

open import Ouroboros.Prelude

infixl 6 _▻_
infixr 5 _Π_
infix  3 _⊆_ _⊢_
infix  9 _∘ˢ_

data Con : Set
data Type (Γ : Con) : Set
data _⊆_ : Con -> Con -> Set
_∘ˢ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
∘ˢ-assoc : ∀ {Ω Γ Δ Θ} (ξ : Δ ⊆ Θ) (φ : Γ ⊆ Δ) (ψ : Ω ⊆ Γ)
         -> (ξ ∘ˢ φ) ∘ˢ ψ ≅ ξ ∘ˢ (φ ∘ˢ ψ)
data _⊢_ (Γ : Con) : Type Γ -> Set
Weaken : ∀ {Γ Δ} -> Γ ⊆ Δ -> Type Γ -> Type Δ
Weaken-comp : ∀ {Γ Δ Θ} {φ : Δ ⊆ Θ} {ψ : Γ ⊆ Δ} (σ : Type Γ)
            -> Weaken (φ ∘ˢ ψ) σ ≅ Weaken φ (Weaken ψ σ)
weaken : ∀ {Γ Δ σ} -> (ψ : Γ ⊆ Δ) -> Γ ⊢ σ -> Δ ⊢ Weaken ψ σ
weaken-comp : ∀ {Γ Δ Θ σ} {φ : Δ ⊆ Θ} {ψ : Γ ⊆ Δ} (x : Γ ⊢ σ)
            -> weaken (φ ∘ˢ ψ) x ≅ weaken φ (weaken ψ x)

data Con where
  ε : Con
  _▻_ : ∀ Γ -> Type Γ -> Con

data Type Γ where
  type :  Type Γ
  _Π_  : (σ : Type Γ) -> Type (Γ ▻ σ) -> Type Γ
  ↑    :  Γ ⊢ type    -> Type Γ

data _⊆_ where
  stop : ∀ {Γ σ}   ->      Γ ⊆ Γ ▻ σ
  skip : ∀ {Γ Δ σ} ->      Γ ⊆ Δ     -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> (ψ : Γ ⊆ Δ)    -> Γ ▻ σ ⊆ Δ ▻ Weaken ψ σ

Weaken ψ  type   = type
Weaken ψ (σ Π τ) = Weaken ψ σ Π Weaken (keep ψ) τ
Weaken ψ (↑ t)   = ↑ (weaken ψ t)

data _⊢_ Γ where
  var : ∀ {Ω σ} -> (ψ : Ω ⊆ Γ) -> Γ ⊢ Weaken ψ σ
    -- If we have `σ' defined in some context `Ω',
    -- and `Ω' is a subcontext of `Γ',
    -- then we can define `σ' in `Γ'.
  ƛ_  : ∀ {σ τ} ->  Γ ▻ σ ⊢ τ  -> Γ ⊢ σ Π τ

pat : ∀ {Γ Δ} -> Type Δ -> Set
pat {Γ} {Δ} τ = Γ ⊆ Δ ▻ τ

stop   ∘ˢ ψ      = skip  ψ
skip φ ∘ˢ ψ      = skip (φ ∘ˢ ψ)
keep φ ∘ˢ stop   = skip  φ
keep φ ∘ˢ skip ψ = skip (φ ∘ˢ ψ)
-- We should never encounter this case. Right?
keep φ ∘ˢ keep ψ = subst pat (Weaken-comp _)
                     (keep (φ ∘ˢ ψ))

∘ˢ-assoc  stop     φ        ψ       = refl
∘ˢ-assoc (skip ξ)  φ        ψ       = cong skip (∘ˢ-assoc ξ φ ψ)
∘ˢ-assoc (keep ξ)  stop     ψ       = refl
∘ˢ-assoc (keep ξ) (skip φ)  ψ       = cong skip (∘ˢ-assoc ξ φ ψ)
∘ˢ-assoc (keep ξ) (keep φ)  stop    =
  trans (sym (cong-subst-removable pat (_∘ˢ stop) (Weaken-comp _)))
        (irefl pat (skip (ξ ∘ˢ φ)) (Weaken-comp _))
∘ˢ-assoc (keep ξ) (keep φ) (skip ψ) =
  trans (sym (cong-subst-removable pat (_∘ˢ skip ψ) (Weaken-comp _)))
        (cong₂ (λ σ ψ -> skip {σ = σ} ψ) (Weaken-comp _) (∘ˢ-assoc ξ φ ψ))
∘ˢ-assoc (keep ξ) (keep φ) (keep ψ) =
  trans (sym (cong-subst-removable pat (_∘ˢ keep ψ) (Weaken-comp _)))
        (trans (subst-removable pat (Weaken-comp _) (keep ((ξ ∘ˢ φ) ∘ˢ ψ)))
               (trans (trans (cong keep (∘ˢ-assoc ξ φ ψ))
                             (sym (subst-removable pat (Weaken-comp _) (keep (ξ ∘ˢ (φ ∘ˢ ψ))))))
                      (cong-subst-removable pat (keep ξ ∘ˢ_) (Weaken-comp _))))

Weaken-comp  type   = refl
Weaken-comp (σ Π τ) = cong₂ _Π_ (Weaken-comp σ)
  (unsubst pat (flip Weaken τ) (Weaken-comp σ) (Weaken-comp τ))
Weaken-comp (↑ t)   = cong ↑ (weaken-comp t)

weaken φ (var ψ) = subst (_ ⊢_) (Weaken-comp _)
                     (var (φ ∘ˢ ψ))
weaken φ (ƛ b)   = ƛ (weaken (keep φ) b)

weaken-comp {φ = ξ} {ψ = φ} (var ψ) =
  trans (subst-removable (_ ⊢_) (Weaken-comp _) (var ((ξ ∘ˢ φ) ∘ˢ ψ)))
        (trans (trans (cong var (∘ˢ-assoc ξ φ ψ))
                      (sym (subst-removable (_ ⊢_) (Weaken-comp _) (var (ξ ∘ˢ (φ ∘ˢ ψ))))))
               (cong-subst-removable (_ ⊢_) (weaken ξ) (Weaken-comp _)))
weaken-comp                 (ƛ b)   =
  cong₃ (λ σ τ (b : _ ▻ σ ⊢ τ) -> ƛ b)
        (Weaken-comp _)
        (unsubst pat (flip Weaken _) (Weaken-comp _) (Weaken-comp _))
        (trans (cong-subst-removable pat (flip weaken b) (Weaken-comp _))
               (weaken-comp b))




Term : (σ : Type ε) -> Set
Term σ = ε ⊢ σ

vz : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
vz = stop

vs_ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊆ Δ ▻ σ
vs_ = skip

I : Term (type Π ↑ (var vz) Π ↑ (var (vs vz)))
I = ƛ ƛ var {σ = ↑ (var vz)} vz

K : Term (type Π type Π ↑ (var (vs vz)) Π ↑ (var (vs vz)) Π ↑ (var (vs vs vs vz)))
K = ƛ ƛ ƛ ƛ var {σ = ↑ (var (vs vz))} (vs vz)
