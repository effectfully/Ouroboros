{-# OPTIONS --no-termination-check #-}

module Ouroboros.Weakening.OPE where

open import Function hiding (_∋_)
open import Relation.Binary.HeterogeneousEquality
open import Data.Nat

open import Ouroboros.Prelude

infixl 4 _▻_
infixr 5 _Π_
infix  3 _∋_ _⊆_ _⊢_

data Con : Set
data Type (Γ : Con) : Set
data _∋_ : ∀ Γ -> Type Γ -> Set
data _⊆_ : Con -> Con -> Set
idˢ : ∀ {Γ} -> Γ ⊆ Γ
_∘ˢ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
data _⊢_ (Γ : Con) : Type Γ -> Set
Weaken : ∀ {Γ Δ} -> Γ ⊆ Δ -> Type Γ -> Type Δ
Weaken-id : ∀ {Γ} -> (σ : Type Γ) -> Weaken idˢ σ ≅ σ
Weaken-comp : ∀ {Γ Δ Θ} {φ : Δ ⊆ Θ} {ψ : Γ ⊆ Δ} (σ : Type Γ)
            -> Weaken (φ ∘ˢ ψ) σ ≅ Weaken φ (Weaken ψ σ)
weaken : ∀ {Γ Δ σ} -> (ψ : Γ ⊆ Δ) -> Γ ⊢ σ -> Δ ⊢ Weaken ψ σ
weaken-id : ∀ {Γ σ} -> (x : Γ ⊢ σ) -> weaken idˢ x ≅ x
weaken-comp : ∀ {Γ Δ Θ σ} {φ : Δ ⊆ Θ} {ψ : Γ ⊆ Δ} (x : Γ ⊢ σ)
            -> weaken (φ ∘ˢ ψ) x ≅ weaken φ (weaken ψ x)

data Con where
  ε : Con
  _▻_ : ∀ Γ -> Type Γ -> Con

data Type Γ where
  type : Type Γ
  _Π_  : (σ : Type Γ) -> Type (Γ ▻ σ) -> Type Γ
  ↑    : Γ ⊢ type     -> Type Γ

data _⊆_ where
  stop : ε ⊆ ε
  skip : ∀ {Γ Δ σ} ->      Γ ⊆ Δ  -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> (ψ : Γ ⊆ Δ) -> Γ ▻ σ ⊆ Δ ▻ Weaken ψ σ

pat : ∀ {Γ Δ} -> Type Δ -> Set
pat {Γ} {Δ} τ = Γ ⊆ Δ ▻ τ

stop   ∘ˢ stop   = stop
skip φ ∘ˢ ψ      = skip (φ ∘ˢ ψ)
keep φ ∘ˢ skip ψ = skip (φ ∘ˢ ψ)
keep φ ∘ˢ keep ψ = subst pat (Weaken-comp _)
                     (keep (φ ∘ˢ ψ))

Weaken ψ  type   = type
Weaken ψ (σ Π τ) = Weaken ψ σ Π Weaken (keep ψ) τ
Weaken ψ (↑ t)   = ↑ (weaken ψ t)

idˢ {ε}     = stop
idˢ {Γ ▻ σ} = subst pat (Weaken-id σ)
                (keep idˢ)

Weaken-id  type   = refl
Weaken-id (σ Π τ) = cong₂ _Π_ (Weaken-id σ)
  (unsubst pat (flip Weaken τ) (Weaken-id σ) (Weaken-id τ))
Weaken-id (↑ t)   = cong ↑ (weaken-id t)

idˢ-left  : ∀ {Γ Δ} {ψ : Γ ⊆ Δ} -> (idˢ ∘ˢ ψ) ≅ ψ
idˢ-left  {ψ = stop  } = refl
idˢ-left  {ψ = skip ψ} =
  trans (sym (cong-subst-removable pat (_∘ˢ skip ψ) (Weaken-id _)))
        (cong₂ (λ σ ψ -> skip {σ = σ} ψ) (Weaken-id _) idˢ-left)
idˢ-left  {ψ = keep ψ} =
  trans (sym (cong-subst-removable pat (_∘ˢ keep ψ) (Weaken-id _)))
        (trans (subst-removable pat (Weaken-comp _) _)
               (cong keep idˢ-left))

idˢ-right : ∀ {Γ Δ} {ψ : Γ ⊆ Δ} -> (ψ ∘ˢ idˢ) ≅ ψ
idˢ-right {ψ = stop  } = refl
idˢ-right {ψ = skip ψ} = cong skip idˢ-right
idˢ-right {ψ = keep ψ} =
  trans (sym (cong-subst-removable pat (keep ψ ∘ˢ_) (Weaken-id _)))
        (trans (subst-removable pat (Weaken-comp _) _)
               (cong keep idˢ-right))

Weaken-comp  type   = refl
Weaken-comp (σ Π τ) = cong₂ _Π_ (Weaken-comp σ)
  (unsubst pat (flip Weaken τ) (Weaken-comp σ) (Weaken-comp τ))
Weaken-comp (↑ t)   = cong ↑ (weaken-comp t)

top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
top = skip idˢ

Pop : ∀ {Γ σ} -> Type Γ -> Type (Γ ▻ σ)
Pop = Weaken top

data _∋_ where
  vz  : ∀ {Γ σ}   -> Γ ▻ σ ∋ Pop σ
  vs_ : ∀ {Γ σ τ} -> Γ     ∋     σ -> Γ ▻ τ ∋ Pop σ

cong-Ws : ∀ {Γ Δ τ} {φ ψ : Γ ⊆ Δ} {σ}
        -> ψ ≅ φ -> Weaken (skip {σ = τ} ψ) σ ≅ Weaken (skip {σ = τ} φ) σ
cong-Ws refl = refl

skip-stop : ∀ {Γ Δ τ} {ψ : Γ ⊆ Δ} {σ}
          -> Pop (Weaken ψ σ) ≅ Weaken (skip {σ = τ} ψ) σ
skip-stop = trans (sym (Weaken-comp _)) (cong-Ws idˢ-left)

keep-stop : ∀ {Γ Δ τ} {ψ : Γ ⊆ Δ} {σ}
          -> Weaken (keep {σ = τ} ψ) (Pop σ) ≅ Pop (Weaken ψ σ)
keep-stop = trans (sym (Weaken-comp _))
                  (trans (trans (cong-Ws idˢ-right) (sym (cong-Ws idˢ-left)))
                         (Weaken-comp _))

weaken-var : ∀ {Γ Δ σ} -> (ψ : Γ ⊆ Δ) -> Γ ∋ σ -> Δ ∋ Weaken ψ σ
weaken-var  stop     ()
weaken-var (skip ψ)  v     = subst (_ ∋_)  skip-stop
                               (vs (weaken-var ψ v))
weaken-var (keep ψ)  vz    = subst (_ ∋_) (sym keep-stop)
                                vz
weaken-var (keep ψ) (vs v) = subst (_ ∋_) (sym keep-stop)
                               (vs (weaken-var ψ v))

weaken-var-id : ∀ {Γ σ} (v : Γ ∋ σ) -> weaken-var idˢ v ≅ v
weaken-var-id  vz    =
  trans (sym (cong-subst-removable pat (flip weaken-var vz) (Weaken-id _)))
        (trans (subst-removable (_ ∋_) (sym keep-stop) vz)
               (irefl (λ σ -> _ ∋ Pop σ) vz (Weaken-id _)))
weaken-var-id (vs v) =
  trans (sym (cong-subst-removable pat (flip weaken-var (vs v)) (Weaken-id _)))
        (trans (subst-removable (_ ∋_) (sym keep-stop) (vs (weaken-var _ v)))
               (cong₃ (λ τ σ (v : _ ∋ σ) -> vs_ {τ = τ} v)
                      (Weaken-id _)
                      (Weaken-id _)
                      (weaken-var-id v)))

weaken-var-comp : ∀ {Γ Δ Θ σ} (φ : Δ ⊆ Θ) (ψ : Γ ⊆ Δ) (v : Γ ∋ σ)
                -> weaken-var (φ ∘ˢ ψ) v ≅ weaken-var φ (weaken-var ψ v)
weaken-var-comp  stop     stop     ()
weaken-var-comp (skip φ)  ψ        v     =
  trans (subst-removable (_ ∋_) skip-stop _)
        (trans (cong₂ (λ σ (v : _ ∋ σ) -> vs v) (Weaken-comp _) (weaken-var-comp φ ψ v))
               (sym (subst-removable (_ ∋_) skip-stop _)))
weaken-var-comp (keep φ) (skip ψ)  v     =
  trans (subst-removable (_ ∋_) skip-stop _)
        (trans (trans (cong₂ (λ σ (v : _ ∋ σ) -> vs v) (Weaken-comp _) (weaken-var-comp φ ψ v))
                      (sym (subst-removable (_ ∋_) (sym keep-stop) _)))
               (cong-subst-removable (_ ∋_) (weaken-var (keep φ)) skip-stop))
weaken-var-comp (keep φ) (keep ψ)  vz    =
  trans (sym (cong-subst-removable pat (flip weaken-var vz) (Weaken-comp _)))
        (trans (trans (trans (subst-removable (_ ∋_) (sym keep-stop) _)
                             (irefl (λ σ -> _ ∋ Pop σ) vz (Weaken-comp _)))
                      (sym (subst-removable (_ ∋_) (sym keep-stop) _)))
               (cong-subst-removable (_ ∋_) (weaken-var (keep φ)) (sym keep-stop)))
weaken-var-comp (keep φ) (keep ψ) (vs v) =
  trans (trans (sym (cong-subst-removable pat (flip weaken-var (vs v)) (Weaken-comp _)))
               (trans (subst-removable (_ ∋_) (sym keep-stop) _)
                      (trans (cong₃ (λ τ σ (v : _ ∋ σ) -> vs_ {τ = τ} v)
                                    (Weaken-comp _)
                                    (Weaken-comp _)
                                    (weaken-var-comp _ _ v))
                             (sym (subst-removable (_ ∋_) (sym keep-stop) _)))))
        (cong-subst-removable (_ ∋_) (weaken-var (keep φ)) (sym keep-stop))

data _⊢_ Γ where
  var  : ∀ {σ}   -> Γ ∋ σ     -> Γ ⊢ σ
  ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ Π τ
  ↓    :            Type Γ    -> Γ ⊢ type

weaken ψ (var v) = var (weaken-var ψ v)
weaken ψ (ƛ b)   = ƛ (weaken (keep ψ) b)
weaken ψ (↓ σ)   = ↓ (Weaken ψ σ)

weaken-id (var v) =
  cong₂ (λ σ (v : _ ∋ σ) -> var v) (Weaken-id _) (weaken-var-id v)
weaken-id (ƛ b)   =
  cong₃ (λ σ τ (b : _ ▻ σ ⊢ τ) -> ƛ b)
        (Weaken-id _)
        (unsubst pat (flip Weaken _) (Weaken-id _) (Weaken-id _))
        (trans (cong-subst-removable pat (flip weaken b) (Weaken-id _))
               (weaken-id b))
weaken-id (↓ σ)   = cong ↓ (Weaken-id σ)

weaken-comp (var v) =
  cong₂ (λ σ (v : _ ∋ σ) -> var v) (Weaken-comp _) (weaken-var-comp _ _ v)
weaken-comp (ƛ b)   =
  cong₃ (λ σ τ (b : _ ▻ σ ⊢ τ) -> ƛ b)
        (Weaken-comp _)
        (unsubst pat (flip Weaken _) (Weaken-comp _) (Weaken-comp _))
        (trans (cong-subst-removable pat (flip weaken b) (Weaken-comp _))
               (weaken-comp b))
weaken-comp (↓ σ)   = cong ↓ (Weaken-comp σ)
