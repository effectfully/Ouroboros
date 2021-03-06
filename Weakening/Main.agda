module Ouroboros.Weakening.Main where

open import Function as F hiding (_∋_)
open import Relation.Binary.HeterogeneousEquality as H hiding (subst; [_])
open import Data.Nat

open import Ouroboros.Prelude

infixl 4 _,_
infixr 5 _Π_
infix  3 _∋_ _⊢_

{-# TERMINATING #-}
mutual
  data Con : ℕ -> Set where
    ε : Con 0
    _,_ : ∀ {n} (Γ : Con n) -> Type Γ -> Con (suc n)

  data Type {n} (Γ : Con n) : Set where
    type : Type Γ
    _Π_  : (σ : Type Γ) -> Type (Γ , σ) -> Type Γ
    ↑    : Γ ⊢ type     -> Type Γ

  data _∋_ : ∀ {n} (Γ : Con n) -> Type Γ -> Set where
    vz  : ∀ {n} {Γ : Con n} {σ}   -> Γ , σ ∋ Pop σ
    vs_ : ∀ {n} {Γ : Con n} {σ τ} -> Γ     ∋ σ     -> Γ , τ ∋ Pop σ

  data _⊢_ {n} (Γ : Con n) : Type Γ -> Set where
    ƛ_   : ∀ {σ τ} -> Γ , σ ⊢ τ -> Γ ⊢ σ Π τ
    ↓    :             Type Γ   -> Γ ⊢ type
    var  : ∀ {σ}   -> Γ ∋ σ    -> Γ ⊢ σ

  rdrop : ∀ {n} -> (i : Fin n) -> Con n -> Con (n ∸ toℕ i)
  rdrop  zero     Γ      = Γ
  rdrop (suc n)  (Γ , σ) = rdrop n Γ

  rinsert : ∀ {n} i (Γ : Con n) -> Type (rdrop i Γ) -> Con (suc n)
  rinsert  zero    Γ      τ = Γ , τ
  rinsert (suc i) (Γ , σ) τ = rinsert i Γ τ , Weaken i σ

  Weaken : ∀ {n} i {Γ : Con n} {σ} -> Type Γ -> Type (rinsert i Γ σ)
  Weaken i  type   = type
  Weaken i (σ Π τ) = Weaken i σ Π Weaken (suc i) τ
  Weaken i (↑ t)   = ↑ (weaken i t)

  Pop : ∀ {n} {Γ : Con n} {σ} -> Type Γ -> Type _
  Pop {σ = σ} = Weaken zero {σ = σ}

  Pop-Weaken : ∀ {n} {i : Fin n} {Γ : Con n} {σ : Type Γ} {τ υ}
             -> Pop (Weaken i {σ = υ} σ) ≅ Weaken (suc i) (Pop {σ = τ} σ)
  Pop-Weaken = Weaken-commute {0} zero _

  weaken : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ⊢ τ -> rinsert i Γ σ ⊢ Weaken i τ
  weaken i (ƛ b)   = ƛ (weaken (suc i) b)
  weaken i (↓ σ)   = ↓ (Weaken i σ)
  weaken i (var v) = var (weaken-var i v)

  weaken-var : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ∋ τ -> rinsert i Γ σ ∋ Weaken i τ
  weaken-var  zero             v     = vs v
  weaken-var (suc i)  {Γ , σ}  vz    = H.subst (_∋_ _) Pop-Weaken
                                          vz
  weaken-var (suc i)  {Γ , σ} (vs v) = H.subst (_∋_ _) Pop-Weaken
                                         (vs (weaken-var i v))

  -- Proofs.

  rdrop-rinsert : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {σ}
                -> rdrop (i +F j) Γ ≅ rdrop (suc (i +F j)) (rinsert (rearrange i) Γ σ)
  rdrop-rinsert  zero           = refl
  rdrop-rinsert (suc i) {_ , _} = rdrop-rinsert i

  turn-rdrop-rinsert : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {σ}
                     -> Type (rdrop (i +F j) Γ)
                     -> Type (rdrop (suc (i +F j)) (rinsert (rearrange i) Γ σ))
  turn-rdrop-rinsert i = H.subst Type (rdrop-rinsert i)

  rdrop-rearrange : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)}
                  -> rdrop (i +F j) Γ ≅ rdrop (rearrange-by i j) (rdrop (rearrange i) Γ)
  rdrop-rearrange  zero           = refl
  rdrop-rearrange (suc i) {_ , _} = rdrop-rearrange i

  turn-rdrop-rearrange : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)}
                       -> Type (rdrop (i +F j) Γ)
                       -> Type (rdrop (rearrange-by i j) (rdrop (rearrange i) Γ))
  turn-rdrop-rearrange i = isubst Con Type (plus-minus-rearrange i) (rdrop-rearrange i)

  rdrop-rearrange-rinsert : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {σ}
                          ->   rinsert (rearrange-by i j) (rdrop (rearrange i) Γ)
                                 (turn-rdrop-rearrange i σ)
                             ≅ rdrop (inject₁ (rearrange i)) (rinsert (i +F j) Γ σ)
  rdrop-rearrange-rinsert  zero           = refl
  rdrop-rearrange-rinsert (suc i) {_ , _} = rdrop-rearrange-rinsert i

  turn-rdrop-rearrange-rinsert : ∀ {n m} (i : Fin n) {j} {Γ : Con (toℕ i + m)} {σ}
                               -> Type (rdrop (rearrange i) Γ)
                               -> Type (rdrop (inject₁ (rearrange i)) (rinsert (i +F j) Γ σ))
  turn-rdrop-rearrange-rinsert i {j} = isubst Con Type (inject₁-rearrange i j) (rdrop-rearrange-rinsert i)
                                     ∘ Weaken (rearrange-by i j)

  contexts-eq : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {τ υ}
              ->   rinsert (inject₁ (rearrange i)) (rinsert (i +F j) Γ υ)
                     (turn-rdrop-rearrange-rinsert i τ)
                 ≅ rinsert (suc (i +F j)) (rinsert (rearrange i) Γ τ) (turn-rdrop-rinsert i υ)
  contexts-eq  zero           = refl
  contexts-eq (suc i) {_ , _} = cong₂ _,_ (contexts-eq i) (Weaken-commute i _)

  Weaken-commute : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} (σ : Type Γ) {τ υ}
                 ->   Weaken (inject₁ (rearrange i)) (Weaken (i +F j)      {σ = υ} σ)
                    ≅ Weaken (suc (i +F j))          (Weaken (rearrange i) {σ = τ} σ)
  Weaken-commute i  type   = irefl Type type (contexts-eq i)
  Weaken-commute i (σ Π τ) = icong₂ Type _Π_ (contexts-eq i) (Weaken-commute i σ) (Weaken-commute (suc i) τ)
  Weaken-commute i (↑ t)   = icong (λ Γ -> Γ ⊢ _) ↑ (contexts-eq i) (weaken-commute i t)

  weaken-commute : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {σ} (t : Γ ⊢ σ) {τ υ}
                 ->   weaken (inject₁ (rearrange i)) {σ = turn-rdrop-rearrange-rinsert i τ}
                        (weaken (i +F j)      {σ = υ} t)
                    ≅ weaken (suc (i +F j))          {σ = turn-rdrop-rinsert           i υ}
                        (weaken (rearrange i) {σ = τ} t)
  weaken-commute i (ƛ b)   = icong³ (λ Γ σ τ -> Γ , σ ⊢ τ) ƛ_
    (contexts-eq i) (Weaken-commute i _) (Weaken-commute (suc i) _) (weaken-commute (suc i) b)
  weaken-commute i (↓ σ)   = icong Type ↓ (contexts-eq i) (Weaken-commute i σ)
  weaken-commute i (var v) = icong² _∋_ var (contexts-eq i) (Weaken-commute i _) (weaken-var-commute i v)

  weaken-var-commute : ∀ {n m j} (i : Fin n) {Γ : Con (toℕ i + m)} {σ} (v : Γ ∋ σ) {τ υ}
                     ->   weaken-var (inject₁ (rearrange i)) (weaken-var (i +F j)      {σ = τ} v)
                        ≅ weaken-var (suc (i +F j))          (weaken-var (rearrange i) {σ = υ} v)
  weaken-var-commute {j = j}  zero            v     {τ} {υ} =
    sym (subst-removable (_∋_ _) Pop-Weaken (vs (weaken-var j v)))
  weaken-var-commute {j = j} (suc i) {Γ , σ}  vz    {τ} {υ} =
    cong-subst-addable-both (_∋_ _) (_∋_ _)
      (weaken-var (suc (inject₁ (rearrange i))) {σ = turn-rdrop-rearrange-rinsert i υ})
      (weaken-var (suc (suc (i +F j)))          {σ = turn-rdrop-rinsert          i τ})
       Pop-Weaken Pop-Weaken _ _
      (subst-addable-both (_∋_ _) (_∋_ _) Pop-Weaken Pop-Weaken _ _
         (irefl² (λ Γ σ -> Γ , σ ∋ Pop σ) vz (contexts-eq i) (Weaken-commute i _)))
  weaken-var-commute {j = j} (suc i) {Γ , σ} (vs v) {τ} {υ} =
    cong-subst-addable-both (_∋_ _) (_∋_ _)
      (weaken-var (suc (inject₁ (rearrange i))) {σ = turn-rdrop-rearrange-rinsert i υ})
      (weaken-var (suc (suc (i +F j)))          {σ = turn-rdrop-rinsert           i τ})
       Pop-Weaken Pop-Weaken _ _
      (subst-addable-both (_∋_ _) (_∋_ _) Pop-Weaken Pop-Weaken _ _
         (icong²₂ _∋_ (λ v τ -> vs_ {τ = τ} v)
            (contexts-eq i) (Weaken-commute i _) (weaken-var-commute i v) (Weaken-commute i _)))
