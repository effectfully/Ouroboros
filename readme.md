# [Ouroboros](en.wikipedia.org/wiki/Ouroboros)

This repository contains some thoughts about representing dependent type theory in dependent type theory.

# Weakening

Weakening is defined as a type-preserving renaming.

This function drops `i' elements from a context, starting from the right.

```
rdrop : ∀ {n} -> (i : Fin n) -> Con n -> Con (n ∸ toℕ i)
rdrop  zero     Γ      = Γ
rdrop (suc n)  (Γ , σ) = rdrop n Γ
```

This function inserts a type into a context at the `i' position, starting from the right.
It also weakens all traversed types to make them indexed by the new context.

```
rinsert : ∀ {n} i (Γ : Con n) -> Type (rdrop i Γ) -> Con (suc n)
rinsert  zero    Γ      τ = Γ , τ
rinsert (suc i) (Γ , σ) τ = rinsert i Γ τ , Weaken i σ
```

This function weakens a type. Each time we go under a binder (`_Π_` in this case), we increase the "weakening index" (I don't know what the right wording is).

```
Weaken : ∀ {n} i {Γ : Con n} {σ} -> Type Γ -> Type (rinsert i Γ σ)
Weaken i  type   = type
Weaken i (σ Π τ) = Weaken i σ Π Weaken (suc i) τ
Weaken i (↑ t)   = ↑ (weaken i t)
```

This function weakens a term. `ƛ_` is the binder now.

```
weaken : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ⊢ τ -> rinsert i Γ σ ⊢ Weaken i τ
weaken i (ƛ b)   = ƛ (weaken (suc i) b)
weaken i (↓ σ)   = ↓ (Weaken i σ)
weaken i (var v) = var (weaken-var i v)
```

This function weakens a variable. If the weakening index is `zero`, then the variable points to the untouched part of the context, and hence we need to increment it, because the context now contains an additional type, that must be skipped. If the weakening index is `suc i` for some `i` and the variable points to the head of the context, then we don't need to weaken it, since the context is changed somewhere forward. 

``` 
weaken-var : ∀ {n} i {Γ : Con n} {σ τ} -> Γ ∋ τ -> rinsert i Γ σ ∋ Weaken i τ
weaken-var  zero             v     = vs v
weaken-var (suc i)  {Γ , σ}  vz    = H.subst (_∋_ _) Pop-Weaken
                                        vz
weaken-var (suc i)  {Γ , σ} (vs v) = H.subst (_∋_ _) Pop-Weaken
                                       (vs (weaken-var i v))
```

A quick illustation taken from the `Tests` module:

```
test-4 : Type (ε , type , type Π type , type)
test-4 = ↑ (var (vs vs vz)) Π ↑ (var (vs vz)) Π type Π ↑ (var vz)

test-6 : Weaken (suc (suc zero)) {σ = type} test-4
         ≡ (↑ (var (vs vs vs vz)) Π ↑ (var (vs vz)) Π type Π ↑ (var vz))
test-6 = refl
```

Here `Weaken` does what expected, i.e. inserts `type` to the context of `test-4` at the second position, starting from zero and from the right:

```
ε {- 3 -} , type {- 2 -} , type Π type {- 1 -} , type {- 0 -}
```

transforming the context into `ε , type , type , (type Π type) , type`. The only variable, that points to the untouched part of the context is `vs vs vs vz`, which was `vs vs vz` previously. Other variables remain unchanged. 