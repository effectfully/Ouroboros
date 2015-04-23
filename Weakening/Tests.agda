module Ouroboros.Weakening.Tests where

open import Ouroboros.Weakening.Main

open import Relation.Binary.PropositionalEquality

test-1 : Type ε
test-1 = type Π ↑ (var vz)

test-2 : Type ε
test-2 = type Π ↑ (var vz) Π ↑ (var (vs vz))

test-3 : Type ε
test-3 = type Π ↑ (var vz) Π ↑ (var (vs vz)) Π type Π ↑ (var vz)

test-4 : Type (ε , type , type Π type , type)
test-4 = ↑ (var (vs (vs vz))) Π ↑ (var (vs vz)) Π type Π ↑ (var vz)

test-5 :    Pop {σ = type} test-4
         ≡ (↑ (var (vs (vs (vs vz)))) Π ↑ (var (vs (vs vz))) Π type Π ↑ (var vz))
test-5 = refl
