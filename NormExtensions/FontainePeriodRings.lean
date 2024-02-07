/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Polynomial.Laurent
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import NormExtensions.CpDef

/-!
# Fontaine's period rings

Fontaine's period rings are certain rings that can detect interesting properties of Galois
representations. They also play a key role in comparison theorems between cohomology theories.

We formalize the definitions of the Fontaine period rings `K_alg` and `B_HT` and provide a
strategy for a formalization of the definition of the ring `B_dR`.

## Main Definitions

* `K_alg` : the algebraic closure of a `p`-adic field `K`.
* `B_HT` : the ring of Laurent polynomials `ℂ_[p][X, X⁻¹]`


## Tags

Fontaine period rings, Galois representation theory, p-adic Hodge theory
-/

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

open MvPolynomial

/-- The first example of a Fontaine period ring is given by the algebraic closure `K^alg` of a
 `p`-adic field `K`. -/
def K_alg {K : Type*} [Field K] [Algebra ℚ_[p] K]
  (_h_fin : FiniteDimensional ℚ_[p] K) :=
AlgebraicClosure K

instance  {K : Type*} [Field K] [Algebra ℚ_[p] K] (h_fin : FiniteDimensional ℚ_[p] K) :
 Inhabited (K_alg p h_fin) := AlgebraicClosure.inhabited _

/-- The ring `B_HT` is defined as the ring of Laurent polynomials `ℂ_[p][X, X⁻¹]`. -/
def B_HT := LaurentPolynomial ℂ_[p]

instance : Inhabited (B_HT p) := ⟨LaurentPolynomial.C 0⟩

/-!  We know present the strategy for the formalization of `B_dR`. An expanded explanation of the
mathematical construction is provided in the accompanying paper. -/
instance : Fact ((PadicComplex.valuedField p).v ↑p ≠ 1) :=
⟨by simp only [PadicComplex.valuation_p, one_div, Ne.def, inv_eq_one, Nat.cast_eq_one,
      Nat.Prime.ne_one hp.1, not_false_iff]⟩

/-- First, we define a ring `E p` as the perfection of `𝓞_ℂ|[p]/(p)`. -/
def E :=  PreTilt ℂ_[p] (PadicComplex.valuedField p).v 𝓞_ℂ_[p]
(Valuation.integer.integers _) p

instance : CommRing (E p) :=PreTilt.instCommRingPreTilt ℂ_[p] (PadicComplex.valuedField p).v
  𝓞_ℂ_[p] (Valuation.integer.integers _) p

instance : Inhabited (E p) := ⟨0⟩

/-- `A_inf p` is the ring of Witt vectors of `E p`. -/
def A_inf := WittVector p (E p)

instance : CommRing (A_inf p) := WittVector.instCommRingWittVector _ _

instance : Inhabited (A_inf p) := ⟨0⟩

/-- `B_inf_plus p` is the ring `(A_inf p)[1/p]`. -/
def B_inf_plus := Localization.Away (p : A_inf p)
instance : CommRing (B_inf_plus p) := Localization.instCommRingLocalizationToCommMonoid

instance : Inhabited (B_inf_plus p) := ⟨0⟩

/-- The missing part in the definition of `B_dR p` is the construction of a canonical ring
homomorphism from `B_inf_plus p` to `ℂ_[p]`.-/
noncomputable def theta : RingHom (B_inf_plus p) ℂ_[p] := sorry

/-- The map `theta` is surjective. -/
lemma theta.surjective : Function.Surjective (theta p) := sorry

instance : WithIdeal (B_inf_plus p) := ⟨RingHom.ker (theta p)⟩

/--`B_dR_plus p` is the completion of `B_inf_plus p` with respect to the ideal `ker(theta)`. -/
def B_dR_plus := UniformSpace.Completion (B_inf_plus p)

instance : CommRing (B_dR_plus p) := UniformSpace.Completion.commRing (B_inf_plus p)

/-- Finally, `B_dR p` is the fraction ring of `B_dR_plus p`. It can be shown that it is in fact a
field. -/
def B_dR := FractionRing (B_dR_plus p)
