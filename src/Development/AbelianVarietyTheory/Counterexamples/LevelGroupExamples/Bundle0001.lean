module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ChosenEqOfAllRules
section
noncomputable section

namespace GlobalTheory.SupNormExample

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

end GlobalTheory.SupNormExample
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetTest

open MvPolynomial Formalism.L2.Pj

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem orig_eq : orig R ι = MvPolynomial.idealOfVars ι R := rfl

theorem mk_eq_zero_iff (p : MvPolynomial ι R) :
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, orig_eq, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE [Fintype ι] [DecidableEq ι] (e : ι →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]

theorem jetMap_mk {κ : Type} (φ : ι → MvPolynomial κ R) (hφ : ∀ i, φ i ∈ orig R κ) (p : MvPolynomial ι R) :
    (jetMap (m := m) φ hφ) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetAug_mk (p : MvPolynomial ι R) :
    (jetAug : Jet R ι m →ₐ[R] R) (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change aeval (fun _ => (0 : R)) p = _
  simp

end GlobalTheory.JetTest
end
end

