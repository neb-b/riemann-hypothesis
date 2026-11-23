module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

noncomputable section

namespace GlobalTheory.SUVol.TamModel

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.UCls.Model GlobalTheory.SUVol
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Up.Definite
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sEquiv_refl (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) (g) : SEquiv G L M g g :=
  ⟨1, by rw [SUVol.ratM_one]; exact ⟨(isKM_one _ G L M).1, det_one⟩, 1, isKM_one _ G L M, det_one, by
    rw [SUVol.ratM_one]; simp⟩

theorem sEquiv_trans {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b d}
    (h : SEquiv G L M a b) (h' : SEquiv G L M b d) : SEquiv G L M a d := by
  obtain ⟨γ, hγ, k, hk, hd, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', hd', rfl⟩ := h'
  exact ⟨γ' * γ, by
    rw [SUVol.ratM_mul]; exact ⟨isUA_mul _ G hγ'.1 hγ.1, by rw [det_mul, hγ'.2, hγ.2, one_mul]⟩,
    k * k', isKM_mul _ G L M hk hk', by rw [det_mul, hd, hd', one_mul], by
    rw [SUVol.ratM_mul]; simp only [Matrix.mul_assoc]⟩

theorem sEquiv_symm {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b}
    (h : SEquiv G L M a b) : SEquiv G L M b a := by
  obtain ⟨γ, hγ, k, hk, hkd, rfl⟩ := h
  have hd1 : γ.det = 1 := by
    have h1 := hγ.2
    rw [ratM_det] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1
  have hd : IsUnit γ.det := hd1 ▸ isUnit_one
  have hi : ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
    rw [← SUVol.ratM_mul, nonsing_inv_mul γ hd, SUVol.ratM_one]
  refine ⟨γ⁻¹, ⟨by rw [← inv_eq_left_inv hi]; exact isUA_inv _ G hγ.1, ?_⟩, k⁻¹, isKM_inv _ G L M hk, ?_, ?_⟩
  · have := congrArg det hi
    rwa [det_mul, hγ.2, mul_one, det_one] at this
  · have := congrArg det (nonsing_inv_mul k hk.1.1)
    rwa [det_mul, hkd, mul_one, det_one] at this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
      Matrix.one_mul]

theorem exists_sReps (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) :
    ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), Nonempty J ∧ IsSReps G L M s := by
  let S : Setoid {g // IsSA G g} :=
    ⟨fun a b => SEquiv G L M a.1 b.1, fun a => sEquiv_refl G L M a.1, sEquiv_symm, sEquiv_trans⟩
  refine ⟨Quotient S, fun q => q.out.1, ⟨Quotient.mk S ⟨1, (isKM_one _ G L M).1, det_one⟩⟩, fun q => q.out.2,
    fun i j h => ?_, fun g hg => ⟨Quotient.mk S ⟨g, hg⟩, Quotient.mk_out (s := S) ⟨g, hg⟩⟩⟩
  rw [← i.out_eq, ← j.out_eq]
  exact Quotient.sound h



end GlobalTheory.SUVol.TamModel
