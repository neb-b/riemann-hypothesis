module

public import Development.WeilBound.CoreStatements.ThetaDilations.Bounded
public import Development.WeilBound.CoreStatements.ThetaDilations.FstarDil
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemma
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem sb_indL {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] {a : ℕ} (ha : 0 < a) :
    SB (indL (F := F) (ι := ι) a) := by
  have := (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.1
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
  have e : indL (F := F) (ι := ι) a = ind 0 (LN F ι 1) ∘ Homeomorph.smul (uA (Units.mk0 (a : F) ha')) := by
    funext u
    have h : (∀ i, (a : A F) * u i ∈ Oh F) ↔ uA (Units.mk0 (a : F) ha') • u - 0 ∈ LN F ι 1 := by
      rw [sub_zero]
      refine forall_congr' fun i => ?_
      have : (uA (Units.mk0 (a : F) ha') • u) i = (a : A F) * u i := by simp [uA, Units.smul_def]
      simp [this]
    by_cases hu : ∀ i, (a : A F) * u i ∈ Oh F
    · exact (Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_mem (h.1 hu)).symm
    · exact (Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_not (mt h.2 hu)).symm
  exact e ▸ sb_homeo (sb_ind 0 (co_LN one_pos)) _

theorem bounded_a : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∃ C : ℝ, ∀ a : ℕ, 0 < a → ∀ x : InfinitePlace F → ℝ, SB (indL (F := F) (ι := ι) a) ∧ ‖((∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) - eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I))‖ ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM Ω _ Pr gf gi hC
  obtain ⟨C, hb⟩ := bounded F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC _ (sb_indL one_pos)
  refine ⟨C, fun a ha x => ⟨sb_indL ha, ?_⟩⟩
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set τ : InfinitePlace F → ℂ := fun w => ((((a : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * ((x w : ℂ) + Complex.I) with hτ
  have him : ∀ w, (τ w).im = ((a : ℝ) ^ 2)⁻¹ := fun w => by simp only [hτ, Complex.im_ofReal_mul]; simp
  have hp : ∀ w, 0 < (τ w).im := fun w => by rw [him]; positivity
  have e1 : opD 1 (algebraMap F (A F) a) (indL (F := F) (ι := ι) 1) = indL a := by
    funext u
    have h : (∀ i, ((1 : ℕ) : A F) * (algebraMap F (A F) a • u) i ∈ Oh F) ↔ ∀ i, (a : A F) * u i ∈ Oh F := by
      simp only [Nat.cast_one, one_mul, Pi.smul_apply, smul_eq_mul, map_natCast]
    simp only [opD, indL, Set.indicator, Complex.ofReal_one, one_mul]
    classical
    convert if_congr h (rfl : (1 : ℂ) = 1) (rfl : (0 : ℂ) = 0) <;> rfl
  have e2 : (fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) = fun w => (x w : ℂ) + Complex.I := by
    funext w; simp only [hτ, map_natCast]; push_cast; field_simp
  have e3 := fun ω => (_root_.GlobalTheory.CompanionTheory.SW.ThetaUD.main F ψ hψ ι M B ρ P hQ _ _ (hC.2.2.2.1 ω) (indL 1) τ).2.1 a ha'
  have e4 := (ei_inv F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ (sb_indL one_pos) τ hp).2.1 a ha'
  rw [e1, e2] at e4
  simp only [e1, e2] at e3
  have h2 := hb τ hp
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have := hQ.1
    rw [IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hw : wt M τ = ((a : ℝ) ^ (Module.finrank ℚ F * M))⁻¹ := by
    simp only [wt, him, Real.sqrt_inv, Real.sqrt_sq haR.le, Finset.prod_const, Finset.card_univ, hcard, ← pow_mul,
      inv_pow, mul_comm M]
  simp only [e3, e4]
  rwa [hw, inv_mul_le_iff₀ (by positivity), mul_comm] at h2

end PositivityTheory.PlacePermOperatorBicommutantSpan
