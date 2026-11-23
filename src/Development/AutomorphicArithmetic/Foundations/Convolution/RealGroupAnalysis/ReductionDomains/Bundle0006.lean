module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Unimod
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.unimod :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (μ : Measure (G1 F)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro F _ _ μ _
  have h0 : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) ≠ 0 := fun g h => by
    have e := map_mul (Measure.modularCharacter (G := G1 F)) g g⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at e
    exact one_ne_zero e
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h3F : (3 : F) ≠ 0 := by norm_num
  let two : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 2 h2F)
  have h2 : (two : A F) = 2 := map_ofNat (algebraMap F (A F)) 2
  have h4 : ∀ b : A F, (Measure.modularCharacter (nU (4 * b)) : ℝ≥0) = Measure.modularCharacter (nU b) := by
    intro b
    have e := congrArg (Measure.modularCharacter (G := G1 F)) (M.mD_mul_nU two b)
    rw [map_mul, map_mul, mul_comm] at e
    have c := mul_right_cancel₀ (h0 _) e
    rw [h2] at c
    norm_num at c
    exact c.symm
  have hn : ∀ c : A F, (Measure.modularCharacter (nU c) : ℝ≥0) = 1 := by
    intro c
    have h3 : (3 : A F) * (rt (3⁻¹ : F) * c) = c := by
      have : (3 : A F) * rt (3⁻¹ : F) = 1 := by
        rw [show (3 : A F) = rt (3 : F) from (map_ofNat (algebraMap F (A F)) 3).symm, ← map_mul, mul_inv_cancel₀ h3F, map_one]
      rw [← mul_assoc, this, one_mul]
    set b : A F := rt (3⁻¹ : F) * c with hb
    have e := h4 b
    rw [show (4 : A F) * b = 3 * b + b by ring, M.nU_add, map_mul, h3] at e
    exact mul_right_cancel₀ (h0 (nU b)) (e.trans (one_mul _).symm)
  have hw : (Measure.modularCharacter (wW F) : ℝ≥0) = 1 := by
    have e : wW F * wW F * (wW F * wW F) = 1 := by
      refine Subtype.ext ?_
      rw [M.val_mul, M.val_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp [wW, Matrix.mul_apply, Fin.sum_univ_two]
    have e' := congrArg (Measure.modularCharacter (G := G1 F)) e
    rw [map_mul, map_mul, map_one] at e'
    have e4 : (Measure.modularCharacter (wW F) : ℝ≥0) ^ 4 = 1 := by rw [← e']; ring
    exact (pow_eq_one_iff.1 e4).resolve_right (by norm_num)
  have hall : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) = 1 := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(gen F).1]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | hx
      · exact hn c
      · rw [Set.mem_singleton_iff.1 hx]; exact hw
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
    | inv x _ hx =>
      have e := map_mul (Measure.modularCharacter (G := G1 F)) x x⁻¹
      rw [mul_inv_cancel, map_one, hx, one_mul] at e
      exact e.symm
  haveI : μ.InnerRegular := inferInstance
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from hall g, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.volD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F), M₀.μ M₀.D < ⊤ := by
  intro F _ _ _ M₀
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨C, ρ, hC, hρ, hcov⟩ := M.ideleCover F c hc
  obtain ⟨hSm, hfin⟩ := M.siegJ F M₀ C ρ hC hρ
  obtain ⟨⟨σ, hσ⟩, hcos⟩ := M.rowCosets F
  set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS
  set u : G1 F → ℝ≥0∞ := Set.indicator S 1 with hu
  have hum : Measurable u := measurable_one.indicator hSm
  have hSinv : ∀ (b : A F) g, nU b * g ∈ S ↔ g ∈ S := by
    have key : ∀ (b : A F) g, g ∈ S → nU b * g ∈ S := by
      rintro b g ⟨b', n, x, hx, k, hk, rfl⟩
      exact ⟨b + b', n, x, hx, k, hk, by rw [M.nU_add]; simp only [mul_assoc]⟩
    refine fun b g => ⟨fun h => ?_, key b g⟩
    have := key (-b) _ h
    rwa [M.nU_neg, inv_mul_cancel_left] at this
  have huinv : ∀ (b : A F) g, u (nU b * g) = u g := by
    intro b g
    by_cases h : g ∈ S
    · rw [hu, Set.indicator_of_mem h, Set.indicator_of_mem ((hSinv b g).2 h)]; rfl
    · rw [hu, Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hSinv b g).1 h'))]
  have hcover : ∀ g : G1 F, 1 ≤ ∑' r, u (ratS F (σ r) * g) := by
    intro g
    obtain ⟨γ, b, a, k, hk, heq, hle⟩ := hred g
    obtain ⟨t, n, x, hx, hta⟩ := hcov a hle
    have hmem : mD (IdeleGroup.diagonal F t) * ratS F γ ∈ Gam F :=
      (Gam F).mul_mem (M.mD_diag_mem t) ⟨γ, rfl⟩
    obtain ⟨⟨r, ξ⟩, hp, -⟩ := hcos σ hσ ⟨_, hmem⟩
    have hp' : mD (IdeleGroup.diagonal F t) * ratS F γ = nU (rt ξ) * ratS F (σ r) := hp
    have hin : nU (rt ξ) * (ratS F (σ r) * g) ∈ S := by
      refine ⟨((IdeleGroup.diagonal F t : (A F)ˣ) : A F) ^ 2 * b, n, x, hx, k, hk, ?_⟩
      rw [← mul_assoc, ← hp', mul_assoc, heq, ← hta, M.mD_mul, ← mul_assoc, ← mul_assoc, M.mD_mul_nU]
      simp only [mul_assoc]
    have hone : u (ratS F (σ r) * g) = 1 := by
      rw [← huinv (rt ξ), hu, Set.indicator_of_mem hin]; rfl
    calc (1 : ℝ≥0∞) = u (ratS F (σ r) * g) := hone.symm
      _ ≤ ∑' r, u (ratS F (σ r) * g) := le_tsum (fun r => u (ratS F (σ r) * g)) r
  have hfs : ∀ g, ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) = u g := by
    intro g
    simp only [huinv]
    rw [lintegral_const, Measure.restrict_apply_univ, adeleMeasure_fundamentalSet, mul_one]
  calc M₀.μ M₀.D = ∫⁻ _ in M₀.D, 1 ∂M₀.μ := by simp
    _ ≤ ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := lintegral_mono fun g => hcover g
    _ = M.J0 M₀ u := by
      rw [M.unfL F M₀ σ u hσ hum (fun ξ g => huinv _ g)]
      simp only [hfs]
    _ < ⊤ := hfin
end

