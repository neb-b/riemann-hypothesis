module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.KAvgDeriv

variable {n : ℕ} {ε : Fin n → Bool}

theorem hs_nonneg' (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ hs g := by
  show 0 ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2
  positivity

theorem continuous_hs' : Continuous (fun g : GlobalTheory.TypeSum.Mx n => hs g) := by
  show Continuous (fun g : GlobalTheory.TypeSum.Mx n => ∑ i, ∑ j, ‖g i j‖ ^ 2)
  fun_prop

theorem mul_exp_conj {P : GlobalTheory.TypeSum.Mx n} (hP : IsUnit P) (X : GlobalTheory.TypeSum.Mx n) (t : ℝ) :
    P * NormedSpace.exp (t • (P⁻¹ * X * P)) = NormedSpace.exp (t • X) * P := by
  rw [← GlobalTheory.TypeSum.GrowthAtPlace.conj_exp hP X t, ← mul_assoc, ← mul_assoc,
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP), one_mul]

theorem bound_K (ε : Fin n → Bool) : ∃ M : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), 1 + hs (Formalism.REAL.toMK k) ≤ M := by
  have hc : Continuous fun k : ↥(Formalism.REAL.KG ε) => 1 + hs (Formalism.REAL.toMK k) :=
    continuous_const.add (continuous_hs'.comp
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k => ?_⟩
  have h := hC k (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem bound_e (e : ↥(Formalism.REAL.KG ε) → ℂ) (he : Continuous e) : ∃ E : ℝ, 0 ≤ E ∧ ∀ k, ‖e k‖ ≤ E := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k => (hC k (Set.mem_univ _)).trans (le_max_left _ _)⟩

theorem bound_line (y X : GlobalTheory.TypeSum.Mx n) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 + hs (y * NormedSpace.exp (t • X)) ≤ M := by
  have hs1 : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
    have h : Continuous (NormedSpace.exp : GlobalTheory.TypeSum.Mx n → GlobalTheory.TypeSum.Mx n) := by
      open Matrix.Norms.Operator in exact NormedSpace.exp_continuous
    exact h.comp hs1
  have hc : Continuous fun t : ℝ => 1 + hs (y * NormedSpace.exp (t • X)) :=
    continuous_const.add (continuous_hs'.comp (continuous_const.mul hexp))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

private theorem isUnit_toMK (k : ↥(Formalism.REAL.KG ε)) : IsUnit (Formalism.REAL.toMK k) :=
  Units.isUnit _

private theorem toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm (k : ↥(Formalism.REAL.KG ε)) :
    (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK k = Formalism.REAL.Jm ε :=
  (k : Formalism.REAL.UJ ε).2

private theorem toMK_mem_UJset (k : ↥(Formalism.REAL.KG ε)) : Formalism.REAL.toMK k ∈ UJset ε :=
  toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k

private theorem mul_mem_UJset_height {g h : GlobalTheory.TypeSum.Mx n} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hh' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hh
  show (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h by
      simp only [mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset_of_mem_lieSet' {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hG : Formalism.REAL.inG ε (t • X) := by
    show (t • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (t • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]
  exact Formalism.REAL.f1alg_exp_inUJ ε (t • X) hG

private theorem toMK_inv_mul_mul_toMK_mem_lieSet (k : ↥(Formalism.REAL.KG ε)) {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) :
    (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k ∈ lieSet ε :=
  GlobalTheory.TypeSum.GrowthAtPlace.conj_lie (isUnit_toMK k) (toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k) hX

private theorem mem_lieSet_of_mem_map_toMK_conj (k : ↥(Formalism.REAL.KG ε)) {l : List (GlobalTheory.TypeSum.Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) :
    ∀ Y ∈ l.map (fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k), Y ∈ lieSet ε := by
  intro Y hY
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
  exact toMK_inv_mul_mul_toMK_mem_lieSet k (hl Z hZ)

private theorem one_add_hs_nonneg (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ 1 + hs g := by
  have := hs_nonneg' g
  linarith

private theorem mul_one_add_hs_mul_pow_le_abs_mul_pow {N : ℕ} {C MK ML : ℝ} {z k : GlobalTheory.TypeSum.Mx n}
    (hMK : 1 + hs k ≤ MK) (hML : 1 + hs z ≤ ML) :
    C * (1 + hs (z * k)) ^ N ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N := by
  have a0 := one_add_hs_nonneg (1 : GlobalTheory.TypeSum.Mx n)
  have k0 := one_add_hs_nonneg k
  have z0 := one_add_hs_nonneg z
  have h1 : 1 + hs (z * k) ≤ (1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML := by
    have h := GlobalTheory.TypeSum.GrowthAtPlace.one_add_hs_conj_le (1 : GlobalTheory.TypeSum.Mx n) z k
    rw [one_mul] at h
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMK a0) hML z0 (mul_nonneg a0 (k0.trans hMK)))
  calc C * (1 + hs (z * k)) ^ N ≤ |C| * (1 + hs (z * k)) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (one_add_hs_nonneg _) N)
    _ ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_add_hs_nonneg _) h1 N) (abs_nonneg C)

theorem avg_derFam_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  intro n ε N F hF hG hM e he
  obtain ⟨E, hE0, hE⟩ := bound_e e he
  obtain ⟨MK, hMK⟩ := bound_K (n := n) ε
  refine ⟨?_, ?_⟩
  · intro l hl X hX g hg
    have hXl : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hX
      · exact hl Y hY
    obtain ⟨C, hC⟩ := hG (X :: l) hXl
    obtain ⟨C0, hC0⟩ := hG l hl
    obtain ⟨ML, hML⟩ := bound_line g X
    have hgt : ∀ t : ℝ, g * NormedSpace.exp (t • X) ∈ UJset ε := fun t => mul_mem_UJset_height hg (exp_smul_mem_UJset_of_mem_lieSet' hX t)
    have hb : ∀ (L : List (GlobalTheory.TypeSum.Mx n)) (C : ℝ),
        (∀ k : ↥(Formalism.REAL.KG ε), ∀ z ∈ UJset ε,
          ‖F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) z‖ ≤ C * (1 + hs z) ^ N) →
        ∀ k : ↥(Formalism.REAL.KG ε), ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          ‖e k * F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
            (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k)‖
            ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N) := by
      intro L C hC k t ht
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height (hgt t) (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) (hML t ht)))
        (norm_nonneg _) hE0
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Formalism.REAL.muK ε) (x₀ := (0 : ℝ))
      (F := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (F' := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F ((X :: l).map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (bound := fun _ => E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N))
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall fun t => he.aestronglyMeasurable.mul (hM l hl _ (hgt t)))
      (Integrable.mono' (integrable_const (E * (|C0| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N)))
        (he.aestronglyMeasurable.mul (hM l hl _ (hgt 0)))
        (Filter.Eventually.of_forall fun k => hb l C0 hC0 k 0 h0))
      (he.aestronglyMeasurable.mul (hM (X :: l) hXl _ (hgt 0)))
      (Filter.Eventually.of_forall fun k t ht => hb (X :: l) C hC k t ht)
      (integrable_const _)
      (Filter.Eventually.of_forall fun k t _ => by
        have hk := isUnit_toMK k
        have hm : ∀ s : ℝ, g * NormedSpace.exp (s • X) * Formalism.REAL.toMK k =
            g * Formalism.REAL.toMK k * NormedSpace.exp (s • ((Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)) := by
          intro s
          rw [mul_assoc g (Formalism.REAL.toMK k), mul_exp_conj hk X s, mul_assoc]
        have hd := GlobalTheory.TypeSum.IsDerFam.hasDerivAt_exp hF (mem_lieSet_of_mem_map_toMK_conj k hl) (toMK_inv_mul_mul_toMK_mem_lieSet k hX)
          (mul_mem_UJset_height hg (toMK_mem_UJset k)) t
        simp only [hm]
        exact hd.const_mul (e k))
    refine key.2.congr_deriv ?_
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  · intro l hl
    obtain ⟨C, hC⟩ := hG l hl
    refine ⟨(Formalism.REAL.muK ε).real Set.univ * E * |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK) ^ N,
      fun g hg => ?_⟩
    have hk : ∀ k : ↥(Formalism.REAL.KG ε),
        ‖e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) (g * Formalism.REAL.toMK k)‖
          ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * (1 + hs g)) ^ N) := by
      intro k
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height hg (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) le_rfl))
        (norm_nonneg _) hE0
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hk)).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    ring

end GlobalTheory.KAvgDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectors
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

theorem casimir_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hX, hY⟩ := _root_.GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet n ε
  have hG := _root_.GlobalTheory.TypeSum.CasEquiv.casOp_equivariant n ε H σ h
  obtain ⟨u, χ, hu, hu0, hχ⟩ := _root_.GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp n ε H σ _ _ (kB ε) (pB ε) h hX hY fun k hk v hv => hG k (K_le_UJ hk) v hv
  have hχr : (starRingEnd ℂ) χ = χ := by
    have e := inner_casOp h.1 hX hY hu hu
    rw [hχ, inner_smul_left, inner_smul_right] at e
    have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hu0
    exact (mul_right_cancel₀ hne e).symm
  refine ⟨χ, fun v hv => ?_⟩
  have hws : Sm ε σ (casOp σ (kB ε) (pB ε) v - χ • v) :=
    (smooth (Jm ε) σ).sub_mem (sm_casOp h.1 hX hY hv) ((smooth (Jm ε) σ).smul_mem χ hv)
  have h0 : ∀ g ∈ UJset ε,
      ((innerSL ℂ (casOp σ (kB ε) (pB ε) v - χ • v) : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) (σ g u) = 0 := by
    intro g hg
    have hgu := hu.translate h.1 hg
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left, inner_smul_left, hχr]
    rw [← inner_casOp h.1 hX hY hv hgu, hG g hg u hu, hχ, map_smul, inner_smul_right, sub_self]
  have hz := h.eq_zero_of_orbit (sobCont_inner _) hu hu0 h0 hws
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hz
  simp only [casOp, sub_sub, sub_eq_zero] at hz
  rw [hz, add_comm]

end GlobalTheory.TypeSum.CasBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  intro n ε H _ _ _ σ h d L hL x hx
  have hd : ∀ (v : Fin d → H), (∀ a, Sm ε σ (v a)) → ∀ X ∈ lieSet ε, ∀ y ∈ UJset ε,
      HasDerivAt (fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X)) (v a)))
        (∑ a, L a (σ y (dRep σ X (v a)))) 0 := by
    intro v hv X hX y hy
    refine HasDerivAt.fun_sum fun a _ => ?_
    simpa using CoefLow.hasDerivAt_coef h (hL a) (hv a) hX hy 0
  have hw : ∀ (u : List (Ltr ε)) (a : Fin d), Sm ε σ (wordV σ u (x a)) := by
    intro u a
    induction u with
    | nil => exact hx a
    | cons z u ih =>
      rcases z with X | k
      · exact Sm.word h.1 ih (l := [X.1]) (by simpa using X.2)
      · exact Sm.translate h.1 ih (K_le_UJ k.2)
  refine ⟨⟨fun l y => ∑ a, L a (σ y (Dw σ l (x a))), fun _ _ => rfl, fun l hl X hX g hg => ?_, fun l hl => ?_⟩,
    fun u => ?_⟩
  · exact hd _ (fun a => Sm.word h.1 (hx a) hl) X hX g hg
  · exact continuousOn_finsetSum _ fun a _ => h.continuousOn_coef (hL a) (Sm.word h.1 (hx a) hl)
  · induction u with
    | nil => exact fun _ _ => rfl
    | cons z u ih =>
      intro y hy
      rcases z with X | k
      · have e : (fun t : ℝ => wordF u (fun y => ∑ a, L a (σ y (x a))) (y * NormedSpace.exp (t • X.1))) =
            fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X.1)) (wordV σ u (x a))) :=
          funext fun t => ih _ (mul_mem_UJ hy (exp_mem_UJ X.2 t))
        exact (congrArg (fun f => deriv f 0) e).trans (hd _ (hw u) X.1 X.2 y hy).deriv
      · refine (ih _ (mul_mem_UJ hy (K_le_UJ k.2))).trans (Finset.sum_congr rfl fun a _ => ?_)
        rw [sigma_mul h.1 hy (K_le_UJ k.2)]
        rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem wordF_fam {n : ℕ} {ε : Fin n → Bool} {N : ℕ} {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ}
    (h1 : ∀ g ∈ UJset ε, F [] g = f g) (h2 : IsDerFam ε F) (h3 : FamGrowth ε N F) (u : List (Ltr ε)) :
    ∃ G : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, G [] g = wordF u f g) ∧ IsDerFam ε G ∧ FamGrowth ε N G := by
  induction u with
  | nil => exact ⟨F, h1, h2, h3⟩
  | cons x u ih =>
    obtain ⟨G, k1, k2, k3⟩ := ih
    rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
    · refine ⟨fun l => G (l ++ [X]), fun g hg => (CSm.rder_eq k1 k2 hX hg).symm, fun l hl Y hY g hg => ?_,
        fun l hl => k3 _ ?_⟩
      · exact k2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
      · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)
    · have hkU := K_le_UJ hk
      have hmap : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
          ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
        intro l hl Z hZ
        obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
        exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
      refine ⟨fun l g => G (l.map fun Y => k⁻¹ * Y * k) (g * k),
        fun g hg => k1 _ (mul_mem_UJ hg hkU), fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
      · have hY' : k⁻¹ * Y * k ∈ lieSet ε := GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU hY
        have := k2 _ (hmap l hl) _ hY' (g * k) (mul_mem_UJ hg hkU)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show G _ (g * NormedSpace.exp (t • Y) * k) = G _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
        rw [← exp_conj_smul hkU Y t]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
      · obtain ⟨C, hC⟩ := k3 _ (hmap l hl)
        refine ⟨max C 0 * (1 + Formalism.REAL.hs k) ^ N, fun g hg => (hC _ (mul_mem_UJ hg hkU)).trans ?_⟩
        have h0 : 0 ≤ 1 + Formalism.REAL.hs (g * k) := by
          unfold Formalism.REAL.hs; positivity
        calc C * (1 + Formalism.REAL.hs (g * k)) ^ N ≤ max C 0 * (1 + Formalism.REAL.hs (g * k)) ^ N :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 N)
          _ ≤ max C 0 * ((1 + Formalism.REAL.hs g) * (1 + Formalism.REAL.hs k)) ^ N :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (one_add_hs_mul_le g k) N) (le_max_right _ _)
          _ = _ := by rw [mul_pow]; ring

theorem wordF_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  intro n ε N f F h1 h2 h3 u
  obtain ⟨G, k1, -, k3⟩ := wordF_fam h1 h2 h3 u
  obtain ⟨C, hC⟩ := k3 [] (by simp)
  exact ⟨C, fun g hg => k1 g hg ▸ hC g hg⟩

end GlobalTheory.TypeSum.CoefClos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnAvgRightTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
end

