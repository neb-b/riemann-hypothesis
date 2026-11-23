module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermBvecEI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.AdjugateLastEntrySum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.FixOfPos
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMulVecFactorization
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S5

variable {k r : ℕ}

lemma W_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v → herm (Hpk k r) v z = 0 →
      ‖v‖ ^ 2 ≤ C * (herm (Hpk k r) v v).re := by
  have hc1 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) v z := by
    unfold herm; fun_prop
  have hc2 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) v v).re := by
    unfold herm; fun_prop
  have hWb : IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} := by
    simp only [inWb, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
  set K : Set (Fin (2 * r + k + 1) → ℂ) :=
    Metric.sphere 0 1 ∩ ({v | inWb k r v} ∩ {v | herm (Hpk k r) v z = 0}) with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (hWb.inter (isClosed_eq hc1 continuous_const))
  have hpos : ∀ v ∈ K, 0 < (herm (Hpk k r) v v).re := by
    rintro v ⟨hv1, hv2, hv3⟩
    refine posV hz hv2 hv3 ?_
    rintro rfl
    simp at hv1
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun v => ((herm (Hpk k r) v v).re)⁻¹)
    (hc2.continuousOn.inv₀ fun v hv => (hpos v hv).ne')
  refine ⟨max C 0, le_max_right _ _, fun v hv hvz => ?_⟩
  by_cases h0 : v = 0
  · subst h0; simp [herm]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  set c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) with hc
  have hwK : c • v ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    · intro i hi; simp [hv i hi]
    · show herm (Hpk k r) (c • v) z = 0
      rw [hm_smul_l, hvz, mul_zero]
  have hf : (herm (Hpk k r) (c • v) (c • v)).re = ‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re := by
    rw [hm_smul_l, hm_smul_r, hc, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hb := hC (c • v) hwK
  have hp := hpos _ hwK
  rw [hf] at hp hb
  have ht : 0 < (herm (Hpk k r) v v).re := by
    have : 0 < ‖v‖⁻¹ ^ 2 := by positivity
    exact pos_of_mul_pos_right hp this.le
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)] at hb
  have hb2 : 1 ≤ C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) := by
    rw [inv_le_iff_one_le_mul₀ hp] at hb; linarith
  have e : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) = (herm (Hpk k r) v v).re := by
    field_simp
  calc ‖v‖ ^ 2 = ‖v‖ ^ 2 * 1 := by ring
    _ ≤ ‖v‖ ^ 2 * (C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = C * (‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) := by ring
    _ = C * (herm (Hpk k r) v v).re := by rw [e]
    _ ≤ max C 0 * (herm (Hpk k r) v v).re := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le

private theorem herm_Hpk_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (c • x) y = c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (c • x)) = c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_Hpk_smul_right_eq_star_mul (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (c • y) = star c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star (c • y) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x) = star c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [star_smul, smul_dotProduct, smul_eq_mul]

lemma unitH_facts {z v : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hv : v ∈ Wsp k r z) :
    unitH k r v ∈ Wsp k r z ∧ (herm (Hpk k r) (unitH k r v) (unitH k r v)).re ≤ 1 := by
  obtain ⟨hw, ho⟩ := hv
  set s : ℝ := (Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ with hs
  have hU : unitH k r v = (s : ℂ) • v := rfl
  rw [hU]
  refine ⟨⟨fun i hi => by rw [Pi.smul_apply, hw i hi, smul_zero], ?_⟩, ?_⟩
  · show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) z = 0
    rw [herm_Hpk_smul_left, ho, mul_zero]
  · show (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) ((s : ℂ) • v)).re ≤ 1
    rw [herm_Hpk_smul_left, herm_Hpk_smul_right_eq_star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    by_cases hpos : 0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re
    · exact le_of_eq (by rw [hs, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne'])
    · rw [hs, Real.sqrt_eq_zero'.2 (not_lt.1 hpos)]
      simp

lemma lift_X' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r)
    {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z') (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have e : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = 0 := by
    have h1 : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      unfold xcofL; rw [hm_sum_r]; simp only [star_star]
    rw [h1, ← ginv_cancel hy (xcofL k r z z' y), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_prW_r huW]
    exact huo
  have hlast : gam k r z z' y u (Fin.last r) = 0 := by
    simp only [gam, wv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [e, mul_zero]
  have hS : Lm k r z z' y *ᵥ u - u = ∑ c, gam k r z z' y u c • fvec k r z' c := by rw [Lm_mulVec]; abel
  rw [hS]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · rw [hc, hlast, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

lemma phi_iso' {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {y : B.Mat k r} (hy : y ∈ B.GV k r)
    (hd : (Zhat k r z z' y).det ≠ 0) {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z')
    (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u) = herm (Hpk k r) u u := by
  rw [Phi_mulVec]
  have hx := sub_prW_X hz (lift_orth hd u)
  have hP := prW_mem hz (y *ᵥ (Lm k r z z' y *ᵥ u))
  have hL := lift_X' hy huW huo
  rw [← herm_add_X hP.1 hP.1 hx hx, aps, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_add_X huW.1 huW.1 hL hL, aps]

lemma Pp_facts {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') (g : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v ∈ Wsp k r z' ∧ herm (Hpk k r) (PpG z z' g *ᵥ v) (omW' k r z z' g) = 0 ∧
      (herm (Hpk k r) (PpG z z' g *ᵥ v) (PpG z z' g *ᵥ v)).re ≤
        (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v)).re := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hPe : PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
    unfold PpG
    rw [sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec]
  set p := PI.UnitaryGroupMassFormula.GsFr.prW k r z' v with hp
  set om := omW' k r z z' g with hom
  have hpW : p ∈ Wsp k r z' := prW_mem hz' v
  have homW : om ∈ Wsp k r z' := prW_mem hz' _
  have hνW : nuG' z z' g ∈ Wsp k r z' := Wsp_smul _ homW
  rw [hPe]
  refine ⟨Wsp_sub hpW (Wsp_smul _ hνW), ?_⟩
  by_cases h0 : om = 0
  · have hν0 : nuG' z z' g = 0 := by
      show unitH k r om = 0
      rw [h0]; simp [unitH]
    rw [hν0, h0]
    simp [herm]
  have ht := posV hz' homW.1 homW.2 h0
  have hνν : herm (Hpk k r) (nuG' z z' g) (nuG' z z' g) = 1 := nz_unit ht
  set c := herm (Hpk k r) p (nuG' z z' g) with hcdef
  set u := p - c • nuG' z z' g with hu
  have huν : herm (Hpk k r) u (nuG' z z' g) = 0 := by
    rw [hu, hm_sub_l, hm_smul_l, hνν, mul_one, sub_self]
  have hνu : herm (Hpk k r) (nuG' z z' g) u = 0 := by
    rw [hm_symm _ hH, huν, star_zero]
  refine ⟨(nz_orth ht u).1 huν, ?_⟩
  have hpu : p = u + c • nuG' z z' g := by rw [hu, sub_add_cancel]
  have e : herm (Hpk k r) p p = herm (Hpk k r) u u + c * star c := by
    conv_lhs => rw [hpu]
    rw [hm_add_l, hm_add_r, hm_add_r, hm_smul_l, hm_smul_l, hm_smul_r, hm_smul_r, huν, hνu, hνν]
    ring
  rw [e, Complex.add_re]
  have : 0 ≤ (c * star c).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
  linarith

lemma embedding_mul_vec_factorization (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

lemma sq_bound {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C) : x ≤ C + 1 := by
  nlinarith [sq_nonneg (x - 1)]

end S5

open S5 in
theorem geometry_boundedness_at_zero : GeomBd0 := by
  intro k r z z' hk hz hz'
  obtain ⟨C1, hC1, hW⟩ := W_bound hz
  obtain ⟨C2, hC2, hW'⟩ := W_bound hz'
  set M := ∑ j : Fin (2 * r + k + 1),
    |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|
    with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hν : ∀ g, ‖nuG z z' g‖ ≤ C1 + 1 := by
    intro g
    have hu := unitH_facts hz (prW_mem hz (xcof k r z z' g))
    have h1 := hW _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC1 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC1
    simpa [nuG, omW] using this
  have hν' : ∀ g, ‖nuG' z z' g‖ ≤ C2 + 1 := by
    intro g
    have hu := unitH_facts hz' (prW_mem hz' (g⁻¹ *ᵥ xcofL k r z z' g))
    have h1 := hW' _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC2 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC2
    simpa [nuG', omW'] using this
  refine ⟨(C1 + 1) + (C2 + 1) + (C1 * M + 1), fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have := hν g; have := mul_nonneg hC1 hM0; linarith
  · have := hν' g; have := mul_nonneg hC1 hM0; linarith
  · have hCM := mul_nonneg hC1 hM0
    have hC : 0 ≤ (C1 + 1) + (C2 + 1) + (C1 * M + 1) := by linarith
    rw [Matrix.norm_le_iff hC]
    intro i j
    have hd := det_ne_of_G hz hz' hg.2
    obtain ⟨huW, huo, hle⟩ := Pp_facts (z := z) hz' g (Pi.single j 1)
    have hiso := phi_iso' hz hg.1 hd huW huo
    set q := Phi k r z z' g *ᵥ (PpG z z' g *ᵥ Pi.single j 1) with hq
    have hqW : q ∈ Wsp k r z := by rw [hq, Phi_mulVec]; exact prW_mem hz _
    have h1 := hW q hqW.1 hqW.2
    rw [hiso] at h1
    have hpM : (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
        (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re ≤ M :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin (2 * r + k + 1) =>
        |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
          (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : ‖q‖ ^ 2 ≤ C1 * M := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpM) hC1)
    have h3 := sq_bound (norm_nonneg q) hCM h2
    have e : ioG z z' g i j = q i := by
      rw [hq, ← embedding_mul_vec_factorization]
      simp
    rw [e]
    have := norm_le_pi_norm q i
    have := hν g
    have := hν' g
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceFirstVector
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S2

variable {k r : ℕ}

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

lemma omW_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : B.Mat k r) :
    omW k r z z' (n * g * n') = omW k r z z' g := by
  show prW k r z (xcof k r z z' (n * g * n')) = prW k r z (xcof k r z z' g)
  rw [xcof_N hz hz' hn hn' g]
  exact prW_N hn (fun a => xcof_esI z z' g a)

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' (n * g * n') = omW' k r z z' g := by
  have hh : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hleft : (Hpk k r * nᴴ * Hpk k r) * n = 1 := by
    calc (Hpk k r * nᴴ * Hpk k r) * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, WeylGroupFacts.hpk_sq]
  have hnn : n⁻¹ * n = 1 := by
    rw [Matrix.inv_eq_left_inv hleft]
    exact hleft
  show prW k r z' ((n * g * n')⁻¹ *ᵥ xcofL k r z z' (n * g * n')) = prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)
  rw [xcofL_N hz hz' hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, hnn, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact prW_N (WeylGroupFacts.mem_n_inv hn') (fun a => ginv_xcofL_esI z z' hg a)

end S2

open S2 in
theorem geometry_equivariance_first_vector : GeomEqvNu := by
  intro k r z z' _ hz hz' h hh n hn h' hh' n' hn' g hg
  have hy : h⁻¹ * n⁻¹ * g * n' * h' = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [Matrix.mul_assoc]
  have hhi := WeylGroupFacts.uw_inv hh
  have hhi' := WeylGroupFacts.uw_inv hh'
  have hni := WeylGroupFacts.mem_n_inv hn
  have hu : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (RankOneEmbeddings.In.uw_unit hh)
  have hu' : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (RankOneEmbeddings.In.uw_unit hh')
  constructor
  · show unitH k r (omW k r z z' g) = h *ᵥ unitH k r (omW k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW_UW hz hhi hh', omW_N hz hz' hni hn', unitH_UH hhi.1, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec]
  · show unitH k r (omW' k r z z' g) = h' *ᵥ unitH k r (omW' k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW'_UW hz hz' hhi hh', omW'_N hz hz' hni hn' hg.1, unitH_UH hhi'.1, Matrix.mulVec_mulVec,
      hu', Matrix.one_mulVec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormCDZPsiCLe
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv_ae (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖)
    (fun n => ((hum n).mul hI.1).add ((hvm n).mul hJ.1)) (hI.norm.add (hJ.norm.const_mul M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
  · calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · filter_upwards [hl] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn.1, hn.2]
    ring

end Lim

section Main

def psiC (n : ℕ) (c : ℂ) : ℂ := ((psiL n c : ℝ) : ℂ)

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := Complex.ofRealCLM.contDiff.comp (psiL_contDiff n)

theorem fderiv_psiC (n : ℕ) (c : ℂ) : fderiv ℝ (psiC n) c = Complex.ofRealCLM.comp (fderiv ℝ (psiL n) c) := by
  have hd : DifferentiableAt ℝ (psiL n) c := (psiL_contDiffAt n c).differentiableAt (by simp)
  exact (Complex.ofRealCLM.hasFDerivAt.comp c hd.hasFDerivAt).fderiv

theorem norm_c_dZ_psiC_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) :
    ‖c * NF.dZ (psiC n) c‖ ≤ C := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · rw [dZ_eq, fderiv_psiC, norm_mul]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hD := norm_mul_fderiv_psiL_le hC n c hc
    have ha : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm 1
    have hb : ‖((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm Complex.I
    have hz : ‖(1 / 2 : ℂ) * (((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ))‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [norm_mul]
      have h3 : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤
          2 * ‖fderiv ℝ (psiL n) c‖ := by
        calc _ ≤ ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ ‖fderiv ℝ (psiL n) c‖ + ‖fderiv ℝ (psiL n) c‖ := by
              rw [norm_mul, Complex.norm_I, one_mul]
              exact add_le_add ha hb
          _ = 2 * ‖fderiv ℝ (psiL n) c‖ := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h2]
      linarith
    calc ‖c‖ * _ ≤ ‖c‖ * ‖fderiv ℝ (psiL n) c‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ ≤ C := hD

theorem psiC_eventually (c : ℂ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, psiC n c = 1 ∧ c * NF.dZ (psiC n) c = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |Real.log ‖c‖|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlt : |Real.log ‖c‖| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev := psiL_one_near n c hc hlt
  refine ⟨?_, ?_⟩
  · simp [psiC, hev.eq_of_nhds]
  · rw [dZ_eq, fderiv_psiC, hev.fderiv_eq]
    simp

end Main

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def ptG (h' : C.LPt) (m : ℕ) : (ℂ × ℂ) ⊕ ℂ → C.LPt
  | Sum.inl q => h' ++ [(m + 1, q.1), (1, q.2)]
  | Sum.inr z => h' ++ [(m + 2, z)]

def yG {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : G.Mat (m + 2) → V) :
    (ℂ × ℂ) ⊕ ℂ → V
  | Sum.inl q => ((kapB m : ℝ) : ℂ) • G.OmBlock β (m + 1) Φ q.1 q.2
  | Sum.inr z => ((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong β (m + 1) Φ z

def okG (m : ℕ) (Kc : Set ℂ) : (ℂ × ℂ) ⊕ ℂ → Prop
  | Sum.inl q => q.1 ≠ 0 ∧ q.2 * q.1 ^ (m + 1) ∈ Kc
  | Sum.inr z => ∃ D ∈ Kc, z ^ (m + 2) = (-1) ^ (m + 3) * D

theorem ptSize_ptG (h' : C.LPt) (m : ℕ) (q : (ℂ × ℂ) ⊕ ℂ) : D.ptSize (ptG h' m q) = D.ptSize h' + (m + 2) := by
  cases q <;> simp [ptG, D.ptSize, List.map_append, List.sum_append] <;> omega

def GermPlace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (ε : ℝ) (h' : C.LPt) (m i : ℕ) (hi : i ≤ P0.r) (hsz : D.ptSize h' + (m + 2) = i),
    B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) → C6.IsCut0 χ →
    0 < ε → 2 ≤ P0.k → D.IsLocPt h' (D.ptSize h') →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : CompleteSpace V)
      (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V) (Cp Cst : ℝ),
      0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
      (∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
        D.formLev T sg ⟨i, by omega⟩ w
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
        Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)) ∧
      ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
        ‖U.uD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D - U.aD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D‖ ≤
          Cst * ‖t‖

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

