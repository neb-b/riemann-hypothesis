module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoices
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv

@[expose] public section

noncomputable section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.MainNotions.S Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpBessel

variable {k r : ℕ}

section jacobian

open GlobalTheory.ThA.OrbSq GlobalTheory.CellRed P.Dx1.Rel

theorem scal_block : ∀ (bs : List (ℂ × ℕ)) (a b : ℕ), blockIdx bs a = blockIdx bs b →
    D.ptScal (sw bs) a = D.ptScal (sw bs) b
  | [], _, _ => fun _ => rfl
  | (t, s) :: bs, a, b => by
    intro h
    have e : sw ((t, s) :: bs) = (s, t) :: sw bs := rfl
    rw [e]
    simp only [blockIdx] at h
    simp only [D.ptScal]
    by_cases h1 : a < s <;> by_cases h2 : b < s <;> simp only [h1, h2, if_true, if_false] at h ⊢
    · omega
    · omega
    · exact scal_block bs _ _ (by omega)

theorem permOf_symm (p : Point ℂ (r + 1)) (a : Fin (r + 1)) : (permOf p).symm a = permOf p a := by
  rw [Equiv.symm_apply_eq, permOf_invol]

theorem zhat_monomial {z z' : Fin (2 * r + k + 1) → ℂ} {g : MatKR k r} {p : Point ℂ (r + 1)}
    (h : ZhatO k r z z' g = ptMat p) :
    ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ (∀ i a, Zhat k r z z' g i a = if i = permOf p a then d a else 0) ∧
      ∀ a b, (a, b) ∈ rootPat p → ‖d a‖ = ‖d b‖ := by
  have hp := isLocPt_sw p
  have hsz : D.ptSize (sw p.1) = r + 1 := hp.2
  refine ⟨fun a => (-1 : ℂ) ^ (r - a.val) * D.ptScal (sw p.1) a.val, fun a => ?_, fun i a => ?_, fun a b hab => ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (scal_ne _ hp.1 _ (by omega))
  · rw [zhat_of_zhatO h, ← ptMat_sw, ← permOf_symm]
    simp only [D.ptMatN]
    rw [(partner_spec _ a.val (by omega)).2.2 i.val]
    simp only [Fin.ext_iff, perm_symm_val]
    split_ifs <;> simp
  · simp only [rootPat, Finset.mem_filter] at hab
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, scal_block _ _ _ hab.2.2]

def flipRoot (p : Point ℂ (r + 1)) (q : rootPat p) : rootPat p :=
  ⟨(permOf p q.1.2, permOf p q.1.1), by
    have := (mem_rootPat p q.1.1 q.1.2).1 q.2
    rw [mem_rootPat]
    simp only [permOf_symm, permOf_invol] at this ⊢
    exact ⟨this.2, this.1⟩⟩

theorem flipRoot_invol (p : Point ℂ (r + 1)) : Function.Involutive (flipRoot p) := fun q =>
  Subtype.ext (Prod.ext (permOf_invol p _) (permOf_invol p _))

theorem rootCoords_eq (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) (x : Mt k r) (q : rootPat p) :
    rootCoords k r z p x q = Bm k r z (Matrix.of x) q.1.1 q.1.2 := by
  have hq : q.1.1.val < r := by
    have h1 := ((mem_rootPat p q.1.1 q.1.2).1 q.2).1
    have h2 := q.1.2.isLt
    rw [Fin.lt_def] at h1; omega
  simp only [rootCoords, flagMat, Bm, Matrix.of_apply, dif_pos hq]
  rfl

theorem measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z p) := by
  refine Continuous.measurable (continuous_pi fun q => ?_)
  unfold rootCoords flagMat
  split_ifs
  · exact (continuous_apply (eI k r _)).comp
      ((continuous_id (X := MatKR k r)).matrix_mulVec (continuous_const (y := fvec k r z q.1.2)))
  · exact continuous_const
  · exact continuous_const

theorem root_conj {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : MatKR k r}
    (hg : g ∈ UH (Hpk k r)) {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g = ptMat p) {μ : Measure (Mt k r)}
    (hμ : B.IsHaarOn (C6.Rset g⁻¹) μ) {c : ℝ≥0∞} (h : μ.map (rootCoords k r z' p) = c • volume) :
    (μ.map (conjM g)).map (rootCoords k r z p) = c • volume := by
  obtain ⟨d, hd, hm, hn⟩ := zhat_monomial hZ
  have hu := unit_det hg
  have hR := P.Dx2.OrbJ.closedR (k := k) (r := r) (Matrix.isUnit_nonsing_inv_det g hu)
  have hI := P.haar_measure_inversion k r _ _ hR hμ
  have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ hu
  let u : rootPat p → Circle := fun q => ⟨star (d (permOf p q.1.2) / d (permOf p q.1.1)), by
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm, norm_star, norm_div,
      hn _ _ (flipRoot p q).2, div_self (norm_ne_zero_iff.2 (hd _))]⟩
  have h1 : MeasurePreserving (fun (y : rootPat p → ℂ) q => rotation (u q) (y q)) volume volume :=
    volume_preserving_pi fun q => (rotation (u q)).measurePreserving
  have h2 := h1.comp (cjE_mp (flipRoot_invol p).toPerm)
  have mi : Measurable (GlobalTheory.SgInf.invM : Mt k r → Mt k r) := P.B2x2.invM_meas
  have hI' : μ.map GlobalTheory.SgInf.invM = μ := hI
  have mc := (continuous_conj g).measurable
  rw [← hI', Measure.map_map mc mi, Measure.map_map (measurable_rootCoords z p) (mc.comp mi), ← h2.map_eq,
    ← Measure.map_smul _ h2.measurable.aemeasurable, ← h, Measure.map_map h2.measurable (measurable_rootCoords z' p)]
  refine Measure.map_congr ?_
  filter_upwards [P.Dx2.OrbJ.ae_mem hμ] with x hx
  have hxi := (hR.inv_mem _ hx).2
  rw [hii] at hxi
  set ρ : MatKR k r := Matrix.of x with hρ
  set m := g * ρ⁻¹ * g⁻¹ with hmdef
  have hU : mᴴ * Hpk k r * m = Hpk k r := hxi.1
  have e1 : m * (g * ρ) = g := by
    rw [hmdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul_cancel_right _ _ (hR.unit _ hx)]
  have key : (Bm k r z m)ᴴ * Zhat k r z z' g = Zhat k r z z' g * Bm k r z' ρ := by
    rw [zhat_eq]
    calc (Bm k r z m)ᴴ * ((P.Dx1.Rel.Fm k r z)ᴴ * Hpk k r * g * P.Dx1.Rel.Fm k r z')
        = (P.Dx1.Rel.Fm k r z * Bm k r z m)ᴴ * Hpk k r * (m * (g * ρ)) * P.Dx1.Rel.Fm k r z' := by
          rw [conjTranspose_mul, e1]; simp only [Matrix.mul_assoc]
      _ = (P.Dx1.Rel.Fm k r z)ᴴ * (mᴴ * Hpk k r * m) * g * (ρ * P.Dx1.Rel.Fm k r z') := by
          rw [← expand z hz m hxi, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, expand z' hz' ρ hx.1]; simp only [Matrix.mul_assoc]
  funext q
  have e := congrFun (congrFun key q.1.2) (permOf p q.1.1)
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single q.1.1, Finset.sum_eq_single (permOf p q.1.2)] at e
  · simp only [hm, permOf_invol, if_true, conjTranspose_apply] at e
    simp only [Function.comp, rotation_apply, cjE_apply, rootCoords_eq]
    show Bm k r z m q.1.1 q.1.2 = star (d (permOf p q.1.2) / d (permOf p q.1.1)) *
      star (Bm k r z' ρ (permOf p q.1.2) (permOf p q.1.1))
    rw [← star_mul', div_mul_eq_mul_div, ← e, mul_div_cancel_right₀ _ (hd _), star_star]
  · intro j _ hj
    rw [hm, if_neg (fun e' => hj (by rw [e', permOf_invol])), zero_mul]
  · simp
  · intro j _ hj
    rw [hm, permOf_invol, if_neg hj, mul_zero]
  · simp

end jacobian


open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions GlobalTheory.CellRed in
theorem amp_at_root (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D lam A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    {γ p} (hp : RelPt D W.z W.z' γ p) {θ' : ℝ} (hθ' : 0 < θ') {νR} (hν : RMeas D W γ θ' νR) :
    ∃ (g : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ),
      CellData (toBessel D τ w w' θ W lam A hW hA hT hT') W.μG g (ENNReal.ofReal θ' • μR) ν₀ ν ∧
      ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧
      IsPtRepO (toBessel D τ w w' θ W lam A hW hA hT hT') p g ∧
      IsRootMeas (toBessel D τ w w' θ W lam A hW hA hT hT') p g μR ∧ ‖s‖ = 1 ∧ A.J νR γ = s • A.J ν₀ g := by
  obtain ⟨q, μ', hroot, hq⟩ := hν
  obtain ⟨hγ, hC, hGf⟩ := hp
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  have hz : inWb _ _ W.z := L.hz.1
  have hz' : inWb _ _ W.z' := L.hz'.1
  have hTz : 0 < Tz _ _ W.z := L.hz.2
  have hTz' : 0 < Tz _ _ W.z' := L.hz'.2
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hsc := GlobalTheory.Amp.RootQuot.scale_pos D
  have hka : 0 < D.host.ka := by
    have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
    have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
    have h1 := (div_pos_iff_of_pos_right (by positivity)).1 hsc
    have h2 := (div_pos_iff_of_pos_right (show 0 < gg D from mul_pos hg0 hg1)).1 h1
    linarith
  obtain rfl : p = q := by
    obtain ⟨n, hn, n', hn', g, hg, e, hZ⟩ := GlobalTheory.CellRep.cell_rep _ _ W.z W.z' γ p hz hz' hTz hTz' hγ hC
    have hG0 := hGf
    rw [e, gInv _ _ _ _ hz hz' _ (P.Dx2.Rad.N_sub_S W.z hn) _ (P.Dx2.Rad.N_sub_S W.z' hn')] at hG0
    obtain ⟨μ, h1, -, h3⟩ := GlobalTheory.Amp.RootQuot.exists_root_haar hk hz hz' hTz hTz' p hg hZ hG0
    refine (_root_.GlobalTheory.SnMass.RootUniq.rootMeas_unique D W.z W.z' γ p q _ μ' hz hz' hTz hTz' hγ hGf hka
      ⟨n, hn, n', hn', g, e, hZ, ENNReal.ofReal _ • μ, ?_, by rw [Measure.map_smul _ (measurable_rootCoords _ _).aemeasurable, h3], rfl⟩ hroot).1
    rw [Measure.smul_apply, h1.2.2.1, smul_zero]
  obtain ⟨n, hn, n', hn', g, rfl, hZ, μ₀, h0, h1, rfl⟩ := hroot
  have hg : g ∈ UH (Hpk D.R.k D.R.rS) := by
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact CellRed.mul_mem (CellRed.mul_mem (CellRed.inv_mem hn.1) hγ) (CellRed.inv_mem hn'.1)
  have hS := Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z hn
  have hS' := Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z' hn'
  rw [gInv _ _ _ _ hz hz' _ hS _ hS'] at hGf
  have hpos : 0 < Gf _ _ W.z W.z' g := lt_of_le_of_ne (gNonneg _ _ _ _ hz hz' hTz hTz' g hg) hGf.symm
  obtain ⟨⟨d, hd, hm⟩, d', hd', hm'⟩ := monomial_of_pt hg hZ
  have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (unit_det hg)
  have hc : 0 < (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card := pow_pos hsc _
  obtain ⟨hH₀, hI₀⟩ := root_haar (μ := μ₀) hk hz' hz hTz' hTz (CellRed.inv_mem hg) (by rw [gf_inv _ _ hg]; exact hpos)
    hd' hm' (by simpa using hc) ENNReal.ofReal_ne_top (by unfold C6.Rset; rw [hii]; exact h0) h1
  set μ : Measure (Mt D.R.k D.R.rS) := ENNReal.ofReal θ' • μ₀ with hμ
  have hH : B.IsHaarOn (C6.Rset g⁻¹) μ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.smul_apply, hH₀.conc, smul_zero]
    · intro a ha
      have hcont : Continuous (lmulM a : Mt D.R.k D.R.rS → Mt D.R.k D.R.rS) :=
        continuous_const.matrix_mul continuous_id
      rw [Measure.map_smul _ hcont.measurable.aemeasurable, hH₀.left a ha]
    · intro a ha
      have hcont : Continuous (B.rmulF a : Mt D.R.k D.R.rS → Mt D.R.k D.R.rS) :=
        continuous_id.matrix_mul continuous_const
      rw [Measure.map_smul _ hcont.measurable.aemeasurable, hH₀.right a ha]
    · intro K hK
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hH₀.finite_compact K hK)
    · intro h0
      apply hH₀.ne_zero
      have h1 := Measure.measure_univ_eq_zero.2 h0
      rw [Measure.smul_apply, smul_eq_mul] at h1
      exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hθ').ne')
  obtain ⟨ν, hν⟩ := exists_orbQuot L ENNReal.ofReal_ne_top hg hH (by positivity)
    (hI₀.smul_measure ENNReal.ofReal_ne_top)
  have hR := haar_conj hg hH
  have hq₀ : IsQuotMeas W.μG μ (νR.map (lmulEquiv hn'.1)) := by
    have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM n' ∘ conjM n'⁻¹ : Mt D.R.k D.R.rS → _) = id := by
      funext x
      have := conj_inv_conj (CellRed.inv_mem hn'.1) x
      rwa [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)] at this
    have := quot_map hn'.1 hG hq
    rwa [e1, Measure.map_smul _ (continuous_conj _).measurable.aemeasurable, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2,
      Measure.map_id] at this
  have hconc : νR.map (lmulEquiv hn'.1) {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 :=
    CutQuot.null_of_stable (R := {x | Matrix.of x ∈ C6.Rset g⁻¹})
      (T := fun s x => fun i j => (Matrix.of s * Matrix.of x) i j) hH.conc hH.ne_zero hq₀
      (CutQuot.measurable_G _ _).compl
      (fun s hs x hx h => hx ((CutQuot.mul_mem_iff hs.1.1 (Matrix.of x)).1 h)) hG.2.2.1
  have hmap : ENNReal.ofReal θ' • μ₀.map (conjM g) = μ.map (conjM g) := (Measure.map_smul _ (continuous_conj _).measurable.aemeasurable).symm
  refine ⟨g, μ₀.map (conjM g), νR.map (lmulEquiv hn'.1), ν,
    (psiS D W.z n / psiS D W.z 1) * star (psiS D W.z' n'⁻¹ / psiS D W.z' 1), ?_, hconc, ⟨hg, hZ⟩,
    ⟨(haar_conj hg hH₀).conc, ?_⟩, ?_, ?_⟩
  · rw [hmap]
    refine ⟨hg, hpos, ⟨_, d, hd, hm⟩, relevant hz hz' hg hZ _,
      ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hR, hR.ne_zero, hR.conc, hR.left⟩, hν, ?_⟩
    have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (g⁻¹ * Matrix.of x * g) i j) = conjM g⁻¹ := by
      funext x
      unfold conjM
      rw [hii]
    have e2 : (conjM g⁻¹ ∘ conjM g : Mt D.R.k D.R.rS → _) = id := funext (conj_inv_conj hg)
    rw [e1, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2, Measure.map_id]
    exact hq₀
  · refine (root_conj hz hz' hg hZ hH₀ h1).trans ?_
    have e : ‖L.c‖ = 2 * D.host.ka / gg D := by
      refine (Complex.norm_real _).trans (Real.norm_of_nonneg ?_)
      exact ((div_pos_iff_of_pos_right (by positivity)).1 hsc).le
    rw [e]
  · have e : ∀ z x, ‖psiS D z x‖ = 1 := fun z x => by
      unfold psiS psi
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_star, norm_div, norm_div, e, e, e, e]
    norm_num
  · obtain ⟨-, hds, hB, hB', hv, -⟩ := hA
    have hae : ∀ᵐ x ∂νR, Matrix.of (lmulEquiv hn'.1 x) ∈ UH (Hpk D.R.k D.R.rS) :=
      (MeasurableEquiv.measurableEmbedding _).ae_map_iff.1 hconc
    unfold LocS.J ampJ
    rw [integral_map_equiv, smul_comm]
    congr 1
    refine Eq.trans (integral_congr_ae ?_) (integral_smul _ _)
    filter_upwards [hae] with x hx
    set y : MatKR D.R.k D.R.rS := Matrix.of (lmulEquiv hn'.1 x) with hy
    have ey : y = n' * Matrix.of x := rfl
    have ex : Matrix.of x = n'⁻¹ * y := by rw [ey, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn'.1)]
    have e1 : A.Φ (n * g * n' * Matrix.of x) = (psiS D W.z n / psiS D W.z 1) • A.Φ (g * y) := by
      rw [show n * g * n' * Matrix.of x = n * (g * y) by rw [ey]; simp only [Matrix.mul_assoc]]
      exact bessel_unip hds hB (psi_ne _ _ _) hv hn (CellRed.mul_mem hg hx)
    have e2 : A.Φ' (Matrix.of x) = (psiS D W.z' n'⁻¹ / psiS D W.z' 1) • A.Φ' y := by
      rw [ex]
      exact bessel_unip hds hB' (psi_ne _ _ _) hv ((nSubgroup _ _).2.2 _ hn') hx
    rw [e1, e2]
    ext u
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
      inner_smul_left, smul_smul, Complex.star_def]
    congr 1
    ring

theorem hs_nonneg {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [GlobalTheory.AmpNorm.hsNormSq_eq]; positivity

section coefficient

open BranchingSupport GlobalTheory.CellAmp Formalism.FourierDecayAlt.P

theorem isKFinCoefH_coefF (L : LocBessel k r) {v v' : L.Hs} (hv : IsKFinHpk (k := k) (r := r) L.σ v)
    (hv' : IsKFinHpk (k := k) (r := r) L.σ v') (ξ : L.Wp) (ξ' : L.Wq) : IsKFinCoefH L.σ (coefF L v v' ξ ξ') := by
  refine ⟨(innerSL ℂ v).smulRight ξ, (innerSL ℂ ξ').smulRight v', fun x => ?_, fun x => ?_, fun g => ?_⟩
  · obtain ⟨S, h1, h2, h3⟩ := hv'
    exact ⟨S, h1, S.smul_mem _ h2, h3⟩
  · obtain ⟨S, h1, h2, h3⟩ := hv
    have e : ContinuousLinearMap.adjoint ((innerSL ℂ v).smulRight ξ) x = ⟪ξ, x⟫_ℂ • v := by
      refine ext_inner_left ℂ fun y => ?_
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp [inner_smul_left, inner_smul_right, mul_comm]
    exact ⟨S, h1, e ▸ S.smul_mem _ h2, h3⟩
  · ext x
    simp [coefF, inner_smul_right, smul_smul]

theorem ae_cellData (hk : 1 ≤ k) (L : LocBessel k r) (μG : Measure (Mt k r))
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hsec : IsSection k r L.z L.z' μsec) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r L.z) (Tz k r L.z') q = 0 ∨
      CellData L μG (bigCell k r q.1 (μsec q.2)) (Measure.dirac (fun i j => (1 : MatKR k r) i j)) μG (pairMeas L) := by
  obtain ⟨Bs, hz, hz'⟩ := GlobalTheory.CellRed.exists_setting hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  let S : B.RealPlaceData k r ℂ ℂ := { Bs with μsec := μsec, sec := by rw [hz, hz']; exact hsec }
  filter_upwards [B7.ae_mem_good_set_or_weight_zero S] with q hq
  rcases hq with hq | hq
  swap
  · left
    rw [← hz, ← hz']
    exact hq
  right
  have hOm := BigCellHermitian.gqDom S hq
  refine Model.cellData_open L μG _ hOm.1 (Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hOm.1))
    (hz ▸ hz' ▸ hOm.2.2) ?_ (GlobalTheory.AmpNorm.rStab_bigCell _ _ hq.1 hOm.1)
  rw [← hz, ← hz']
  have hZ := bigCellZhat k r S.z S.z' q.1 (S.μsec q.2) S.z_mem S.z'_mem
  rw [BigCellHermitian.herm_bigCell _ _ S.z_mem S.z'_mem, (S.sec.2 q.2 hq.2).2] at hZ
  refine ⟨1, fun a => if h : a.val < r then q.1 ⟨a.val, h⟩ else q.2, fun a => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hq.1 _
    · intro h0
      have := hq.2
      rw [h0, map_zero] at this
      exact absurd (mul_pos S.T_pos S.T'_pos) this.not_gt
  · refine hZ.trans ?_
    ext i j
    rw [Matrix.diagonal_apply]
    show _ = if i = j then _ else _
    by_cases h : i = j
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h]

theorem isOrbQuot_smul {L : LocBessel k r} {g : MatKR k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} {t : ℝ}
    (h : IsOrbQuot L g (ENNReal.ofReal t • μR) ν) : IsOrbQuot L g μR (ENNReal.ofReal t • ν) := by
  intro f hf
  rw [h f hf, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun x => lintegral_smul_measure _ _

end coefficient



end GlobalTheory.AmpBessel

end
