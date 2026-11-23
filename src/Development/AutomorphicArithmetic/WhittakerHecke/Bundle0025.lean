module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0022
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0018
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0021
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0023
public import Development.AutomorphicArithmetic.WhittakerHecke.HasSumWhittakerDiagTorusRatEqUnipotentConstantTe

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ConjLieElementEmbedRotationEqTrigMatrix
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem kInf_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ)
    (i j : Fin 2) (w : InfinitePlace E) :
    (kInf (em E (rot t))).val i j w = (((Nz.X t).val i j (Fo.pl ℚ w.embedding) : ℝ) : ℂ) := by
  have h1 := (UpperTheory.ConvolutionTheory.R2.Fo.coordMk ℚ E D).1 w.embedding ((rot t).val i j) 0
  rw [FieldIso.coord_embedding] at h1
  have h2 : D.mkE ((rot t).val i j) 0 = AdeleBaseChange.adeleMap ℚ E ((rot t).val i j) := by
    simp [Dat.mkE]
  have h3 : TR.pInf ℚ ((rot t).val i j) = (Nz.X t).val i j := by
    have h := congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL (Nz.X t))
    rw [← Nz.rot_eq] at h
    exact h
  change pInf E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) w = _
  rw [← h2, h1]
  simp [Fo.cw, h3]

private theorem kInf_rot {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ) :
    (kInf (em E (rot t))).val =
      !![fun _ => (Real.cos t : ℂ), fun _ => -(Real.sin t : ℂ); fun _ => (Real.sin t : ℂ), fun _ => (Real.cos t : ℂ)] := by
  ext i j w
  rw [kInf_val D]
  fin_cases i <;> fin_cases j <;> simp [Nz.X]

theorem UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ), XB D (em E (rot t)) = !![(Real.cos t * Real.sin t) • thInf D, (Real.cos t ^ 2) • thInf D; -((Real.sin t ^ 2) • thInf D), -((Real.cos t * Real.sin t) • thInf D)] := by
  intro E _ _ _ D t
  have hinv : (kInf (em E (rot t)))⁻¹ = kInf (em E (rot (-t))) := by
    rw [Nz.rot_neg, map_inv]
    simp [kInf, map_inv]
  rw [XB, hinv, kInf_rot D, kInf_rot D]
  ext i j w
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IdeleCoveringLintegralEqConstMulHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {G Q : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group Q] [Countable Q] (μ υ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure υ] (c : ℝ → G → Q → G) (S : Set G) (hc : ∀ α, Continuous fun p : ℝ × G => c p.1 p.2 α) (hS : υ Sᶜ = 0)
    (hinv : ∀ w ∈ S, υ.map (fun x => w * x) = υ) (hcov : ∀ x, ∃ t u α, u ∈ S ∧ x = c t u α)
    (hmul : ∀ τ w β t u α, c τ w β * c t u α = c (τ + t) (w * u) (β * α))
    (hfin : ∀ K, IsCompact K → ∃ (R : ℝ) (F : Finset Q), ∀ t, ∀ u ∈ S, ∀ α, c t u α ∈ K → t ∈ Set.Icc (-R) R ∧ α ∈ F) :
    ∃ k : ℝ≥0, k ≠ 0 ∧ ∀ h : G → ℝ≥0∞, Measurable h → ∫⁻ t : ℝ, ∫⁻ u, ∑' α : Q, h (c t u α) ∂υ = k * ∫⁻ y, h y ∂μ := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ℝ × G), ν = volume.prod υ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Measure G, m = Measure.sum fun α : Q => ν.map fun p => c p.1 p.2 α := ⟨_, rfl⟩
  have key : ∀ h : G → ℝ≥0∞, Measurable h → ∫⁻ y, h y ∂m = ∫⁻ t : ℝ, ∫⁻ u, ∑' α : Q, h (c t u α) ∂υ := fun h hh => by
    have hα : ∀ α, Measurable fun p : ℝ × G => h (c p.1 p.2 α) := fun α => hh.comp (hc α).measurable
    rw [hm, lintegral_sum_measure, tsum_congr fun α => lintegral_map hh (hc α).measurable,
      ← lintegral_tsum fun α => (hα α).aemeasurable, hν, lintegral_prod _ (Measurable.tsum hα).aemeasurable]
  have inv : m.IsMulLeftInvariant := ⟨fun x => by
    obtain ⟨τ, w, β, hw, rfl⟩ := hcov x
    have hp : MeasurePreserving (fun p : ℝ × G => (τ + p.1, w * p.2)) ν ν := by
      rw [hν]
      exact (measurePreserving_add_left volume τ).prod (g := fun x => w * x) ⟨measurable_const_mul w, hinv w hw⟩
    have e : ∀ α, ((ν.map fun p => c p.1 p.2 α).map (c τ w β * ·)) = ν.map fun p => c p.1 p.2 (β * α) := fun α => by
      refine Eq.trans ?_ (congrArg (Measure.map fun p : ℝ × G => c p.1 p.2 (β * α)) hp.map_eq)
      rw [Measure.map_map (measurable_const_mul _) (hc α).measurable, Measure.map_map (hc (β * α)).measurable hp.measurable]
      exact congrArg (fun f => Measure.map f ν) (funext fun p => hmul τ w β p.1 p.2 α)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, Measure.map_sum (measurable_const_mul _).aemeasurable]
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs, tsum_congr fun α => congrArg (fun n : Measure G => n s) (e α)]
    exact (Equiv.mulLeft β).tsum_eq fun α : Q => (ν.map fun p => c p.1 p.2 α) s⟩
  have fin : IsFiniteMeasureOnCompacts m := ⟨fun K hK => by
    obtain ⟨R, F, hF⟩ := hfin K hK
    have hb : ∀ α, (ν.map fun p => c p.1 p.2 α) K ≤ if α ∈ F then volume (Set.Icc (-R) R) else 0 := fun α => by
      rw [Measure.map_apply (hc α).measurable hK.measurableSet]
      have hn : ν (Set.univ ×ˢ Sᶜ) = 0 := by rw [hν, Measure.prod_prod, hS, mul_zero]
      split_ifs with h
      · refine (measure_mono (t := Set.Icc (-R) R ×ˢ Set.univ ∪ Set.univ ×ˢ Sᶜ) fun p hp => ?_).trans ((measure_union_le _ _).trans ?_)
        · by_cases hu : p.2 ∈ S
          · exact Or.inl ⟨(hF _ _ hu α hp).1, trivial⟩
          · exact Or.inr ⟨trivial, hu⟩
        · rw [hn, add_zero, hν, Measure.prod_prod, measure_univ, mul_one]
      · exact (measure_mono (t := Set.univ ×ˢ Sᶜ) fun p hp => ⟨trivial, fun hu => h (hF _ _ hu α hp).2⟩).trans hn.le
    rw [hm, Measure.sum_apply _ hK.measurableSet]
    refine (ENNReal.tsum_le_tsum hb).trans_lt ?_
    rw [tsum_eq_sum (s := F) fun α h => if_neg h]
    exact ENNReal.sum_lt_top.2 fun α h => by rw [if_pos h]; exact measure_Icc_lt_top⟩
  have e := Measure.isMulLeftInvariant_eq_smul m μ
  refine ⟨m.haarScalarFactor μ, fun h0 => ?_, fun h hh => ?_⟩
  · rw [h0, zero_smul] at e
    have h1 := key (fun _ => 1) measurable_const
    rw [e, lintegral_zero_measure] at h1
    have h2 : (∑' _ : Q, (1 : ℝ≥0∞)) ≠ 0 := fun h => one_ne_zero (ENNReal.tsum_eq_zero.1 h 1)
    rw [lintegral_const, lintegral_const, measure_univ, mul_one, Real.volume_univ] at h1
    exact mul_ne_zero h2 ENNReal.top_ne_zero h1.symm
  · rw [← key h hh]
    exact (congrArg (fun n : Measure G => ∫⁻ y, h y ∂n) e).trans (by rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul])

private theorem cov_cont (α : ℚˣ) : Continuous fun p : ℝ × IdeleGroup ℚ => Un.cov p.1 p.2 α := by
  have hcont := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
  unfold Un.cov
  exact (continuous_const.mul ((hcont.comp continuous_fst).mul (hcont.comp continuous_fst))).mul continuous_snd

private theorem fin_rat {C : Set (IdeleGroup ℚ)} (hC : IsCompact C) : {α : ℚˣ | IdeleGroup.diagonal ℚ α ∈ C}.Finite := by
  have h1 : (C ∩ (IdeleGroup.diagonal ℚ).range).Finite :=
    (hC.inter_right (Subgroup.isClosed_of_discrete (U := (IdeleGroup.diagonal ℚ).range))).finite
      (isDiscrete_iff_discreteTopology.2 (DiscreteTopology.of_subset (s := ((IdeleGroup.diagonal ℚ).range : Set _)) (inferInstanceAs (DiscreteTopology (IdeleGroup.diagonal ℚ).range))
        Set.inter_subset_right))
  exact (h1.preimage (IdeleGroup.diagonal_injective ℚ).injOn).subset fun α hα => ⟨hα, α, rfl⟩

private theorem cov_fin (K : Set (IdeleGroup ℚ)) (hK : IsCompact K) :
    ∃ (R : ℝ) (F : Finset ℚˣ), ∀ t, ∀ u ∈ UU, ∀ α, Un.cov t u α ∈ K → t ∈ Set.Icc (-R) R ∧ α ∈ F := by
  obtain ⟨-, hab, -, habU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  have hl : Continuous fun y : (A ℚ)ˣ => Real.log (ab y) := M.continuous_ab.log fun y => (M.ab_pos y).ne'
  obtain ⟨R, hR⟩ := (hK.image hl).isBounded.exists_norm_le
  have ht : ∀ t, ∀ u ∈ UU, ∀ α, Un.cov t u α ∈ K → t ∈ Set.Icc (-R) R := fun t u hu α h => by
    have h1 := hR _ ⟨_, h, rfl⟩
    have h2 : ab (Un.cov t u α) = Real.exp (t + t) := by
      unfold Un.cov
      rw [M.ab_mul, M.ab_mul, M.ab_mul, M.ab_diag, habU u hu, hab _ (Real.exp_ne_zero _), abs_of_pos (Real.exp_pos _), one_mul,
        mul_one, Real.exp_add]
    dsimp only at h1
    rw [h2, Real.log_exp, Real.norm_eq_abs, abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hq : Continuous fun q : IdeleGroup ℚ × ℝ × IdeleGroup ℚ => q.1 * (Un.cov q.2.1 q.2.2 1)⁻¹ :=
    continuous_fst.mul ((cov_cont 1).comp continuous_snd).inv
  have hfin := fin_rat ((hK.prod ((isCompact_Icc (a := -R) (b := R)).prod UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.1)).image hq)
  refine ⟨R, hfin.toFinset, fun t u hu α h => ⟨ht t u hu α h, hfin.mem_toFinset.2 ⟨(_, t, u), ⟨h, ht t u hu α h, hu⟩, ?_⟩⟩⟩
  simp only [Un.cov, map_one, one_mul, mul_assoc, mul_inv_cancel, mul_one]

theorem UpperTheory.ideleCovering_lintegral_eq_const_mul_haar :
    ∀ U : UMeas, ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
        ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ) := by
  intro U
  haveI := U.prob
  haveI : Countable ℚˣ := Units.val_injective.countable
  refine gen (ideleMeasure ℚ) U.υ Un.cov UU cov_cont U.supp U.inv UpperTheory.exists_rat_idele_eq_exp_unit_principal (fun τ w β t u α => ?_) cov_fin
  simp only [Un.cov, Real.exp_add, UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.1 _ _ (Real.exp_ne_zero _) (Real.exp_ne_zero _), map_mul]
  ac_rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MeasurePreservingIdeleScaleAndConjOnMaximalCompa
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact :
    ∀ (M₀ : Meas ℚ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        MeasurePreserving (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) M₀.ν M₀.ν ∧
        MeasurableEmbedding (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) := by
  intro M₀ t u hu
  haveI := M₀.prob
  let c : IdeleGroup ℚ := (iy (Real.exp t) * u : (A ℚ)ˣ)
  have h1 : MeasurePreserving (fun z : IdeleGroup ℚ => c * z⁻¹) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    (measurePreserving_mul_left (ideleMeasure ℚ) c).comp (Measure.measurePreserving_inv (ideleMeasure ℚ))
  have h2 : MeasurePreserving (cD u : G1 ℚ → G1 ℚ) M₀.κ M₀.κ :=
    ⟨(M.continuous_cD u).measurable, UpperTheory.maximalCompact_measure_map_conjDiag_eq M₀ u hu⟩
  let e1 : IdeleGroup ℚ ≃ᵐ IdeleGroup ℚ := (MeasurableEquiv.inv (IdeleGroup ℚ)).trans (MeasurableEquiv.mulLeft c)
  let e2 : G1 ℚ ≃ᵐ G1 ℚ :=
    { toFun := cD u
      invFun := cD (u⁻¹ : (A ℚ)ˣ)
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      measurable_toFun := (M.continuous_cD u).measurable
      measurable_invFun := (M.continuous_cD _).measurable }
  exact ⟨h1.prod h2, (e1.prodCongr e2).measurableEmbedding⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatRowLintegralAbsPowBounded
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re]

private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re]

private theorem re_congr {x y : A ℚ} (h : x.1 = y.1) : re x = re y := by
  unfold re
  have : TR.pInf ℚ x = TR.pInf ℚ y := by
    change (TR.infEq ℚ).symm x.1 = (TR.infEq ℚ).symm y.1
    rw [h]
  rw [this]

private theorem re_one : re (1 : A ℚ) = 1 := by
  simp [re]

private theorem row_sq {k : G1 ℚ} (hk : InfOrth k) :
    re (k 1 0) ^ 2 + re (k 1 1) ^ 2 = 1 := by
  have h := re_congr (hk 1 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  rw [re_add, re_mul, re_mul, re_one] at h
  nlinarith [h]

private theorem abs_re_le_infPart (x : Fin 2 → A ℚ) (j : Fin 2) : |re (x j)| ≤ ‖infPartPi x‖ := by
  rw [abs_re]
  exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
    (norm_le_pi_norm (infPartPi x) j)

private theorem abs_re_le {k : G1 ℚ} (hk : InfOrth k) (z : A ℚ) :
    |re z| ≤ 2 * ‖infPartPi fun j => z * row k j‖ := by
  set N := ‖infPartPi fun j => z * row k j‖ with hN
  have h0 : |re z| * |re (k 1 0)| ≤ N := by
    have h : |re (z * k 1 0)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 0
    rwa [re_mul, abs_mul] at h
  have h1 : |re z| * |re (k 1 1)| ≤ N := by
    have h : |re (z * k 1 1)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 1
    rwa [re_mul, abs_mul] at h
  have hs := row_sq hk
  have hz := abs_nonneg (re z)
  have ha := abs_nonneg (re (k 1 0))
  have hb := abs_nonneg (re (k 1 1))
  have hs' : |re (k 1 0)| ^ 2 + |re (k 1 1)| ^ 2 = 1 := by simpa [sq_abs] using hs
  by_contra hc
  push_neg at hc
  have hlt : |re (k 1 0)| + |re (k 1 1)| ≥ 1 := by nlinarith
  nlinarith

private theorem fin_eq {k : G1 ℚ} (z : A ℚ) :
    z.2 = (z * row k 0).2 * (-(k 0 1).2) + (z * row k 1).2 * (k 0 0).2 := by
  have hd := congrArg Prod.snd k.det_coe
  rw [Matrix.det_fin_two] at hd
  have hd' : (k 0 0).2 * (k 1 1).2 - (k 0 1).2 * (k 1 0).2 = 1 := hd
  change z.2 = (z.2 * (k 1 0).2) * (-(k 0 1).2) + (z.2 * (k 1 1).2) * (k 0 0).2
  linear_combination (-z.2) * hd'

theorem UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded :
    ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ e : ℝ, 1 < e → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ z : IdeleGroup ℚ, ‖Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j‖ₑ * ENNReal.ofReal (ab z ^ e) ∂(ideleMeasure ℚ) ≤ C := by
  intro Φ hΦ e he
  obtain ⟨M, hM⟩ := exists_nat_gt e
  obtain ⟨C₀, hC₀, L, hL, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ M
  set O : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := ↑(integralFiniteAdeles (𝓞 ℚ) ℚ) with hO
  have hOc : IsCompact O := isCompact_integralFiniteAdeles ℚ
  set K' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ =>
      p.1 0 * p.2.1 + p.1 1 * p.2.2) '' (L ×ˢ (O ×ˢ O)) with hK'
  have hK'c : IsCompact K' := (hL.prod (hOc.prod hOc)).image (by fun_prop)
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K' hK'c e he M hM
  set I : ℝ≥0∞ := ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K' then
    ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ M)⁻¹ * ab y ^ e) else 0) ∂(ideleMeasure ℚ) with hIdef
  refine ⟨(ENNReal.ofReal (C₀ * 2 ^ M) * I).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne), hIdef,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hab : 0 ≤ ab z ^ e := by
    have : 0 < ab z := (IdeleGroup.ideleModule ℚ z).2
    positivity
  set x : Fin 2 → A ℚ := fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j with hx
  have hm := hmaj x
  by_cases hxL : finPartPi x ∈ L
  · rw [Set.indicator_of_mem hxL, mul_one] at hm
    have hmem : ((z : (A ℚ)ˣ) : A ℚ).2 ∈ K' := by
      refine ⟨(finPartPi x, -(k 0 1).2, (k 0 0).2), ⟨hxL, ?_, ?_⟩, (fin_eq _).symm⟩
      · exact Subring.neg_mem _ (mem_integralFiniteAdeles.2 fun v => hk.2 v 0 1)
      · exact mem_integralFiniteAdeles.2 fun v => hk.2 v 0 0
    rw [if_pos hmem, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle := abs_re_le hk.1 ((z : (A ℚ)ˣ) : A ℚ)
    set N := ‖infPartPi x‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpow : (1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M ≤ 2 ^ M * (1 + N) ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hinv : ((1 + N) ^ M)⁻¹ ≤ 2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ := by
      rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv, inv_mul_le_iff₀ (by positivity)]
      exact hpow
    calc ‖Φ x‖ * ab z ^ e ≤ (C₀ * ((1 + N) ^ M)⁻¹) * ab z ^ e :=
          mul_le_mul_of_nonneg_right hm hab
      _ ≤ (C₀ * (2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹)) * ab z ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC₀) hab
      _ = C₀ * 2 ^ M * (((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ * ab z ^ e) := by ring
  · rw [Set.indicator_of_notMem hxL, mul_zero] at hm
    have h0 : Φ x = 0 := norm_le_zero_iff.1 hm
    simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.TsumUnfoldedIntegrandIdeleCoveringEqExpMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by simp [ab, map_mul]

private theorem ab_pos' (a : (A ℚ)ˣ) : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2

private theorem ab_inv' (a : (A ℚ)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by simp [ab, map_inv]

private theorem ab_diag' (α : ℚˣ) : ab (IdeleGroup.diagonal ℚ α) = 1 := by
  simp [ab, IdeleGroup.ideleModule_diagonal]

private theorem cpow_exp (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
  have h : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [Complex.cpow_def_of_ne_zero h, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem modid (t r : ℝ) (hr : 0 < r) (s : ℂ) :
    Complex.exp (2 * s * t) * ((((Real.exp t * r⁻¹)⁻¹ ^ 2 : ℝ)) : ℂ) =
      ((Real.exp t * Real.exp t * (r⁻¹ * r⁻¹) : ℝ) : ℂ) ^ (s - 1) * (r : ℂ) ^ (2 * s) := by
  obtain ⟨L, rfl⟩ : ∃ L, r = Real.exp L := ⟨Real.log r, (Real.exp_log hr).symm⟩
  have h1 : (Real.exp t * (Real.exp L)⁻¹)⁻¹ ^ 2 = Real.exp (2 * L - 2 * t) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : Real.exp t * Real.exp t * ((Real.exp L)⁻¹ * (Real.exp L)⁻¹) = Real.exp (2 * t - 2 * L) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, cpow_exp, cpow_exp, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cpow_ne {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne')]
  exact Complex.exp_ne_zero _

private theorem cg1 {G : Type} [CommGroup G] (e u z : G) :
    e * e * u * (z * z)⁻¹ = (e * u * z⁻¹) * (e * u * z⁻¹) * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg2 {G : Type} [CommGroup G] (e u z : G) :
    e * ((e * u * z⁻¹)⁻¹ * u) = z := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg3 {G : Type} [CommGroup G] (a u : G) :
    a * a * u⁻¹ = u * (u * a⁻¹)⁻¹ * (u * a⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg4 {G : Type} [CommGroup G] (a b u : G) :
    (u * a⁻¹) * (b * (a * a * u⁻¹)) = b * a := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gl_mD (a : (A ℚ)ˣ) : (gl (mD a)).val = !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl

private theorem mat_id (b a u : (A ℚ)ˣ) :
    aE b * gl (mD a) * dM u = Matrix.GeneralLinearGroup.scalar (Fin 2) (u * a⁻¹) * aE (b * (a * a * u⁻¹)) := by
  have h4 : ((u : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) * ((b : A ℚ) * ((a : A ℚ) * (a : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ))) = (b : A ℚ) * (a : A ℚ) := by
    have := congrArg Units.val (cg4 a b u)
    simpa only [Units.val_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aE, gl_mD, dM, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two, h4, mul_comm]

private theorem row_id (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a) * dM u * gl k).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * row k j := by
  simp [gl_mD, dM, UpperTheory.ConvolutionTheory.R2.G.row, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.tsum_unfoldedIntegrand_ideleCovering_eq_exp_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∀ p : IdeleGroup ℚ × G1 ℚ, (Summable fun α : ℚˣ => Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p)) →
        Complex.exp (2 * s * t) * (((χ.1 u : ℂˣ) : ℂ) * Un.Tt φ Φ t u p) = ∑' α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p) := by
  intro E _ _ D ω χ φ hA hχω Φ s t u hu p hS
  obtain ⟨z, k⟩ := p
  obtain ⟨e, he⟩ : ∃ e : (A ℚ)ˣ, e = iy (Real.exp t) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (A ℚ)ˣ, a = e * u * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (A ℚ)ˣ, c = u * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, y = a * a * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : GL (Fin 2) (A E), x = em E (gl (mD a) * dM u * gl k) := ⟨_, rfl⟩
  obtain ⟨Φz, hΦz⟩ : ∃ w : ℂ, w = Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := ⟨_, rfl⟩
  have haa : Un.aa t u z = a := by rw [ha, he]; rfl
  have hcov : ∀ α : ℚˣ, Un.cov t u α * (z * z)⁻¹ = IdeleGroup.diagonal ℚ α * y := fun α => by
    have h := cg1 e u z
    rw [← ha, ← hy] at h
    rw [← h, he]
    simp only [Un.cov, mul_assoc]
  have hrow : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD a) * dM u * gl k).val 1 j) =
      fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := by
    funext j
    rw [row_id, ← he, ← mul_assoc, ← Units.val_mul, ha, cg2]
  have hTt : Un.Tt φ Φ t u (z, k) = (((ab a)⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ x * Φz := by
    show (((ab (Un.aa t u z))⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ (em E (gl (mD (Un.aa t u z)) * dM u * gl k)) *
      (Φ fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u z)) * dM u * gl k).val 1 j) = _
    rw [haa, hrow, ← hx, ← hΦz]
  obtain ⟨W, hWd⟩ : ∃ W : ℚˣ → ℂ, W = fun α => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) := ⟨_, rfl⟩
  have hW : ∀ α : ℚˣ, Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * W α := fun α => by
    have h : aE (IdeleGroup.diagonal ℚ α) * (gl (mD a) * dM u * gl k) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * (aE (IdeleGroup.diagonal ℚ α * y) * gl k) := by
      calc _ = aE (IdeleGroup.diagonal ℚ α) * gl (mD a) * dM u * gl k := by simp only [mul_assoc]
        _ = _ := by rw [mat_id, mul_assoc, ← hc, ← hy]
    rw [hx, ← map_mul, h, map_mul, UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul E D ω φ hA, hWd]
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) * (Φz * ((ab z : ℝ) : ℂ) ^ (2 * s)) := ⟨_, rfl⟩
  have habd : ∀ α : ℚˣ, ab (IdeleGroup.diagonal ℚ α * y) = ab y := fun α => by
    rw [ab_mul', ab_diag', one_mul]
  have hχd : ∀ α : ℚˣ, χ.1 (IdeleGroup.diagonal ℚ α * y) = χ.1 y := fun α => by
    have h : χ.1 (IdeleGroup.diagonal ℚ α) = 1 := χ.2.2 α
    rw [map_mul, h, one_mul]
  have hH : ∀ α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (z * z)⁻¹, (z, k)) = W α * C := fun α => by
    rw [hcov α]
    show Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) * ((χ.1 (IdeleGroup.diagonal ℚ α * y) : ℂˣ) : ℂ) *
      ((ab (IdeleGroup.diagonal ℚ α * y) : ℝ) : ℂ) ^ (s - 1) *
      ((Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) = _
    rw [hχd, habd, ← hΦz, hC, hWd]
    ring
  have hS' : Summable fun α : ℚˣ => W α * C := by
    simpa only [hH] using hS
  simp only [hH]
  rw [hTt]
  by_cases h0 : Φz = 0
  · have hC0 : C = 0 := by rw [hC, h0]; ring
    simp [h0, hC0]
  have hCne : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (cpow_ne (ab_pos' y) _)) (mul_ne_zero h0 (cpow_ne (ab_pos' z) _))
  have hsW : Summable W := (summable_mul_right_iff hCne).1 hS'
  have hsum : Summable fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) := by
    simp only [hW]
    exact hsW.mul_left _
  have hFb : Un.Fb φ x = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * ∑' α, W α := by
    have h := (UpperTheory.hasSum_whittaker_diagTorus_rat_eq_unipotentConstantTerm E D ω φ hA x hsum).tsum_eq
    simp only [hW] at h
    rw [← h, tsum_mul_left]
  have hchar : ((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 = ((χ.1 y : ℂˣ) : ℂ) := by
    have h2 : ω.1 c ^ 2 = (χ.1 c)⁻¹ * (χ.1 c)⁻¹ := by
      have h := hχω c
      rw [mul_pow] at h
      rw [← mul_inv, ← sq]
      exact eq_inv_of_mul_eq_one_right h
    have h3 : χ.1 y = χ.1 u * ω.1 c ^ 2 := by
      rw [hy, cg3, ← hc, map_mul, map_mul, map_inv, h2, mul_assoc]
    rw [h3]
    push_cast
    rfl
  have hiy : ab e = Real.exp t := by
    rw [he, (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.1 _ (Real.exp_ne_zero t), abs_of_pos (Real.exp_pos t)]
  have hau : ab u = 1 := (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.2.2 u hu
  have hab : ab a = Real.exp t * (ab z)⁻¹ := by
    rw [ha, ab_mul', ab_mul', hiy, hau, ab_inv', mul_one]
  have haby : ab y = Real.exp t * Real.exp t * ((ab z)⁻¹ * (ab z)⁻¹) := by
    rw [hy, ab_mul', ab_mul', ab_inv', hab, hau]
    ring
  have hmod := modid t (ab z) (ab_pos' z) s
  rw [← hab, ← haby] at hmod
  rw [tsum_mul_right, hFb, hC, ← hchar]
  linear_combination (((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 * (∑' α, W α) * Φz) * hmod
end

