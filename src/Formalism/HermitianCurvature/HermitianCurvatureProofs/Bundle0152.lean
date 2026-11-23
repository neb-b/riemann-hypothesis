module

public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.StatementPN
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
public import Formalism.FlagUnipotentLattices.Bundle0003
public import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.FlagUnipotentLattices.Bundle0004

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section beta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem JF_cutF (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (g : Mat k r) :
    JF D (Formalism.FourierDecayAlt.D.cutF D χ F ε) g = ((χ (Gf k r D.z D.z' g / ε) : ℝ) : ℂ) • JF D F g := by
  unfold JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := Formalism.FourierDecayAlt.P.B5.ae_inSS D
  filter_upwards [hae] with p hp
  have e := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g
  simp only [sgs] at e
  simp only [Formalism.FourierDecayAlt.D.cutF, e]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem hsVec_smul' [FiniteDimensional ℂ Wq] (a : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (a • A) = a • hsVec A := by
  unfold hsVec; ext i; simp

theorem hsVec_cont' [FiniteDimensional ℂ Wq] : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  unfold hsVec
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)

theorem inner_self_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem bcWeight_nonneg' (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_cutF [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) =
      ∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 *
        ‖hsVec (JF D F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
  unfold beta betaBig
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [gq]
  rw [JF_cutF, hsVec_smul', inner_smul_left, inner_smul_right, inner_self_real, Complex.conj_ofReal]
  push_cast
  ring

theorem cut_bound {χ : ℝ → ℝ} (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |χ x| ≤ M := by
  obtain ⟨hs, ⟨δ, _, h0⟩, h1⟩ := hχ
  have hc : Continuous χ := hs.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x < δ
  · rw [h0 x hx, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  by_cases hx1 : 1 ≤ x
  · rw [h1 x hx1, abs_one]; exact le_max_right _ _
  · have := hM x ⟨not_lt.1 hx, le_of_not_ge hx1⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

end beta

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_cut_limit (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (hA : AB k r ≤ A) (hF : ∀ m : ℕ, InCC A m F) :
    normSq D F ≠ ⊤ ∧
      Tendsto (fun ε => beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((normSq D F).toReal : ℝ) : ℂ)) := by

  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hA
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin : normSq D F ≠ ⊤ := (hC0 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  refine ⟨hfin, ?_⟩
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  set J : (Fin r → ℂ) × ℂ → _ := fun q => hsVec (JF D F (gq D q)) with hJ
  set h : (Fin r → ℂ) × ℂ → ℝ := fun q => w q * ‖J q‖ ^ 2 with hh
  set μQ : Measure ((Fin r → ℂ) × ℂ) := volume.restrict (Qset D) with hμQ
  have hw0 : ∀ q, 0 ≤ w q := fun q => bcWeight_nonneg' _ _ q
  have hh0 : ∀ q, 0 ≤ h q := fun q => mul_nonneg (hw0 q) (sq_nonneg _)
  have hwQ : ∀ q, q ∉ Qset D → w q = 0 := by
    intro q hq
    have : ¬ 0 < w q := hq
    exact le_antisymm (not_lt.1 this) (hw0 q)

  have hcont : ContinuousOn F (GV k r) := Formalism.FourierDecayAlt.P.B7.jc_cont (hF 4)
  have hJm : AEStronglyMeasurable J μQ := by
    have h1 := Formalism.FourierDecayAlt.P.B7.jc_aesm_J D hcont (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rw [e] at h1
    exact hsVec_cont'.comp_aestronglyMeasurable h1
  have hwm : Measurable w := Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _
  have hhm : AEStronglyMeasurable h μQ := hwm.aestronglyMeasurable.mul (hJm.norm.pow 2)

  have hlin : normSq D F = ∫⁻ q, ENNReal.ofReal (h q) ∂μQ := by
    show (∫⁻ q, ENNReal.ofReal (h q)) = _
    rw [hμQ, setLIntegral_eq_of_support_subset]
    intro q hq
    by_contra hn
    apply hq
    simp only [hh, hwQ q hn, zero_mul, ENNReal.ofReal_zero]
  have hhi : Integrable h μQ := by
    refine ⟨hhm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hh0), ← hlin]
    exact lt_top_iff_ne_top.2 hfin
  have hlim : ∫ q, ((h q : ℝ) : ℂ) ∂μQ = (((normSq D F).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhm, ← hlin]

  obtain ⟨M, hM0, hM⟩ := cut_bound hχ
  have hχc : Continuous χ := hχ.1.continuous
  have hGc : Continuous fun x : Mt k r => Gf k r D.z D.z' (Matrix.of x) :=
    (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z').comp continuous_id
  set Fe : ℝ → (Fin r → ℂ) × ℂ → ℂ := fun ε q =>
    ((w q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 * ‖J q‖ ^ 2 : ℝ) : ℂ) with hFe
  have hbeta : ∀ ε, beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) = ∫ q, Fe ε q ∂μQ := by
    intro ε
    rw [beta_cutF, hμQ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro q hq
    simp only [hFe, hwQ q hq, zero_mul, Complex.ofReal_zero]
  simp_rw [hbeta]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun q => M ^ 2 * h q) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hχm : AEStronglyMeasurable (fun q => χ (Gf k r D.z D.z' (gq D q) / ε)) μQ := by
      refine (((hχc.comp (hGc.div_const ε)).measurable.comp
        (Formalism.FourierDecayAlt.P.B7.measurable_gqM D)).aestronglyMeasurable).congr ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
      simp only [Function.comp_apply]
      rw [Formalism.FourierDecayAlt.P.B7.gqM_eq D hq]
      rfl
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hwm.aestronglyMeasurable.mul (hχm.pow 2)).mul (hJm.norm.pow 2))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun q => ?_
    simp only [hFe, Complex.norm_real, Real.norm_eq_abs]
    have h2 : χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 q) (sq_nonneg _)) (sq_nonneg _))]
    simp only [hh]
    nlinarith [hw0 q, sq_nonneg ‖J q‖, mul_nonneg (hw0 q) (sq_nonneg ‖J q‖)]
  · exact hhi.const_mul _
  · filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
    have hG : 0 < Gf k r D.z D.z' (gq D q) := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq).2.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds hG)] with ε hε hle
    simp only [hFe, hh]
    rw [hχ.2.2 _ ((one_le_div (Set.mem_Ioi.mp hε)).mpr hle)]
    push_cast
    ring

end core

theorem AB_le_of_thr (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (h : 1 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    AB k r ≤ A₀ := by
  unfold AB
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set x : ℝ := (r : ℝ) + 1 with hx
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (k : ℝ) + r ≤ n := by rw [hn]; linarith
  have h2 : 1 ≤ x := by rw [hx]; linarith
  have h3 : 3 ≤ n := by rw [hn]; linarith
  have h4 : x ≤ x ^ 4 := by
    have : 1 ≤ x ^ 3 := one_le_pow₀ h2
    nlinarith
  have h5 : 2 * n + 1 ≤ n ^ 3 := by nlinarith
  have h6 : 0 ≤ (N : ℝ) * n ^ 2 := mul_nonneg hN (sq_nonneg _)
  calc 2 * ((k : ℝ) + r) * x + 1 ≤ 2 * n * x + 1 := by nlinarith
    _ ≤ x * (2 * n + 1) := by nlinarith
    _ ≤ x * n ^ 3 := by nlinarith
    _ ≤ x ^ 4 * n ^ 3 := by nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 3]
    _ ≤ 1 * x ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 4]
    _ ≤ A₀ := h

end Formalism.FourierDecayAlt.P.JCTx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem beta_cutoff_limit : Formalism.FourierDecayAlt.JCT.BetaCutLimit := by
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP v
  obtain ⟨_, _, _, hB, _, _, _, _, _, _, hk, hA, _⟩ := hP
  exact Formalism.FourierDecayAlt.P.JCTx2.beta_cut_limit (T v).base χ hB.1 (f v) A₀
    (Formalism.FourierDecayAlt.P.JCTx2.AB_le_of_thr S.G.k S.G.r S.Ntop A₀ hk hA) (fun m => (hB.2 v).2.2.2.2.1 m)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAssemble
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bd_of_ubl {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (z z' : Fin (2 * r + k + 1) → ℂ) (φ : B.Mat k r → F) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ geG k r z z' ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (geG k r z z' ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r z z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem geometry_assembly_holds : GeomAssemble := by
  intro hS hEn hEi hAt hB0 hU
  refine ⟨6, by norm_num, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Bs := (T v).base with hBs
  have hk : 1 ≤ S.G.k := Bs.k_pos
  have hz : C2.StdZ S.G.k S.G.r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
  have hz' : C2.StdZ S.G.k S.G.r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
  refine ⟨nuG Bs.z Bs.z', nuG' Bs.z Bs.z', ioG Bs.z Bs.z', ?_⟩
  obtain ⟨s1, s2, s3⟩ := hS _ _ _ _ hk hz hz'
  obtain ⟨C0, hC0⟩ := hB0 _ _ _ _ hk hz hz'
  have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hBg : ∀ e γ : ℕ, e ≤ 4 * (S.G.r + 1) → γ ≤ 2 * (S.G.r + 1) → (e : ℝ) + γ ≤ Cb * ((S.G.r : ℝ) + 1) := by
    intro e γ he hγ
    have he' : (e : ℝ) ≤ 4 * ((S.G.r : ℝ) + 1) := by exact_mod_cast he
    have hγ' : (γ : ℝ) ≤ 2 * ((S.G.r : ℝ) + 1) := by exact_mod_cast hγ
    nlinarith
  have hpos : ∀ ε : ℝ, 0 < ε → ∀ g ∈ geG S.G.k S.G.r Bs.z Bs.z' ε, g ∈ posG S.G.k S.G.r Bs.z Bs.z' :=
    fun ε hε g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2⟩
  refine ⟨s1, s2, s3, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp g hg
    obtain ⟨h1, h2⟩ := hEn _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg
    exact ⟨h1, h2, hEi _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg⟩
  · intro ε hε m
    obtain ⟨⟨e, γ, he, hγ, hu⟩, -, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).1⟩ hu m
  · intro ε hε m
    obtain ⟨-, ⟨e, γ, he, hγ, hu⟩, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.1⟩ hu m
  · intro ε hε m
    obtain ⟨-, -, ⟨e, γ, he, hγ, hu⟩⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.2⟩ hu m
  · intro q hq
    have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' := by
      show (D.parOf S v).T * (D.parOf S v).T' = _
      rw [hPl.2.2.2.1, hPl.2.2.2.2.1]
    have hq2 : Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' < Complex.normSq q.2 := hTT ▸ hq.2
    exact hAt _ _ _ _ Bs.μsec hk hz hz' Bs.sec q.1 q.2 hq.1 hq2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomInvSqrt
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phiS (c t : ℝ) : ℝ := sc c t * (Real.sqrt t)⁻¹

def PhiS (c : ℝ) (w : ℂ) : ℂ := ((phiS c w.re : ℝ) : ℂ)

lemma phiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (phiS c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 8 < t
  · have h1 : ContDiff ℝ ∞ (sc c) := by
      unfold sc
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    have hpos : 0 < t := by linarith
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.sqrt y)⁻¹) t :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact h1.contDiffAt.mul h2
  · have hev : phiS c =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < c / 4 by linarith)] with y hy
      have hy' : y < c / 4 := hy
      have h0 : (y - c / 4) / (c / 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp [phiS, sc, Real.smoothTransition.zero_of_nonpos h0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma phiS_ev {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : c / 2 < t) :
    phiS c =ᶠ[𝓝 t] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with y hy
  have hy' : c / 2 < y := hy
  have hc4 : 0 < c / 4 := by positivity
  have h1 : 1 ≤ (y - c / 4) / (c / 4) := by
    rw [le_div_iff₀ hc4]
    linarith
  have hy0 : 0 ≤ y := by linarith
  simp only [phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]
  rw [Real.rpow_neg hy0, Real.sqrt_eq_rpow]

lemma phiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, c ≤ t → ‖iteratedFDeriv ℝ j (phiS c) t‖ ≤ A := by
  refine ⟨|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * c ^ (-(1 / 2 : ℝ) - j), fun t ht => ?_⟩
  have hct : c / 2 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hev := phiS_ev hc hct
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq : -(1 / 2 : ℝ) - (j : ℝ) ≤ 0 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht hq) (abs_nonneg _)

lemma PhiS_eq : ∀ c : ℝ, PhiS c = (Complex.ofRealCLM) ∘ (phiS c ∘ Complex.reCLM) := by
  intro c
  funext w
  simp [PhiS]

lemma PhiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (PhiS c) := by
  rw [PhiS_eq]
  exact Complex.ofRealCLM.contDiff.comp ((phiS_cd hc).comp Complex.reCLM.contDiff)

lemma PhiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ B : ℝ, ∀ w ∈ {w : ℂ | c ≤ w.re}, ‖iteratedFDeriv ℝ j (PhiS c) w‖ ≤ B := by
  obtain ⟨A, hA⟩ := phiS_bound hc j
  refine ⟨‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖), fun w hw => ?_⟩
  have hw' : c ≤ w.re := hw
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [PhiS_eq]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (phiS c ∘ Complex.reCLM)) w‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (phiS c ∘ Complex.reCLM) w‖ :=
        Complex.ofRealCLM.norm_iteratedFDeriv_comp_left ((phiS_cd hc).comp Complex.reCLM.contDiff).contDiffAt hj
    _ ≤ ‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖) := by
        gcongr
        rw [Complex.reCLM.iteratedFDeriv_comp_right (phiS_cd hc) w hj]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr
        exact hA _ (by simpa using hw')

theorem unipotent_inverse_sqrt_bound : UBLInvSqrt := by
  intro k r d P hP S hSG c hc hSc n
  obtain ⟨hPcd, -⟩ := poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hU : UBL (fun g => PhiS c (P g)) S n 0 d :=
    ubl_fdb P hPcd S hSG {w : ℂ | c ≤ w.re} hSc d n M hM (PhiS c) (PhiS_cd hc) (PhiS_bound hc)
  refine ubl_congr (V := P ⁻¹' {w : ℂ | c / 2 < w.re}) ?_ ?_ hSG ?_ hU
  · exact (isOpen_lt continuous_const Complex.continuous_re).preimage hPcd.continuous
  · intro g hg
    have h := hSc g hg
    show c / 2 < (P g).re
    linarith
  · intro g _ hg
    have hg' : c / 2 < (P g).re := hg
    have hc4 : 0 < c / 4 := by positivity
    have h1 : 1 ≤ ((P g).re - c / 4) / (c / 4) := by
      rw [le_div_iff₀ hc4]
      linarith
    show (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ) = PhiS c (P g)
    rw [PhiS, phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
section
namespace Formalism.FourierDecayAlt.P.NormChainLemmas

open Formalism.FourierDecayAlt.PN Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem exactCores : Formalism.FourierDecayAlt.PN.ExactCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.S4.step4, Formalism.HermitianLatticeCounting.Final.S4.omCount, Formalism.HermitianLatticeCounting.Final.S4.weightedCS,
   Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four⟩

theorem loopCores : Formalism.FourierDecayAlt.PN.LoopCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.single_row_lattice_sum_bound,
   Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gainSqrt, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lattice_exp_sum_upper_bound, Formalism.FourierDecayAlt.Final.pb_loopsJoint,
   Formalism.FourierDecayAlt.Final.pb_loopsGiveRows⟩

theorem nGChain : Formalism.FourierDecayAlt.PN.NGChain :=
  ⟨exactCores, Formalism.FourierDecayAlt.Final.pn_classSquaresSum, Formalism.FourierDecayAlt.Final.pn_rowFromClasses,
   Formalism.FourierDecayAlt.Final.pn_classCS, Formalism.FourierDecayAlt.Final.pn_firstBracket, Formalism.FourierDecayAlt.Final.pn_secondBracket,
   Formalism.FourierDecayAlt.Final.pn_meanAmpJoint, Formalism.FourierDecayAlt.Final.pn_rowNGAbstract, Formalism.FourierDecayAlt.Final.pn_normBound,
   Formalism.FourierDecayAlt.Final.pn_framePassage, Formalism.FourierDecayAlt.Final.pn_normRe, Formalism.FourierDecayAlt.Final.pn_exponentSum,
   Formalism.FourierDecayAlt.Final.pn_nGNumbers⟩

end Formalism.FourierDecayAlt.P.NormChainLemmas

namespace Formalism.FourierDecayAlt.P

theorem loop_kernels : Formalism.FourierDecayAlt.PN.LoopCores := NormChainLemmas.loopCores

theorem norm_chain : Formalism.FourierDecayAlt.PN.NGChain := NormChainLemmas.nGChain

end Formalism.FourierDecayAlt.P
end

