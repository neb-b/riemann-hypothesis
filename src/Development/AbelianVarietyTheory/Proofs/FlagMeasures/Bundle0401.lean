module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded
section
noncomputable section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covN_haarLie_smul {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    haarLie S κ = κ • haarLie S 1 := by
  unfold haarLie; rw [one_smul]

theorem covN_muNB_one (D : D7) : muNB D 1 =
    (kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • GlobalTheory.Amp.lebN D.R.k D.R.rS := by
  rw [muNB, covN_haarLie_smul, _root_.GlobalTheory.Amp.NLie.haarLie_eq_lebN, smul_smul]

theorem covN_pi_smul {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0) : Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    first
    | (have h : ((c : ℝ≥0∞) • μ) = c • μ := (ENNReal.smul_def c μ).symm
       rw [h]; infer_instance)
    | (rw [← ENNReal.smul_def]; infer_instance)
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem covN_arith (v : ℝ) (hv : 1 ≤ v) (r k f : ℕ) :
    1 ≤ ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) := by
  have hv0 : 0 < v := by linarith
  have h2v : 0 < 2 * v := by linarith
  have hA : (2 * v) ^ (-((r : ℝ) * k)) * v ^ (k * r) = ((2 : ℝ) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_pow,
      show k * r = r * k from Nat.mul_comm k r]
    have : (0 : ℝ) < v ^ (r * k) := pow_pos hv0 _
    field_simp
  have hB : ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) =
      (((2 : ℝ) ^ (r * k))⁻¹ * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f := by
    rw [← hA, pow_mul, ← mul_pow]
    ring
  rw [hB]
  apply one_le_pow₀
  rw [← div_eq_inv_mul, one_le_div (by positivity)]
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith [Nat.zero_le (r * (r - 1))]

theorem covNC_holds : CovNC := by
  intro D large₂ X Y u C hS
  obtain ⟨hCM, hPl, hv, hv1, -, hcard, -, -, -, hnorm, hfin, hg2, -⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hS
  obtain ⟨N, hF, hF', hj, hT, h𝔡, hTerm, hRef, hist⟩ := _root_.GlobalTheory.IdNF.idNFC_holds D large₂ X Y u hS (VS D).L0 (Or.inr rfl)
  obtain ⟨hU, -, hz, -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main D.host.E (VS D).V (HV D) hCM D.R.rS N (gS D) (VS D).L0 (by omega) hTerm
  have hzL : N.F.z ∈ GlobalTheory.HermLat.latL N.F N.F' (VS D).L0 := by
    have h := (hz 1).2 (by simp)
    simpa using h
  have hFr := _root_.GlobalTheory.TypeAsm.baseFrame_real D large₂ X u C hS N hF hF' hj hT (hist rfl)
  have hN𝔡 : (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (2 * Fintype.card D.what₂.Tau) := by
    rw [h𝔡, hnorm, hv, hcard]
  have hv1' : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by rw [hv]; exact hv1
  obtain ⟨Ω, hΩ, hlo, hhi⟩ := _root_.GlobalTheory.DegVol.RefCov.covol_ref D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D)
    (fun _ => 0) (fun τ => phiV C τ) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) (fun _ => 1)
    hPl hfin hFr hN𝔡 hv1' _ hU hzL
  rw [hRef, _root_.GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf D large₂ X Y u C hS N hF hF'] at hΩ
  have hsw := (_root_.GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product D.R.k D.R.rS N.j (fun _ => 0) monotone_const (by intro a b _; simp [hj])).2.2.2 hj
  rw [hsw, hj, hv, hcard, Nat.sub_zero] at hlo hhi
  obtain ⟨hc, h1, hmul, hinv, hNs⟩ := _root_.GlobalTheory.CovGrp.cov_grp D X Y u C
  have heq := _root_.GlobalTheory.FundEq.measure_eq D.what₂.Tau D.R.k D.R.rS _ _ _ hc h1 hmul hinv hNs hΩ (_root_.GlobalTheory.TypeAsm.CovTrans.isFund_trI D X Y u C)
  haveI : SigmaFinite (GlobalTheory.Amp.lebN D.R.k D.R.rS) := (_root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN D.R.k D.R.rS).1
  set c : ℝ≥0 := ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1).toNNReal *
    2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) with hc_def
  have hk : kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) = (c : ℝ≥0∞) := by
    rw [hc_def, kapN, ENNReal.ofReal]
    push_cast
    rfl
  have hcov : covN C Y u = (c : ℝ≥0∞) ^ D.R.f * Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω := by
    rw [covN, covN_muNB_one, hk, covN_pi_smul, Measure.smul_apply, smul_eq_mul, hcard, ← heq]
  have hfinΩ : Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hne : covN C Y u ≠ ⊤ := by
    rw [hcov]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfinΩ
  refine ⟨hne, ?_⟩
  have hlo' := (ENNReal.ofReal_le_iff_le_toReal hfinΩ).1 hlo
  have hlpos : 0 < lossV D := by
    unfold lossV; exact pow_pos (by linarith) _
  have hcr : ((c : ℝ≥0∞) ^ D.R.f).toReal = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, hc_def, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast; ring
  rw [hcov, ENNReal.toReal_mul, hcr]
  have key := covN_arith D.host.v hv1 D.R.rS D.R.k D.R.f
  have hpos : 0 ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by positivity
  have hq : D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D =
      D.host.v ^ (D.R.k * D.R.rS * D.R.f) := by
    unfold lossV; field_simp
  calc (1 : ℝ) ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f * D.host.v ^ (D.R.k * D.R.rS * D.R.f) := key
    _ = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f *
        (D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D) := by rw [hq]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hlpos.le
      exact mul_le_mul_of_nonneg_left hlo' hpos

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometries
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

theorem form_mulVec_mulVec {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (J γ : Matrix (Fin m) (Fin m) E)
    (x y : Fin m → E) :
    GlobalTheory.SgAlg.form σ J (γ *ᵥ x) (γ *ᵥ y) = GlobalTheory.SgAlg.form σ (GlobalTheory.SgAlg.cT σ γ * J * γ) x y := by
  have h : (fun i => σ ((γ *ᵥ y) i)) = (fun i => σ (y i)) ᵥ* GlobalTheory.SgAlg.cT σ γ := by
    funext i
    simp [GlobalTheory.SgAlg.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  simp only [GlobalTheory.SgAlg.form]
  rw [h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem form_single_single {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (M : Matrix (Fin m) (Fin m) E)
    (i j : Fin m) : GlobalTheory.SgAlg.form σ M (Pi.single j 1) (Pi.single i 1) = M i j := by
  simp [GlobalTheory.SgAlg.form, dotProduct, Pi.single_apply, Matrix.mulVec_single]

theorem isUn_iff_mem_isom {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) :
    GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  constructor
  · intro hU
    change ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y
    intro x y
    rw [← vecOf_crdH X x, ← vecOf_crdH X y, n_vecOf hγ, n_vecOf hγ, hT_vecOf, hT_vecOf,
      form_mulVec_mulVec, hU]
  · intro hn
    have hn' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
    ext i j
    rw [← form_single_single _ (GlobalTheory.SgAlg.cT _ γ * Jc X * γ) i j, ← form_mulVec_mulVec,
      ← hT_vecOf X, ← n_vecOf hγ, ← n_vecOf hγ, hn', hT_vecOf, form_single_single]

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometrySubOneOrthogonalLeCoordinates
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem eOf_Pc_apply (u : D.what₂.Word) (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    GlobalTheory.SgAlg.eOf (Pc X u) i a = crdH X (X.eX a) i := by
  simp [GlobalTheory.SgAlg.eOf, Pc]

theorem Xsp_Fu_eq_span (u : D.what₂.Word) :
    Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem vecOf_eOf_mulVec (u : D.what₂.Word) (c : Fin D.R.rS → D.host.E) :
    vecOf X (GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) = ∑ a, c a • X.eX a := by
  have hcol : GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c = ∑ a, c a • crdH X (X.eX a) := by
    ext i
    simp [Matrix.mulVec, dotProduct, eOf_Pc_apply, Finset.sum_apply, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hcol, map_sum]
  simp only [map_smul, vecOf_crdH]

theorem cT_eOf_mulVec_apply (u : D.what₂.Word) (v : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) (a : Fin D.R.rS) :
    ((GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v) a
      = (VS D).hT (X.eX a) (vecOf X v) := by
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← vecOf_crdH X (X.eX a), hT_vecOf]
  simp only [GlobalTheory.SgAlg.form, GlobalTheory.SgAlg.cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, eOf_Pc_apply]

theorem mem_orth_span_iff (y : (VS D).V) :
    y ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) ↔
      ∀ a, (VS D).hT (X.eX a) y = 0 := by
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => simp
    | add x z _ _ hx hz => simp [hx, hz]
    | smul c x _ hx => simp [hx]

theorem orth_cond_iff_coord : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  intro D X u n γ hγ
  have inj : Function.Injective (vecOf X) := fun a b h => by
    simpa [crdH_vecOf] using congrArg (crdH X) h
  have hperp : ∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 ↔
      ∀ a, (VS D).hT (X.eX a) (vecOf X v) = 0 := by
    intro v
    constructor
    · intro h a
      have h' := congrFun h a
      rwa [cT_eOf_mulVec_apply] at h'
    · intro h
      funext a
      rw [cT_eOf_mulVec_apply]
      exact h a
  have himg : ∀ v c, (γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c ↔
      n (vecOf X v) - vecOf X v = ∑ a, c a • X.eX a) := by
    intro v c
    rw [← vecOf_eOf_mulVec X u c, n_vecOf hγ, ← map_sub]
    exact inj.eq_iff.symm
  rw [Xsp_Fu_eq_span X u]
  constructor
  · intro H x hx
    rw [mem_orth_span_iff X x] at hx
    obtain ⟨c, hc⟩ := H (crdH X x) ((hperp _).2 (by simpa [vecOf_crdH] using hx))
    rw [himg, vecOf_crdH] at hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, hc.symm⟩
  · intro H v hv
    have hx : vecOf X v ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) :=
      (mem_orth_span_iff X (vecOf X v)).2 ((hperp v).1 hv)
    have hm := H _ hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, (himg v c).2 hc.symm⟩

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreserved
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem crdH_injective : Function.Injective (crdH X) := by
  intro y y' h
  rw [← vecOf_crdH X y, h, vecOf_crdH]

theorem mul_eOf_Pc_apply (u : D.what₂.Word)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (γ * GlobalTheory.SgAlg.eOf (Pc X u)) i a = (γ *ᵥ crdH X (X.eX a)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, GlobalTheory.SgAlg.eOf, Pc]

theorem eOf_Pc_mul_apply (u : D.what₂.Word) (ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (GlobalTheory.SgAlg.eOf (Pc X u) * ν) i a = crdH X (∑ b, ν b a • X.eX b) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coordEquiv_symm_apply, map_sum]
  simp [Matrix.mul_apply, GlobalTheory.SgAlg.eOf, Pc, coordEquiv_symm_apply, Finset.sum_apply, mul_comm]

theorem xflag_Fu (u : D.what₂.Word) (j : ℕ) :
    Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j = Submodule.span D.host.E (X.eX '' {i | i.1 < j}) := by
  show (X.Fu u).Xa j = _
  unfold FlagG.Xa
  rw [X.Fu_e]

theorem flag_iff {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) :
    (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
    ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔
      ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  intro hγ
  have hcol : ∀ ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν ↔ ∀ a, n (X.eX a) = ∑ b, ν b a • X.eX b := by
    intro ν
    constructor
    · intro h a
      apply crdH_injective X
      funext i
      rw [← eOf_Pc_mul_apply, ← h, mul_eOf_Pc_apply, hγ]
    · intro h
      ext i a
      rw [mul_eOf_Pc_apply, eOf_Pc_mul_apply, ← h, hγ]
  simp only [xflag_Fu]
  constructor
  · rintro ⟨ν, hν, h⟩
    have h1 := (hcol ν).1 h
    have hstep : ∀ a : Fin D.R.rS,
        n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
      intro a
      rw [h1 a]
      have hs : ∑ b, ν b a • X.eX b - X.eX a = ∑ b, (ν b a - if b = a then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [hs]
      refine Submodule.sum_mem _ fun b _ => ?_
      rcases lt_trichotomy b a with hb | rfl | hb
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · simp [(hν b b).2 rfl]
      · simp [(hν b a).1 hb, hb.ne']
    intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hij : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hsub : {k : Fin D.R.rS | k.1 < i.1} ⊆ {k : Fin D.R.rS | k.1 < j} :=
        fun k (hk : k.1 < i.1) => (lt_of_lt_of_le hk hij : k.1 < j)
      exact Submodule.span_mono (Set.image_mono hsub) (hstep i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      convert Submodule.add_mem _ hx hy using 1
      abel
    | smul c x _ hx =>
      rw [map_smul]
      convert Submodule.smul_mem _ c hx using 1
      rw [smul_sub]
  · intro h
    have ha : ∀ a : Fin D.R.rS, ∃ l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.1 < a.1},
        Finsupp.linearCombination D.host.E X.eX l = n (X.eX a) - X.eX a := by
      intro a
      rw [← Finsupp.mem_span_image_iff_linearCombination]
      exact h a.1 (X.eX a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    choose l hl hl2 using ha
    refine ⟨fun b a => l a b + if b = a then 1 else 0, ?_, (hcol _).2 fun a => ?_⟩
    · intro i j
      constructor
      · intro hji
        have h0 : l j i = 0 := (Finsupp.mem_supported' _ _).1 (hl j) i (fun hh => absurd (hh : i.1 < j.1) (not_lt.2 (le_of_lt hji)))
        simp [h0, (ne_of_lt hji).symm]
      · rintro rfl
        have h0 : l i i = 0 := (Finsupp.mem_supported' _ _).1 (hl i) i (fun hh => lt_irrefl i.1 hh)
        simp [h0]
    · have hlc := hl2 a
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hlc]
      abel

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlace
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem coordMat_place : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  intro D X x n γ hR hγ τ
  obtain ⟨M, -, h1, -, h4⟩ := hR
  have hPu : IsUnit (X.B.I.P (vOf X τ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit (vOf X τ))
  have hP : X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹ =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) := by
    rw [h1 (vOf X τ)]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

  have hN : ∀ c, γ *ᵥ c = (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X)) *ᵥ c := by
    intro c
    have hc := hγ (vecOf X c)
    rw [crdH_vecOf] at hc
    rw [← hc]
    funext i
    rw [crdH_eq_crd, h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← (ci X).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← crdH_eq_crd, crdH_vecOf]
  have hγe : γ = ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X) :=
    Matrix.toLin'.injective (LinearMap.ext fun c => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hN c)
  rw [hP, hγe]
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, X.φ_eq]
  congr 1
  simp [vOf]

end GlobalTheory.CovDomGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPtsEqImage
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMeanStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattices_mean_eq_genus_mean : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ → ∀ reps : Finset (LatW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps → ∀ N : LatW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) → (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞) := by
  first | exact @GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | exact GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | (intros; apply GlobalTheory.MeanGenus.mean_rows_eq_mean_genus <;> assumption)
end

