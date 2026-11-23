module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
public import Formalism.HermitianCurvature.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompPS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

section ps

variable {TT : ℝ}

lemma gg_eval (ζ : ℂ) : gg TT ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ]
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.mul_conj]
  push_cast
  ring

lemma ps_const (c : ℂ) : PS TT (fun _ => c) := ⟨0, MvPolynomial.C c, fun ζ _ => by simp⟩

lemma ps_id : PS TT (fun ζ => ζ) := ⟨0, MvPolynomial.X 0, fun ζ _ => by simp⟩

lemma ps_conj : PS TT (fun ζ => conj ζ) := ⟨0, MvPolynomial.X 1, fun ζ _ => by simp⟩

lemma ps_sig : PS TT (fun ζ => sig TT ζ) := ⟨0, MvPolynomial.X 2, fun ζ _ => by simp⟩

lemma ps_add {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ n * p + (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ m * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_pow, ← gg_eval, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma ps_mul {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, p * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_mul, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma sig_sq {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ * sig TT ζ = gg TT ζ := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

lemma sig_ne {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ ≠ 0 := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith))

lemma ps_sigInv : PS TT (fun ζ => (sig TT ζ)⁻¹) := by
  refine ⟨1, MvPolynomial.X 2, fun ζ hζ => ?_⟩
  rw [pow_one, ← sig_sq hζ, mul_assoc, mul_inv_cancel₀ (sig_ne hζ), mul_one]
  simp

end ps

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRKapLine
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

theorem kappa_line_holds : KapLine := by
  intro Wp Wq _ _ _ _ _ _ P Bs hμs hk X d hA Pr hPr
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := id hA
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hμs] at hcs
  have hH : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩
  obtain ⟨Qs, hK⟩ := Gauge.GC.gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  refine ⟨Qs, hK, ?_⟩
  intro ζ hζ Xf hXf ρ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp

  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => Xf) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hXf p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  have hval : Φ c0 μ = Xf := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, μ) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζT⟩⟩

  have hfib : ∀ σ, Xf.comp (Qs σ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro σ
    have h1 := hK.2.2.2 (fun τ => if τ = σ then 1 else 0) Φ' qq
    have h2 : (∑ τ, (if τ = σ then (1 : ℂ) else 0) • Qs τ) = Qs σ := by
      simp [ite_smul]
    rw [h2] at h1
    change (((d.κ fun τ => if τ = σ then 1 else 0).1 Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 μ = (Φ c0 μ).comp (Qs σ) at h1
    rw [hval] at h1
    rw [← h1]
    intro p hp
    have h := ((d.κ fun τ => if τ = σ then 1 else 0).1 Φ').2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
    simp only at h
    rw [hp.2.2] at h
    exact h.symm

  have hfix : ∀ σ, (Pr σ ν).comp (Xf.comp (Qs σ)) = Xf.comp (Qs σ) := by
    intro σ
    have hE : (Xf.comp (Qs σ)).comp (Qs σ) = Xf.comp (Qs σ) := by
      rw [ContinuousLinearMap.comp_assoc, hK.1 σ σ, if_pos rfl]
    have hEeig := (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hK ζ hζT _ hFr' σ _ (hfib σ)).1 hE
    ext v
    rw [ContinuousLinearMap.comp_apply]
    refine ((hPr.2.2 ν hpos).2.2.2 σ _).2 ?_
    intro Fr2 hFr2 w
    rw [hνfix] at hFr2
    rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w
      ((Xf.comp (Qs σ)) v), hpass _ (hfib σ) w v, hgl']
    have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
    conv_lhs => rw [hw]
    exact hEeig _ v
  have hs : Xf = ∑ σ, Xf.comp (Qs σ) := by
    rw [← ContinuousLinearMap.comp_finsetSum, hK.2.1]
    rfl
  have hPP := (hPr.2.2 ν hpos).2.2.1
  conv_lhs => rw [hs]
  rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single ρ]
  · exact hfix ρ
  · intro σ _ hσ
    rw [← hfix σ, ← ContinuousLinearMap.comp_assoc, hPP ρ σ, if_neg (Ne.symm hσ), ContinuousLinearMap.zero_comp]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jdc_thrW (o : ℕ) (A d : ℝ) (hd : 0 ≤ d)
    (h : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  unfold Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  rw [hn] at h
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) <
      12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by
    nlinarith [pow_nonneg hr 3, mul_nonneg hr (mul_nonneg hk hk), mul_nonneg (mul_nonneg hr hr) hk,
      mul_nonneg hr hr, mul_nonneg hr hk, mul_nonneg hk hk]
  have hpos : 0 < 12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  constructor <;> linarith

theorem jdc_om_sub_gpos (Db : B.RealPlaceData k r Wp Wq) : JF.Om k r Db.z Db.z' ⊆ B.GPos Db := by
  intro g hg
  unfold JF.Om Q.OmPlus at hg
  unfold B.GPos
  exact ⟨hg.1, hg.2.2⟩

theorem jdc_om_of (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (h : 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0) :
    g ∈ JF.Om k r z z' := by
  refine ⟨hg, ?_, h.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | h0
  · have e : l = ⟨0, by omega⟩ := Fin.ext h0
    rw [e]
    unfold Formalism.QuantumDeterminants.Dmin
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have e : l = ⟨((⟨l.val - 1, by omega⟩ : Fin r) : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact h.2 _

theorem jdc_of_om (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0 := by
  unfold JF.Om Q.OmPlus at hg
  obtain ⟨_, hD, hG⟩ := hg
  exact ⟨hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩

end gen

section gen2

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem jdc_ckOn_mono {m : ℕ∞} {UU VV : Set (B.Mat k r)} (h : UU ⊆ VV) {f : B.Mat k r → E₁} (hf : B.CkOn m VV f) :
    B.CkOn m UU f := by
  intro g₀ hg₀
  exact hf g₀ (h hg₀)

theorem jdc_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  unfold B.CkOn at *
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', hea⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hg₂, hΦ', heΦ⟩ := hΦ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have hr : ContDiffOn ℝ _ (fun g => (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ) (a' g)) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (ha'.mono Set.inter_subset_left)
    exact hr.clm_apply (hΦ'.mono Set.inter_subset_right)
  · intro g hg hgG
    simp only [hea g hg.1 hgG, heΦ g hg.2 hgG]

theorem jdc_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end gen2

section gen3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem jdc_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (jdc_ckOn_ap (h T (by simp)) (jdc_ckOn_Rw T.word_lie hJ))
      (jdc_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem jdc_ckOn_om (z z' : Fin (2 * r + k + 1) → ℂ) {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : Q.SmoothLev k r 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} J) :
    B.CkOn ⊤ (JF.Om k r z z') J := by
  unfold B.CkOn
  unfold Q.SmoothLev at hJ
  intro g₀ hg₀
  unfold JF.Om Q.OmPlus at hg₀
  obtain ⟨hgG, hD, hG⟩ := hg₀
  have hmem : g₀ ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    ⟨⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ g₀ hmem
  refine ⟨U, F, hU, hgU, hF, ?_⟩
  intro g hg hgV
  exact hJF g hg ⟨hgV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

variable [FiniteDimensional ℂ Wp]

theorem jdc_ffl (Db : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hSC : B.SmoothCoef (B.GPos Db) Θ)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (hH : ∀ g ∈ JF.Om k r Db.z Db.z', B.opApply Θ J g = B.JF Db H g) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := jdc_om_of _ _ hg₀.1.1 hg₀.2
    have hck := jdc_ckOn_opApply (jdc_ckOn_om Db.z Db.z' hJ.1) Θ
      (fun T hT => jdc_ckOn_mono (jdc_om_sub_gpos Db) (hSC T hT).1)
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hck g₀ hg₀O
    refine ⟨U ∩ Q.OmPlus k r Db.z Db.z', f', hU.inter (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _), ⟨hgU, hg₀O.2⟩,
      hc.mono Set.inter_subset_left, ?_⟩
    intro g hg hgG
    have hgO : g ∈ JF.Om k r Db.z Db.z' := ⟨hgG.1, hg.2⟩
    rw [← hH g hgO]
    exact he g hg.1 hgG.1
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

end gen3

theorem transfer_commutation_holds : JDJComm := by
  refine ⟨12, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d A hd hSC hC _hG hA F _hCk hCC hJF
  have hT := jdc_thrW (k := S.G.k) (r := S.G.r) (B.opOrder Θ) A d hd hA
  have hCOm : B.Commutes (T v).base (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') Θ :=
    fun p hp f' hf' g hg => hC p hp f' hf' g (jdc_om_sub_gpos _ hg)
  have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ (T v).base A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT (hCC _) hCOm
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨jdc_ffl (T v).base Θ hSC hJF _ hth, ?_⟩
  intro x hx
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  exact hth _ (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSplit
section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfIsHaarOn
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

end Formalism.FourierDecayAlt.P5
end
end

