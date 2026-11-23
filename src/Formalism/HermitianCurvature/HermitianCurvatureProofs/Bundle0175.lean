module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

open Asm in
theorem polynomial_radial_base_holds : PolynomialRadialAtSectionOfPhaseInvariance := by
  intro hD hK hF hA hC hP hE hW Wp Wq _ _ _ _ _ _ P Bs hsec hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hAct' := hAct
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hAct'
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hsec] at hcs
  have hAnn : ∀ ζ ∈ Gauge.GC.Ann P, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ :=
    fun ζ hζ => by rw [hTz]; exact hζ
  set ζ₁ : ℂ := ((P.TT + 1 : ℝ) : ℂ) with hζ₁def
  have hζ₁ : ζ₁ ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ζ₁
    rw [hζ₁def, Complex.normSq_ofReal]; nlinarith
  have hDc : ∀ ζ ∈ Gauge.GC.Ann P,
      SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ ∧
      SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ ∧
      SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ := by
    intro ζ hζ
    rw [hsec]
    exact hD P.k P.r Bs.z Bs.z' (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)
  have hFc : ∀ ζ ∈ Gauge.GC.Ann P,
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)]
  obtain ⟨Qr, hKP, hKL⟩ := hK Wp Wq P Bs hsec hk X d hAct Pr hPr
  have hGT : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hSt, hRel, hQQ⟩
  have hLine := Gauge.GC.gauge_kappa_line_holds Wp Wq P Bs X d hGT Qr hKP ζ₁ hζ₁
  obtain ⟨Eπ, hEπF, hEπQ, hEπn, hEπsp⟩ := hLine π
  obtain ⟨Eρ, hEρF, hEρQ, hEρn, hEρsp⟩ := hLine ρ
  have hQQr : ∀ σ, (Qr σ).comp (Qr σ) = Qr σ := fun σ => by rw [hKP.1 σ σ, if_pos rfl]

  have hval : ∀ (Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r →
      ∀ ζ ∈ Gauge.GC.Ann P, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro Ψ c hc ζ hζ p hp
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
    have h1 := Ψ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom p.1 hp.1 p.2 hp.2.1
    simp only at h1
    rw [hp.2.2] at h1
    exact h1.symm
  have hEπne : Eπ ≠ 0 := by
    intro h0
    rw [h0] at hEπn
    have : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq)).map_zero
    rw [this, inner_zero_left] at hEπn
    exact zero_ne_one hEπn
  have hEπFa : ∀ ζ ∈ Gauge.GC.Ann P, Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun ζ hζ => (hFc ζ hζ).symm ▸ hEπF
  have hPπ : ∀ ζ ∈ Gauge.GC.Ann P, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Eπ = Eπ :=
    fun ζ hζ => by rw [hKL ζ hζ Eπ (hEπFa ζ hζ) π, hEπQ]

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := Gauge.GC.radBase_of P Bs hpl
  have hsecπ : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun _ : (Fin P.r → ℂ) × ℂ => Eπ) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨(contDiffOn_const (c := Eπ)).congr fun q hq => by simp [Set.indicator_of_mem hq], fun q hq => ?_,
      fun q hq => by simp [Set.indicator_of_notMem hq]⟩
    rw [Set.indicator_of_mem hq]
    exact hEπFa q.2 (by show P.TT < _; rw [← hTz]; exact hq.2)
  obtain ⟨Φ0, hΦ0, hΦr⟩ :=
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsecπ
  let Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ0, hΦ0⟩
  have hΦ : ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = Eπ := by
    intro c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    have h := congrFun hΦr (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hsum : ∀ σ : M.Ty P, (∑ τ, (Pi.single σ (1 : ℂ) : M.Ty P → ℂ) τ • Qr τ) = Qr σ := by
    intro σ
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (fun h => absurd (Finset.mem_univ σ) h)]
    simp
  have hKπ : (d.κ (Pi.single π 1)).1 Φ = Φ := by
    apply Subtype.ext
    refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ (Pi.single π 1)).1 Φ).2 _ Φ.2 (funext fun q => ?_)
    by_cases hq : q ∈ NF.QR P.k P.r Bs.z Bs.z'
    · simp only [NF.radR, Set.indicator_of_mem hq]
      have hqA : q.2 ∈ Gauge.GC.Ann P := by show P.TT < _; rw [← hTz]; exact hq.2
      have h1 := hKP.2.2.2 (Pi.single π 1) Φ ⟨(q.1, q.2), hq.1, hqA⟩
      simp only at h1
      rw [h1, hsum, hΦ q.1 hq.1 q.2 hqA, hEπQ]
    · simp only [NF.radR, Set.indicator_of_notMem hq]

  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, M.xEx P {l} π Y ≠ 0 := by
    refine ⟨((1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| : ℝ) : ℂ), ?_⟩
    unfold M.xEx
    rw [Finset.prod_ne_zero_iff]
    intro i hi h0
    have h2 := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h2
    have hle : |M.rho P π i| ≤ ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P π j| :=
      Finset.single_le_sum (f := fun j => |M.rho P π j|) (fun j _ => abs_nonneg _) (Finset.mem_sdiff.1 hi).1
    linarith [neg_abs_le (M.rho P π i)]

  have hAlg := hA P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) d hRel l hl π ρ hUp Y
  have hAlg1 : (d.κ (Pi.single ρ 1)).1 (X.t Y 1 0 Φ) = M.xEx P {l} π Y • (d.SS l).1 Φ := by
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ) hAlg
    rw [← hQQ Y] at h
    change ((d.κ (Pi.single ρ 1)).1 * (X.t Y 1 0) * (d.κ (Pi.single π 1)).1) Φ =
      (algebraMap ℂ (Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (M.xEx P {l} π Y) *
        ((d.SS l).1 * (d.κ (Pi.single π 1)).1)) Φ at h
    simp only [Module.End.mul_apply, Module.algebraMap_end_apply] at h
    rw [hKπ] at h
    exact h
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hPt : ∀ ζ ∈ Gauge.GC.Ann P, M.xEx P {l} π Y • S ζ Eπ =
      (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0)
        (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
    intro ζ hζ
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, hAnn ζ hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
    have e1 := congrArg (fun Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)) hAlg1
    have h1 := hKP.2.2.2 (Pi.single ρ 1) (X.t Y 1 0 Φ) ⟨(c0, ζ), hc0, hζ⟩
    simp only at h1 e1
    rw [h1, hsum, X.t_apply Y 1 0 Φ (c0, NF.muZ P.k P.r Bs.μsec ζ) hdom, Submodule.coe_smul] at e1
    simp only [Pi.smul_apply] at e1
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ] at e1
    exact e1.symm

  have hSF : ∀ ζ ∈ Gauge.GC.Ann P, S ζ Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro ζ hζ
    have h := hval ((d.SS l).1 Φ) c0 hc0 ζ hζ
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ] at h
    exact h
  have hW1 : ∀ ζ ∈ Gauge.GC.Ann P, (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) =
      (M.xEx P {l} π Y)⁻¹ • (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0)
        (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
    intro ζ hζ
    rw [hKL ζ hζ _ (hSF ζ hζ) ρ]
    have h := hPt ζ hζ
    have h2 : S ζ Eπ = (M.xEx P {l} π Y)⁻¹ • (Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0) (NF.muZ P.k P.r Bs.μsec ζ)).comp (Qr ρ) := by
      rw [← h, smul_smul, inv_mul_cancel₀ hY, one_smul]
    rw [h2, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hQQr]

  have hWline : ∀ ζ ∈ Gauge.GC.Ann P, (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) =
      inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ))) • Eρ := by
    intro ζ hζ
    have hWF := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ hζ _ (hSF ζ hζ) ρ).1
    refine hEρsp _ (hFc ζ hζ ▸ hWF) ?_
    rw [hKL ζ hζ _ (hSF ζ hζ) ρ, ContinuousLinearMap.comp_assoc, hQQr]

  let F : ℂ → ℂ := fun ζ =>
    inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ)))
  have hCP := hC Wp Wq P Bs hpl hk hsec Φ Eπ hΦ c0 hc0 Y
  let Lf : (Wq →L[ℂ] Wp) →ₗ[ℂ] ℂ := (M.xEx P {l} π Y)⁻¹ •
    ((innerₛₗ ℂ (B.hsVec Eρ)).comp ((Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Qr ρ)).toLinearMap))
  have hFPS : PS P.TT F := by
    refine PS.congr (PSV.apply hCP Lf) fun ζ hζ => ?_
    show inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ))) = _
    rw [hW1 ζ hζ]
    simp only [Lf, LinearMap.smul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]
    change inner ℂ (B.hsVec Eρ) (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq) ((M.xEx P {l} π Y)⁻¹ • _)) = _
    rw [map_smul, inner_smul_right]
    rfl

  obtain ⟨T1, hT1def⟩ : ∃ T : Wq →L[ℂ] Wp, T = (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁)).comp
      (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁)
        (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ₁) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁) Eπ) := ⟨_, rfl⟩
  have hT1ne : T1 ≠ 0 := by
    rw [hT1def]
    exact hW Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' l hl π ρ hUp ζ₁ hζ₁ Eπ hEπF (hPπ ζ₁ hζ₁) hEπne
  have hThtF := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ Eπ hEπF ρ).2
  have hT1F := (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ _ hThtF ρ).1
  have hT1line : T1 = inner ℂ (B.hsVec Eρ) (B.hsVec T1) • Eρ := by
    rw [hT1def]
    refine hEρsp _ hT1F ?_
    rw [hKL ζ₁ hζ₁ _ hThtF ρ, ContinuousLinearMap.comp_assoc, hQQr]
  obtain ⟨t0, ht0def⟩ : ∃ t : ℂ, t = inner ℂ (B.hsVec Eρ) (B.hsVec T1) := ⟨_, rfl⟩
  rw [← ht0def] at hT1line
  have ht0 : t0 ≠ 0 := by
    intro h0; apply hT1ne; rw [hT1line, h0, zero_smul]

  have hrotA : ∀ θ : ℝ, ∀ ζ ∈ Gauge.GC.Ann P, rot θ ζ ∈ Gauge.GC.Ann P := by
    intro θ ζ hζ
    show P.TT < Complex.normSq (rot θ ζ)
    have h1 : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
    rw [rot, Complex.normSq_mul, h1, one_mul]; exact hζ
  have hFinv : ∀ θ : ℝ, ∀ ζ : ℂ, P.TT < Complex.normSq ζ → F (rot θ ζ) = F ζ := by
    intro θ ζ hζ
    obtain ⟨c, hc⟩ := hP Wp Wq P Bs hsec hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp θ
    have hc1 : c = 1 := by
      have h := (hc ζ₁ hζ₁ Eπ hEπF (hPπ ζ₁ hζ₁)).2
      obtain ⟨e1, e2, e3⟩ := hDc (rot θ ζ₁) (hrotA θ ζ₁ hζ₁)
      rw [e1, e2, e3, ← hT1def] at h
      have h' : (1 - c) • T1 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact (sub_eq_zero.1 h'').symm
      · exact absurd h'' hT1ne
    have h := (hc ζ hζ Eπ (hEπFa ζ hζ) (hPπ ζ hζ)).1
    rw [hc1, one_smul] at h
    show inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp
      (S (rot θ ζ) Eπ))) = inner ℂ (B.hsVec Eρ) (B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
      (S ζ Eπ)))
    rw [h]
  obtain ⟨m, q, hq⟩ := hE P.TT F hTT hFPS hFinv
  refine ⟨m, Polynomial.C t0⁻¹ * q, fun ζ hζ Xf hXf hXπ => ?_⟩
  have hXF1 : Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := hFc ζ hζ ▸ hXf
  have hXQ : Xf.comp (Qr π) = Xf := by rw [← hKL ζ hζ Xf hXf π, hXπ]
  obtain ⟨x, hXe⟩ : ∃ x : ℂ, Xf = x • Eπ := ⟨_, hEπsp Xf hXF1 hXQ⟩
  subst hXe
  have hW' : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Eπ) = F ζ • Eρ := hWline ζ hζ
  obtain ⟨e1, e2, e3⟩ := hDc ζ hζ
  rw [map_smul, map_smul, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, hW', e1, e2, e3,
    ← hT1def, hT1line]
  simp only [smul_smul, Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  have hq' := hq ζ hζ
  simp only [gg, sig] at hq'
  have hinv : t0⁻¹ * t0 = 1 := inv_mul_cancel₀ ht0
  rw [mul_left_comm, hq']
  linear_combination (-(q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) * x)) * hinv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExh
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section eqv

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem psi_star_mul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : B.Mat k r) :
    star (psi k r z c x) * psi k r z c x = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (Complex.I * (((c * ell k r z x).re : ℝ) : ℂ)) +
      Complex.I * (((c * ell k r z x).re : ℝ) : ℂ) = 0 := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [h, Complex.exp_zero]

def oneP : B.SS k r := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), (1 : B.Mat k r)))

theorem oneP_inSS (D : B.RealPlaceData k r Wp Wq) : D.inSS oneP :=
  ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one⟩

theorem sgs_oneP (g : B.Mat k r) : B.sgs oneP g = g := by
  show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * g * 1 * 1 = g
  simp

theorem eqv_of_FFl (D : B.RealPlaceData k r Wp Wq) (X : B.Mat k r → (Wq →L[ℂ] Wp))
    (hX : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z'))
    {p : B.SS k r} (hp : D.inSS p) {y : B.Mat k r} (hy : y ∈ JF.Om k r D.z D.z') :
    JF.xiP D p • B.rho D p X y = X y := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hnN : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv h2
  have mem : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hg.1, hg.2⟩
  have nlev : ∀ m ∈ Nset k r, m ∈ Q.Nlev k r 0 := fun m hm => ⟨hm, (Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 m).2 hm.1⟩
  have hyn : y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)) y =
        y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  have hnyn : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h2, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)) y =
        (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  obtain ⟨_, hL, hR, hU⟩ := hX
  have e1 : X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) =
      (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) • X y := by
    rw [Matrix.mul_assoc, hL _ (mem _ hyn) _ (nlev _ hnN), hR _ (mem _ hy) _ (nlev _ h4), smul_smul]
  have e2 : X ((Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) *
      (Matrix.of p.2.1 : B.Mat k r)) =
      (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹).comp ((X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
        (Matrix.of p.2.2 : B.Mat k r))).comp (D.π' (Matrix.of p.2.1 : B.Mat k r))) :=
    hU _ (mem _ hnyn) _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3
  have hsgs : B.sgs p y = (Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
      (Matrix.of p.2.2 : B.Mat k r)) * (Matrix.of p.2.1 : B.Mat k r) := by
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) *
      (Matrix.of p.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  have hπ : ∀ w, D.π (Matrix.of p.1.1 : B.Mat k r) (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π_rep.2 _ h1 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1)
    rw [Matrix.mul_nonsing_inv _ hu1, D.π_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hπ' : ∀ w, D.π' (Matrix.of p.2.1 : B.Mat k r) (D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π'_rep.2 _ h3 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h3)
    rw [Matrix.mul_nonsing_inv _ hu3, D.π'_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hc : JF.xiP D p * (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ *
      psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) = 1 := by
    unfold JF.xiP
    have a1 := BesselUnipotentEquiv.star_psi_inv D.z cStd D.z_mem _ h2
    have a2 := psi_star_mul D.z cStd ((Matrix.of p.1.2 : B.Mat k r)⁻¹)
    have a3 := psi_star_mul D.z' cStd (Matrix.of p.2.2 : B.Mat k r)
    rw [a1] at a2
    calc psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) *
          (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r))
        = (psi k r D.z cStd (Matrix.of p.1.2) * psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹) *
          (star (psi k r D.z' cStd (Matrix.of p.2.2)) * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) := by ring
      _ = 1 := by rw [a2, a3, one_mul]
  unfold B.rho
  rw [hsgs, e2, e1]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, hπ', hπ, smul_smul, hc, one_smul]

end eqv

theorem sAExh_of_avgCutoff (hA : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff) : SAExh := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v X hX Cs hCs hCsQ
  set Db := (T v).base with hDb
  have hplace : Q.IsPlace (D.parOf S v) Db.z Db.z' Db.π Db.π' := (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hX' : X ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (Q.OmPlus S.G.k S.G.r Db.z Db.z') := by
    have := hX
    unfold smoothFormsPositiveCone at this
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v] at this
  obtain ⟨K', hK'c, hCsK', hK'Q⟩ := exists_compact_between hCs (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open Db.z Db.z')
    (fun x hx => hQ x (hCsQ hx))
  obtain ⟨φ, hφ, ⟨C, hCc, hCO, hCφ⟩, hint⟩ := hA S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C := by
    refine closure_minimal (fun g hg => ?_) hCc.isClosed
    by_contra hgC
    exact hg (by simp [hCφ g hgC])
  refine ⟨fun g => φ g • X g, interior K', isOpen_interior, hCsK', ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus S.G.k S.G.r Db.z Db.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, fun h => hO (hCO h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hCφ g hg]
  · exact hCc.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
    exact fun g hg => (hCO (hsuppC hg)).2
  · intro y hy
    have hgy : B.gq Db y ∈ JF.Om S.G.k S.G.r Db.z Db.z' :=
      Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db y (hQ y hy)
    have hJ : B.JF Db (fun g => φ g • X g) (B.gq Db y) =
        (∫ p, φ (B.sgs p (B.gq Db y)) ∂Db.μSS) • X (B.gq Db y) := by
      change ∫ p, JF.xiP Db p • B.rho Db p (fun g => φ g • X g) (B.gq Db y) ∂Db.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Db] with p hp
      have hr : B.rho Db p (fun g => φ g • X g) (B.gq Db y) =
          φ (B.sgs p (B.gq Db y)) • B.rho Db p X (B.gq Db y) := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, eqv_of_FFl Db X hX' hp hgy]
    refine ⟨fun hyU => ?_, fun h0 => ?_⟩
    · have h1 := hint oneP (oneP_inSS Db) y (interior_subset hyU)
      simp only [sgs_oneP] at h1
      rw [hJ, h1, one_smul]
    · rw [hJ, h0, smul_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

theorem sec_at (hR : SARadSec) (hD : SADescend) (hC : SACover)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (U : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ K ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'), Gauge.trJB P Bs e K = U := by
  obtain ⟨Φ, hΦ, hval⟩ := hR Wp Wq P Bs hpl e he U
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ := hD Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem Φ hΦ
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r Bs.z Bs.z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ := hC P.k P.r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  refine ⟨K, ?_, ?_⟩
  · obtain ⟨hs, hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  · funext ρ
    have hraw : Gauge.rawJ P Bs e K ρ = (U ρ : MA.Qp P.r P.TT → ℂ) := by
      funext q
      have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
        rw [Gauge.GC.SSTr.tz_eq P Bs hpl]; exact q.2.2
      have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
        Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
      have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
        unfold Q.GGl
        rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
        linarith
      have hζ' : P.TT < Complex.normSq q.1.2 := q.2.2
      have horth := (he.2 q.1.2 hζ').2.1
      have hwpos : 0 < Real.sqrt (MA.wq P.k q.1 P.TT) := Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos q.2)
      have hw : ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      simp only [Gauge.rawJ]
      rw [Gauge.tc_gq, (hKv q.1.1 q.2.1 _ hG hGG).2, hval q, Gauge.tc_hsVec_smul, inner_smul_right,
        Gauge.tc_hsVec_sum, inner_sum]
      simp only [Gauge.tc_hsVec_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      push_cast
      field_simp
    show MA.toSm P (Gauge.rawJ P Bs e K ρ) = U ρ
    have hm : Gauge.rawJ P Bs e K ρ ∈ MA.smSub P.r P.TT := by rw [hraw]; exact (U ρ).2
    rw [Gauge.toSm_of_mem P hm]
    apply Subtype.ext
    exact hraw

theorem sASection_of_parts (hR : SARadSec) (hD : SADescend) (hC : SACover) : SASection := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he U _
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨K, hK, hKU⟩ := sec_at hR hD hC (D.parOf S v) (T v).base hpl e he U
  refine ⟨K, ?_, hKU⟩
  show K ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
  exact hK

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

