module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0198
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTransfer
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Tr

section datum

variable {k r : ℕ}

theorem unitH_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.unitH k r (h *ᵥ v) = h *ᵥ SSn.unitH k r v := by
  unfold SSn.unitH
  rw [Formalism.FourierDecayAlt.P.Qx2.herm_uh hh, Matrix.mulVec_smul]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μ μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ} {h h' : B.Mat k r}

theorem section_first_vector_transport (hz : inWb k r z) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.nu0 k r z z' μ ζ = h *ᵥ SSn.nu0 k r z z' μ0 ζ := by
  unfold SSn.nu0
  rw [hd, ← Matrix.mulVec_mulVec, hh'.2.2, ← Matrix.mulVec_mulVec, kap_prWv_mulVec hz hh, unitH_uh hh.1]

theorem nu0'_tr (hz' : inWb k r z') (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.nu0' k r z z' μ ζ = h'⁻¹ *ᵥ SSn.nu0' k r z z' μ0 ζ := by
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  unfold SSn.nu0'
  rw [hd, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hhi.2.2,
    kap_prWv_mulVec hz' hhi', unitH_uh hhi'.1]

theorem section_embedding_transport (hz' : inWb k r z') (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.io0 k r z z' μ ζ = h * SSn.io0 k r z z' μ0 ζ * h' := by
  apply Formalism.FourierDecayAlt.P.Qx8.mat_ext
  intro v
  set ν := SSn.nu0' k r z z' μ0 ζ with hν
  have e1 : h' *ᵥ (h'⁻¹ *ᵥ ν) = ν := by
    rw [Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mulVec]
  have e2 : ∀ w, herm (Hpk k r) (h' *ᵥ w) ν = herm (Hpk k r) w (h'⁻¹ *ᵥ ν) := by
    intro w
    conv_lhs => rw [← e1]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh'.1 _ _
  rw [MC.DT.ioMulVec, nu0'_tr hz' hh hh' hd, ← hν, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, MC.DT.ioMulVec, ← hν,
    kap_prWv_mulVec hz' hh', e2, hd, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, e1]

end datum

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem rep_inv_l {π : B.Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (y : Wp) : π h⁻¹ (π h y) = y := by
  have e : (π h⁻¹).comp (π h) = 1 := by
    rw [← hπ.2 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh) _ hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, hπ.1]
  exact congrArg (fun T : Wp →L[ℂ] Wp => T y) e

theorem rep_inv_r {π : B.Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (y : Wp) : π h (π h⁻¹ y) = y := by
  have e : (π h).comp (π h⁻¹) = 1 := by
    rw [← hπ.2 _ hh _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hπ.1]
  exact congrArg (fun T : Wp →L[ℂ] Wp => T y) e

end ops

section fib

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μ μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ}
  {h h' : B.Mat k r} {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem fib_tr (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π')
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') {Xf : Wq →L[ℂ] Wp} (hX : Xf ∈ NF.Fib k r z z' μ π π' ζ) :
    (π h⁻¹).comp (Xf.comp (π' h'⁻¹)) ∈ NF.Fib k r z z' μ0 π π' ζ := by
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hst : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μ ζ := by
    refine ⟨Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi,
      Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh', ?_⟩
    show h * p.1 * h⁻¹ * NF.muZ k r μ ζ * (h'⁻¹ * p.2 * h') = NF.muZ k r μ ζ
    rw [hd]
    calc h * p.1 * h⁻¹ * (h * NF.muZ k r μ0 ζ * h') * (h'⁻¹ * p.2 * h')
        = h * p.1 * (h⁻¹ * h) * NF.muZ k r μ0 ζ * (h' * h'⁻¹) * p.2 * h' := by simp only [Matrix.mul_assoc]
      _ = h * (p.1 * NF.muZ k r μ0 ζ * p.2) * h' := by
          rw [Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh']
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = h * NF.muZ k r μ0 ζ * h' := by rw [hp3]
  have hfix := hX _ hst
  apply ContinuousLinearMap.ext
  intro x
  have h1 := congrArg (fun T : Wq →L[ℂ] Wp => T (π' h'⁻¹ x)) hfix
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [hπ.2 _ (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) _ hhi, hπ.2 _ hh _ hp1,
    hπ'.2 _ (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) _ hh', hπ'.2 _ hhi' _ hp2] at h1
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [rep_inv_r hπ' hh'] at h1
  simp only [ContinuousLinearMap.comp_apply]
  rw [← h1, rep_inv_l hπ hh]

end fib

end Tr

open Tr in
theorem transfer_holds : Transfer := by
  intro hTF h0 Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl := hA.1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  have hdec : ∀ ζ : ℂ, ∃ hh : Q.Mx P.k P.r × Q.Mx P.k P.r, ζ ∈ Gauge.GC.Ann P →
      hh.1 ∈ UWset P.k P.r Bs.z ∧ hh.2 ∈ UWset P.k P.r Bs.z' ∧
        NF.muZ P.k P.r Bs.μsec ζ = hh.1 * NF.muZ P.k P.r μ0 ζ * hh.2 := by
    intro ζ
    by_cases hζ : ζ ∈ Gauge.GC.Ann P
    · have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
      have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
      obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
        hdom.2.1 hdom.2.2
      rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
      exact ⟨(h, h'), fun _ => ⟨hh, hh', he⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hζ⟩
  choose H hH using hdec
  let S0 : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun ζ =>
    (sandw (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)).comp ((S ζ).comp (sandw (Bs.π (H ζ).1) (Bs.π' (H ζ).2)))
  have hS0 : IsSSPt P Bs0 d l S0 := by
    intro Φ c hc ζ hζ
    obtain ⟨hh, hh', hd⟩ := hH ζ hζ
    set h := (H ζ).1 with hh_def
    set h' := (H ζ).2 with hh'_def
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
    have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
    have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
    have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
    have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
      rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    have hb1 : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r μ0 ζ) =
        (Bs.π h⁻¹).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
      rw [hback]
      exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'
    have hf : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
        (Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
      rw [hd]
      exact Φ.2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
    change (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp ((S ζ ((Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ)).comp
        (Bs.π' h')))).comp (Bs.π' h'⁻¹))
    rw [← hf, ← hS Φ c hc ζ hζ]
    exact hb1
  obtain ⟨n, q, hq⟩ := h0 Wp Wq P Bs0 rfl hk X d hA l hl S0 hS0 Pr hPr Bw Bw' hBw hBw' π ρ hUp
  refine ⟨n, q, fun ζ hζ Xf hXf hline => ?_⟩
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1 with hh_def
  set h' := (H ζ).2 with hh'_def
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  have hinv : h'⁻¹⁻¹ = h' := Matrix.nonsing_inv_nonsing_inv h' (WeylGroupFacts.isUnit_of_uh hh'.1)
  have eν := section_first_vector_transport (z' := Bs.z') hz hh hh' hd
  have eν' := nu0'_tr (z := Bs.z) hz' hh hh' hd
  have eι := section_embedding_transport (z := Bs.z) hz' hh hh' hd
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' μ0 ζ with hν
  set ν' := SSn.nu0' P.k P.r Bs.z Bs.z' μ0 ζ with hν'
  set ι := SSn.io0 P.k P.r Bs.z Bs.z' μ0 ζ with hι
  set Xf0 : Wq →L[ℂ] Wp := (Bs.π h⁻¹).comp (Xf.comp (Bs.π' h'⁻¹)) with hXf0
  have hXb : (Bs.π h).comp (Xf0.comp (Bs.π' h')) = Xf := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [hXf0, ContinuousLinearMap.comp_apply]
    rw [rep_inv_l Bs.π'_rep hh', rep_inv_r Bs.π_rep hh]
  have hmem0 : Xf0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := fib_tr Bs.π_rep Bs.π'_rep hh hh' hd hXf
  have hPrT : ∀ σ : M.Ty P, Pr σ (h *ᵥ ν) = (Bs.π h).comp ((Pr σ ν).comp (Bs.π h⁻¹)) := fun σ => hPr.2.1 h hh σ ν
  have hline0 : (Pr π ν).comp Xf0 = Xf0 := by
    rw [eν, hPrT] at hline
    apply ContinuousLinearMap.ext
    intro x
    have h1 := congrArg (fun T : Wq →L[ℂ] Wp => Bs.π h⁻¹ (T (Bs.π' h'⁻¹ x))) hline
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [rep_inv_l Bs.π_rep hh] at h1
    simp only [hXf0, ContinuousLinearMap.comp_apply]
    exact h1
  have hkey : (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ ν).comp (S0 ζ Xf0) =
      q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ ν).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' ν ν' ι Xf0) := hq ζ hζ Xf0 hmem0 hline0
  have hS0v : S0 ζ Xf0 = (Bs.π h⁻¹).comp ((S ζ Xf).comp (Bs.π' h'⁻¹)) := by
    change (Bs.π h⁻¹).comp ((S ζ ((Bs.π h).comp (Xf0.comp (Bs.π' h')))).comp (Bs.π' h'⁻¹)) = _
    rw [hXb]
  have hT := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h'⁻¹ hhi' ν ν' ι Xf0).1
  rw [hinv, hXb] at hT
  rw [eν, eν', eι, hT, hPrT]
  rw [hS0v] at hkey
  apply ContinuousLinearMap.ext
  intro x
  have h1 := congrArg (fun T : Wq →L[ℂ] Wp => Bs.π h (T (Bs.π' h' x))) hkey
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul] at h1
  rw [rep_inv_l Bs.π'_rep hh'] at h1
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply]
  rw [rep_inv_l Bs.π_rep hh]
  exact h1

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQOpen
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

theorem jAdjTrQQ_of_open (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) (h12 : JAGroupAdj) (h13 : JALocCC) :
    JAdjTrQQ :=
  jAdjTrQQ_of_leaves quadratic_assembly_holds h1 h7 h11 h12 h13 smooth_forms_stability_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_pairing_list_holds : SA.SAPairL :=
  SA.sAPairL_of_parts smooth_forms_stability_holds SA.self_adjoint_locality_holds (SA.sAExh_of_smooth SA.averaging_smoothness_holds) SA.self_adjoint_commutation_compact
    SA.compact_support_lemma_three

theorem star_operator_transfer_holds : JAStarOp := jAStarOp_of_pairL self_adjoint_pairing_list_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSStab
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

namespace DT

variable {k r : ℕ}

theorem eP_uw {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : B.Mat k r} (hg : g ∈ UWset k r z')
    (ν v : Fin (2 * r + k + 1) → ℂ) : eP k r z' (g *ᵥ ν) (g *ᵥ v) = g *ᵥ eP k r z' ν v := by
  unfold eP
  rw [kap_prWv_mulVec hz' hg, Qx2.herm_uh hg.1, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem decomp (z' ν v : Fin (2 * r + k + 1) → ℂ) :
    ∃ (o : Fin (2 * r + k + 1) → ℂ) (α β : ℂ), (∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) ∧
      v = eP k r z' ν v + o + α • z' + β • ν := by
  refine ⟨v - SSn.wbP k r v, -(herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)),
    herm (Hpk k r) (SSn.prWv k r z' v) ν, ?_, ?_⟩
  · intro i h1 h2
    simp [SSn.wbP, h1, h2]
  · have hP : SSn.prWv k r z' v =
        SSn.wbP k r v + (herm (Hpk k r) (SSn.wbP k r v) z' / (Tz k r z' : ℂ)) • z' := rfl
    unfold eP
    generalize herm (Hpk k r) (SSn.prWv k r z' v) ν = β
    rw [hP, neg_smul]
    abel

theorem fixOut {g : B.Mat k r}
    (hg : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    {o : Fin (2 * r + k + 1) → ℂ} (ho : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → o i = 0) :
    g *ᵥ o = o := by
  have hcol : ∀ j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) →
      g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j hj
    rcases hj with hj | hj
    · have h1 := (hg ⟨j.val, hj⟩).1
      have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
      rw [e] at h1
      exact h1
    · have hlt : 2 * r + k - j.val < r := by omega
      have h1 := (hg ⟨2 * r + k - j.val, hlt⟩).2
      have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := Fin.ext (by simp only [esI]; omega)
      rw [e] at h1
      exact h1
  have hent : ∀ i j : Fin (2 * r + k + 1), (g *ᵥ Pi.single j 1) i = g i j := by
    intro i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ j, g i j * o j = ∑ j, (if j = i then o i else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
        · rw [ho j hj.1 hj.2, mul_zero]
          split_ifs with hji
          · rw [← hji, ho j hj.1 hj.2]
          · rfl
        · rw [← hent i j, hcol j (by omega), Pi.single_apply]
          split_ifs with hij hji hji
          · rw [one_mul, hij]
          · exact absurd hij.symm hji
          · exact absurd hji.symm hij
          · rw [zero_mul]
    _ = o i := by simp

theorem core {z z' ν₁ ν₂ ν₁' ν₂' : Fin (2 * r + k + 1) → ℂ} {μ₁ μ₂ h h' a b : B.Mat k r}
    (hz' : inWb k r z') (hμ₁ : μ₁ ∈ Q.Glev k r (Fin.last r)) (hμ₂ : μ₂ ∈ Q.Glev k r (Fin.last r))
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z')
    (hab : a * μ₂ * b = μ₂) (e1 : h *ᵥ ν₁ = ν₂) (e2 : h' *ᵥ ν₁' = ν₂')
    (e3 : ∀ v, h *ᵥ (μ₁ *ᵥ eP k r z' ν₁' (h'⁻¹ *ᵥ v)) = μ₂ *ᵥ eP k r z' ν₂' v)
    {s₁ c₁ s₂ c₂ s₁' c₁' s₂' c₂' : ℂ} (hs₁ : s₁ ≠ 0)
    (f1 : ν₁ = s₁ • (μ₁ *ᵥ z' + c₁ • z)) (f2 : ν₂ = s₂ • (μ₂ *ᵥ z' + c₂ • z))
    (f1' : ν₁' = s₁' • (μ₁⁻¹ *ᵥ z + c₁' • z')) (f2' : ν₂' = s₂' • (μ₂⁻¹ *ᵥ z + c₂' • z')) :
    h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = μ₁ := by
  have hai : a⁻¹ * a = 1 := NFRadRedS.uw_inv_mul ha
  have hhi : h⁻¹ * h = 1 := NFRadRedS.uw_inv_mul hh
  have hh'i : h'⁻¹ * h' = 1 := NFRadRedS.uw_inv_mul hh'
  have hμ₂i : μ₂⁻¹ * μ₂ = 1 := FrameEntries.inv_mul_uh hμ₂.1
  have hμ₂m : μ₂ * μ₂⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₂.1
  have hμ₁m : μ₁ * μ₁⁻¹ = 1 := FrameEntries.mul_inv_uh hμ₁.1
  have hi' : h'⁻¹ ∈ UWset k r z' := LieBracketMultiplication.uw_inv hh'
  have A0 : a *ᵥ (μ₂ *ᵥ z') = μ₂ *ᵥ z' := by
    have h1 : (a * μ₂ * b) *ᵥ z' = μ₂ *ᵥ z' := by rw [hab]
    rwa [← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec] at h1
  have A : a *ᵥ ν₂ = ν₂ := by
    rw [f2, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, A0, ha.2.2]
  have B0 : b *ᵥ (μ₂⁻¹ *ᵥ z) = μ₂⁻¹ *ᵥ z := by
    have h1 : b * μ₂⁻¹ = μ₂⁻¹ * a⁻¹ := by
      calc b * μ₂⁻¹ = μ₂⁻¹ * (a⁻¹ * a) * μ₂ * b * μ₂⁻¹ := by
            rw [hai, Matrix.mul_one, hμ₂i, Matrix.one_mul]
        _ = μ₂⁻¹ * a⁻¹ * (a * μ₂ * b) * μ₂⁻¹ := by simp only [Matrix.mul_assoc]
        _ = μ₂⁻¹ * a⁻¹ := by rw [hab, Matrix.mul_assoc, hμ₂m, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, (LieBracketMultiplication.uw_inv ha).2.2]
  have B : b *ᵥ ν₂' = ν₂' := by
    rw [f2', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, B0, hb.2.2]
  have e2i : h'⁻¹ *ᵥ ν₂' = ν₁' := by
    rw [← e2, Matrix.mulVec_mulVec, hh'i, Matrix.one_mulVec]
  have C1 : ∀ v, h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) = μ₂ *ᵥ eP k r z' ν₂' v := by
    intro v
    rw [← eP_uw hz' hi', e2i]
    exact e3 v
  have Z0 : μ₁ *ᵥ z' = s₁⁻¹ • ν₁ - c₁ • z := by
    rw [f1, smul_smul, inv_mul_cancel₀ hs₁, one_smul, add_sub_cancel_right]
  have Z1 : h *ᵥ (μ₁ *ᵥ z') = s₁⁻¹ • ν₂ - c₁ • z := by
    rw [Z0, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, hh.2.2]
  have Z2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ z')) = h *ᵥ (μ₁ *ᵥ z') := by
    rw [Z1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, A, ha.2.2]
  have V0 : μ₁ *ᵥ ν₁' = s₁' • (z + c₁' • (μ₁ *ᵥ z')) := by
    rw [f1', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hμ₁m,
      Matrix.one_mulVec]
  have V1 : h *ᵥ (μ₁ *ᵥ ν₁') = s₁' • (z + c₁' • (h *ᵥ (μ₁ *ᵥ z'))) := by
    rw [V0, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh.2.2]
  have V2 : a *ᵥ (h *ᵥ (μ₁ *ᵥ ν₁')) = h *ᵥ (μ₁ *ᵥ ν₁') := by
    rw [V1, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ha.2.2, Z2]
  have key : ∀ v, a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ v)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ v)) := by
    intro v
    obtain ⟨o, α, β, ho, hv⟩ := decomp z' ν₂' v
    have E : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ eP k r z' ν₂' v)))) =
        h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ eP k r z' ν₂' v)) := by
      have h1 : b *ᵥ eP k r z' ν₂' v = eP k r z' ν₂' (b *ᵥ v) := by
        rw [← eP_uw hz' hb, B]
      rw [h1, C1, C1, ← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hab]
    have O : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ o)))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ o)) := by
      rw [fixOut hb.2.1 ho, fixOut hi'.2.1 ho, fixOut (fun c => hμ₁.2 c (by simp)) ho, fixOut hh.2.1 ho,
        fixOut ha.2.1 ho]
    have Zc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ z')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ z')) := by
      rw [hb.2.2, hi'.2.2, Z2]
    have Vc : a *ᵥ (h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ (b *ᵥ ν₂')))) = h *ᵥ (μ₁ *ᵥ (h'⁻¹ *ᵥ ν₂')) := by
      rw [B, e2i, V2]
    generalize eP k r z' ν₂' v = u at hv E
    subst hv
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [E, O, Zc, Vc]
  have M : a * (h * μ₁ * h'⁻¹) * b = h * μ₁ * h'⁻¹ := by
    have h1 : ∀ v, (a * (h * μ₁ * h'⁻¹) * b) *ᵥ v = (h * μ₁ * h'⁻¹) *ᵥ v := by
      intro v
      simp only [← Matrix.mulVec_mulVec]
      exact key v
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact h1 v)
  calc h⁻¹ * a * h * μ₁ * (h'⁻¹ * b * h') = h⁻¹ * (a * (h * μ₁ * h'⁻¹) * b) * h' := by
        simp only [Matrix.mul_assoc]
    _ = h⁻¹ * (h * μ₁ * h'⁻¹) * h' := by rw [M]
    _ = (h⁻¹ * h) * μ₁ * (h'⁻¹ * h') := by simp only [Matrix.mul_assoc]
    _ = μ₁ := by rw [hhi, hh'i, Matrix.one_mul, Matrix.mul_one]

theorem herm_zero_zero : herm (Hpk k r) 0 0 = 0 := by
  simp [herm]

theorem first_vector_normal_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, s ≠ 0 ∧ SSn.nu0 k r z z' μsec ζ = s • (NF.muZ k r μsec ζ *ᵥ z' + c • z) := by
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hb := (DU.base hz hz' hT hT' hsec hζ).2.1
  have e : SSn.nu0 k r z z' μsec ζ =
      (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ) • SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z') := rfl
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))
        (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z / (Tz k r z : ℂ), ?_, ?_⟩
  · intro h0
    rw [e, h0, zero_smul, herm_zero_zero] at hb
    exact zero_ne_one hb
  · rw [← DU.prWv_of hy]
    exact e

theorem nu0'_form {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ s c : ℂ, SSn.nu0' k r z z' μsec ζ = s • ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z + c • z') := by
  have hG := FrameEntries.glev_inv (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ))
  have hy : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hG hz
  refine ⟨(((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))
        (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ),
    herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' / (Tz k r z' : ℂ), ?_⟩
  rw [← DU.prWv_of hy]
  rfl

end DT

theorem datum_transit_stabilizer : DTStab := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3 p hp
  obtain ⟨ha, hb, hab⟩ := hp
  refine ⟨LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh) ha) hh, LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_inv hh') hb) hh', ?_⟩
  obtain ⟨s₁, c₁, hs₁, f1⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₁
  obtain ⟨s₂, c₂, -, f2⟩ := DT.first_vector_normal_form hz hz' hT hT' hsec h₂
  obtain ⟨s₁', c₁', f1'⟩ := DT.nu0'_form (z' := z') hz hsec h₁
  obtain ⟨s₂', c₂', f2'⟩ := DT.nu0'_form (z' := z') hz hsec h₂
  have e3' : ∀ v, h *ᵥ (NF.muZ k r μsec ζ₁ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₁) (h'⁻¹ *ᵥ v)) =
      NF.muZ k r μsec ζ₂ *ᵥ DT.eP k r z' (SSn.nu0' k r z z' μsec ζ₂) v := by
    intro v
    have h3 : (h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹) *ᵥ v = SSn.io0 k r z z' μsec ζ₂ *ᵥ v := by rw [e3]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, DT.ioMulVec, DT.ioMulVec] at h3
    exact h3
  exact DT.core hz' (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₁)) (NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec h₂))
    hh hh' ha hb hab e1 e2 e3' hs₁ f1 f2 f1' f2'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

