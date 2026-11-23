module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0289
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0286
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0271
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpX
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0270
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralCompositionZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0288
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasHM

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRFibStable
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace FS

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ}

theorem stabilizer_fixes_first_vector (hz : inWb k r z) (hT : 0 < Tz k r z) {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.1 *ᵥ SSn.nu0 k r z z' μsec ζ = SSn.nu0 k r z z' μsec ζ := by
  obtain ⟨ha, hb, hab⟩ := hp
  have e : p.1 *ᵥ (NF.muZ k r μsec ζ *ᵥ z') = NF.muZ k r μsec ζ *ᵥ z' := by
    conv_rhs => rw [← hab, ← Matrix.mulVec_mulVec, hb.2.2, ← Matrix.mulVec_mulVec]
  unfold SSn.nu0 SSn.unitH
  rw [Matrix.mulVec_smul, ← TF.prWv_uw hz hT ha, e]

theorem nu0'_fix (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.2⁻¹ *ᵥ SSn.nu0' k r z z' μsec ζ = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨ha, hb, hab⟩ := hp
  have hai := P.LieBracketMultiplication.uw_inv ha
  have hbi := P.LieBracketMultiplication.uw_inv hb
  have h1 : (NF.muZ k r μsec ζ)⁻¹ = p.2⁻¹ * ((NF.muZ k r μsec ζ)⁻¹ * p.1⁻¹) := by
    conv_lhs => rw [← hab, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e : p.2⁻¹ *ᵥ ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) = (NF.muZ k r μsec ζ)⁻¹ *ᵥ z := by
    conv_rhs => rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hai.2.2]
  unfold SSn.nu0' SSn.unitH
  rw [Matrix.mulVec_smul, ← TF.prWv_uw hz' hT' hbi, e]

theorem nu0'_fix' (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.2 *ᵥ SSn.nu0' k r z z' μsec ζ = SSn.nu0' k r z z' μsec ζ := by
  conv_lhs => rw [← nu0'_fix hz' hT' hp, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hp.2.1.1), Matrix.one_mulVec]

theorem stabilizer_fixes_section_embedding (hz' : inWb k r z') (hT' : 0 < Tz k r z') {p : Q.Mx k r × Q.Mx k r}
    (hp : p ∈ NF.Stab k r z z' μsec ζ) :
    p.1 * SSn.io0 k r z z' μsec ζ * p.2 = SSn.io0 k r z z' μsec ζ := by
  have hν := nu0'_fix' hz' hT' hp
  obtain ⟨ha, hb, hab⟩ := hp
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ,
      (p.1 * SSn.io0 k r z z' μsec ζ * p.2) *ᵥ v = SSn.io0 k r z z' μsec ζ *ᵥ v := by
    intro v
    have hh : herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) =
        herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) := by
      calc herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ)
          = herm (Hpk k r) (p.2 *ᵥ SSn.prWv k r z' v) (p.2 *ᵥ SSn.nu0' k r z z' μsec ζ) := by rw [hν]
        _ = _ := P.Qx2.herm_uh hb.1 _ _
    have hk : SSn.prWv k r z' (p.2 *ᵥ v) -
          herm (Hpk k r) (SSn.prWv k r z' (p.2 *ᵥ v)) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ =
        p.2 *ᵥ (SSn.prWv k r z' v -
          herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
      rw [TF.prWv_uw hz' hT' hb, Matrix.mulVec_sub, Matrix.mulVec_smul, hν, hh]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, MC.DT.ioMulVec, MC.DT.ioMulVec, hk, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hab]
  exact Matrix.ext_of_mulVec_single fun i => key _

end FS

theorem fibre_stability_holds : FibStable := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk Pr hPr Bw Bw' hBw hBw' ζ hζ Xf hX ρ
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := Bs.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hx := hX p hp
    have e1 := hPr.2.1 p.1 hp.1 ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
    rw [FS.stabilizer_fixes_first_vector hz hT hp] at e1
    conv_rhs => rw [e1, ← hx]
    ext x
    simp only [ContinuousLinearMap.comp_apply, TF.rep_inv_cancel hR hp.1]
  · have hbi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hp.2.1
    have hbb : (p.2⁻¹)⁻¹ = p.2 := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hp.2.1.1)
    have e := TF.tht_eqv hz hT hR hz' hT' hR' hBw hBw' hp.1 hbi (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf
    rw [hbb, FS.stabilizer_fixes_first_vector hz hT hp, FS.nu0'_fix hz' hT' hp, FS.stabilizer_fixes_section_embedding hz' hT' hp, hX p hp] at e
    exact e.symm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHThtRot
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

namespace TR

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.P.TheSecStab

section block

variable {k : ℕ}

theorem img_perp_a {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ} (hxb : herm (Hb k) x b = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) a = 0 := by
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have hne' : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by
    rw [show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]; exact hne
  have h1 : herm (Hb k) (gB k b T' *ᵥ x) (Pi.single (Fin.last k) 1) = 0 := by
    rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right] at hxb
    exact (mul_eq_zero.1 hxb).resolve_left hne'
  have h2 := form_of_unitary (Hb k) (gA_spec k hT ha).1 (gB k b T' *ᵥ x)
    (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
  rw [(gA_spec k hT ha).2] at h2
  rw [h2, herm_smul_right, h1, mul_zero]

theorem img_perp_0 {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ}
    (hx0 : herm (Hb k) x ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) (gA k a T *ᵥ Pi.single 0 1) = 0 := by
  rw [form_of_unitary (Hb k) (gA_spec k hT ha).1, ← DC.gB_adj hT' hb]
  exact hx0

end block

section big

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem stabilizer_fixes_section_embedding (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) {h : Q.Mx k r}
    (hfix : ∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (DC.EE k r z) = 0 → h *ᵥ v = v) :
    h * SSn.io0 k r z z' (theSection k r z z') ζ = SSn.io0 k r z z' (theSection k r z z') ζ := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  rw [DC.section_embedding_eq_matrix hk hz hz' hT hT' hζ]
  ext i j
  obtain ⟨h1, h2, h3⟩ := DC.uu_facts (r := r) hk hz' hT' j
  have g2 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) (wbPart k r z') = 0 := by
    rw [← DC.herm_of h1 hz']; exact h2
  have g3 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) ((gB k (wbPart k r z') (Tz k r z'))⁻¹ *ᵥ Pi.single 0 1) = 0 := by
    rw [DC.EE', DC.herm_of h1 (inWb_jV _), wbPart_jV] at h3; exact h3
  have e := hfix (jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ (gB k (wbPart k r z') (Tz k r z') *ᵥ wbPart k r (DC.uu k r z' j))))
    (inWb_jV _)
    (by rw [DC.herm_of (inWb_jV _) hz, wbPart_jV]; exact img_perp_a hT hT' ha hb g2)
    (by rw [DC.EE, herm_jV]; exact img_perp_0 hT hT' ha hb g3)
  rw [Matrix.mul_apply]
  exact congrFun e i

end big

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
  {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem tht_iota_smul (F F' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) {ι ι' : B.Mat k r}
    (h : ∀ q, ι' *ᵥ F' q = u • (ι *ᵥ F' q)) : tht k r z z' π π' F F' a a' ι' = u • tht k r z z' π π' F F' a a' ι := by
  unfold tht
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h q, P.Qx8.herm_smul_left', smul_smul]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tht_rot (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    {h h' : B.Mat k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (u : ℂ) (hu : conj u * u = 1)
    {a a' : Fin (2 * r + k + 1) → ℂ} {ι : B.Mat k r} (ha : h *ᵥ a = u • a) (ha' : h' *ᵥ a' = u • a') (hι : h * ι = ι)
    (hsc : ∀ q, h' *ᵥ F' q = u • F' q) (X : Wq →L[ℂ] Wp) :
    (π h).comp ((tht k r z z' π π' F F' a a' ι X).comp (π' h')) =
      conj u • tht k r z z' π π' F F' a a' ι ((π h).comp (X.comp (π' h'))) := by
  have uh' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hinv : (h'⁻¹)⁻¹ = h' := Matrix.nonsing_inv_nonsing_inv _ uh'
  have e2 : h'⁻¹ *ᵥ a' = conj u • a' := by
    have e := congrArg (fun v => conj u • (h'⁻¹ *ᵥ v)) ha'
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uh', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, hu,
      one_smul] at e
    exact e.symm
  have e3 : ∀ q, (h * ι * h') *ᵥ F' q = u • (ι *ᵥ F' q) := by
    intro q
    rw [hι, ← Matrix.mulVec_mulVec, hsc q, Matrix.mulVec_smul]
  have key := TF.tht_eqv hz hT hR hz' hT' hR' hF hF' hh (P.LieBracketMultiplication.uw_inv hh') a a' ι X
  rw [hinv, ha, e2, TF.tht_phase hz hT hR hz' hT' hR' hF hF', tht_iota_smul F F' a a' u e3, smul_smul] at key
  rw [← key, FunLike.coe_smul, Pi.smul_apply]
  congr 1
  linear_combination (conj u) * hu

end gen

end TR

open Formalism.FourierDecayAlt.P.TheSec in
theorem theta_rotation_holds : ThtRot := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec Bw Bw' hBw hBw' θ h h' hh hh' ζ hζ hν hfix hsc Xf
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := hTe ▸ hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := hTe' ▸ hOK.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  have hk1 : 1 ≤ P.k := by omega
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTe, hTe']; exact hζ
  have hu : conj (PS.eM θ) * PS.eM θ = 1 := by
    rw [← Complex.star_def, PS.star_eM]; exact PS.expPlus_mul_expMinus θ
  have hcu : conj (PS.eM θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.star_def, PS.star_eM]; rfl
  rw [hsec] at hν hfix ⊢
  obtain ⟨hE, hEz, _⟩ := DC.EE'_facts (r := P.r) hk1 hz' hT'
  have hν' : h' *ᵥ SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      PS.eM θ • SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    rw [DC.nu0'_eq hk1 hz hz' hT hT' hζ', Matrix.mulVec_neg, smul_neg]
    exact congrArg Neg.neg (hsc _ hE hEz)
  have hι : h * SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    refine TR.stabilizer_fixes_section_embedding hk1 hz hz' hT hT' hζ' ?_
    rw [DC.section_first_vector_eq hk1 hz hz' hT hT' hζ'] at hfix
    exact hfix
  rw [← hcu]
  exact TR.tht_rot hz hT hR hz' hT' hR' hBw hBw' hh hh' (PS.eM θ) hu hν hν' hι
    (fun q => hsc _ (TF.frame_inW hBw' q).1 (TF.frame_inW hBw' q).2) Xf

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitPt
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def mk3 (k : ℕ) {n : ℕ} (v0 : Fin n → ℂ) (F : Fin (k - 1) → Fin n → ℂ) (zz : Fin n → ℂ) : Fin (k + 1) → Fin n → ℂ :=
  fun a => if h0 : a.val = 0 then v0 else if hk : a.val = k then zz else F ⟨a.val - 1, by have := a.isLt; omega⟩

theorem three_part_frame_zero {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h : a.val = 0) :
    mk3 k v0 F zz a = v0 := by
  unfold mk3; rw [dite_eq_left h]

theorem three_part_frame_last {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} (hk : 1 ≤ k) {a : Fin (k + 1)}
    (h : a.val = k) : mk3 k v0 F zz a = zz := by
  unfold mk3; rw [dite_eq_right (by omega), dite_eq_left h]

theorem three_part_frame_middle {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h0 : a.val ≠ 0)
    (hk : a.val ≠ k) : mk3 k v0 F zz a = F ⟨a.val - 1, by have := a.isLt; omega⟩ := by
  unfold mk3; rw [dite_eq_right h0, dite_eq_right hk]

theorem three_part_frame_orthonormal (hk : 2 ≤ k) {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hv0 : inWb k r v0) (hzz : inWb k r zz) (hF : ∀ j, inWb k r (F j))
    (h00 : herm (Hpk k r) v0 v0 = 1) (hzz1 : herm (Hpk k r) zz zz = -1) (h0z : herm (Hpk k r) v0 zz = 0)
    (hF0 : ∀ j, herm (Hpk k r) (F j) v0 = 0) (hFz : ∀ j, herm (Hpk k r) (F j) zz = 0)
    (hFF : ∀ i j, herm (Hpk k r) (F i) (F j) = if i = j then 1 else 0) : ONb k r (mk3 k v0 F zz) := by
  have hz0 : herm (Hpk k r) zz v0 = 0 := by rw [DU.hswap, h0z, map_zero]
  have h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0 := fun j => by rw [DU.hswap, hF0 j, map_zero]
  have hzF : ∀ j, herm (Hpk k r) zz (F j) = 0 := fun j => by rw [DU.hswap, hFz j, map_zero]
  constructor
  · intro a
    by_cases h0 : a.val = 0
    · rw [three_part_frame_zero h0]; exact hv0
    · by_cases hl : a.val = k
      · rw [three_part_frame_last (by omega) hl]; exact hzz
      · rw [three_part_frame_middle h0 hl]; exact hF _
  · intro a b
    by_cases ha0 : a.val = 0
    · rw [three_part_frame_zero ha0]
      by_cases hb0 : b.val = 0
      · rw [three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]
      · rw [if_neg (fun h => hb0 (by rw [← h]; exact ha0))]
        by_cases hbl : b.val = k
        · rw [three_part_frame_last (by omega) hbl, h0z]
        · rw [three_part_frame_middle hb0 hbl, h0F]
    · by_cases hal : a.val = k
      · rw [three_part_frame_last (by omega) hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]
          · rw [three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]
      · rw [three_part_frame_middle ha0 hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]
          · rw [three_part_frame_middle hb0 hbl, hFF]
            by_cases hab : a = b
            · subst hab; rw [if_pos rfl, if_pos rfl, if_neg hal]
            · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
              rw [if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem pt_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (SSn.nu0 k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) z = 0 ∧
    herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
    inWb k r (SSn.nu0' k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) z' = 0 ∧
    herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨h1, h2, h3, h4⟩ := DU.base hz hz' hT hT' hsec hζ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hνW : inWb k r (SSn.nu0 k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _
  refine ⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩
  · rw [← h1]; exact DU.prWv_perp hT hνW
  · rw [← h3]; exact DU.prWv_perp hT' hνW'

theorem mu_frame (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) :
    (∀ j, inWb k r (NF.muZ k r μsec ζ *ᵥ Fr j)) ∧
    (∀ i j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr i) (NF.muZ k r μsec ζ *ᵥ Fr j) = if i = j then 1 else 0) ∧
    (∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) z = 0) ∧
    ∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) (SSn.nu0 k r z z' μsec ζ) = 0 := by
  obtain ⟨-, -, hνν, -, -, -, hν'ν', -⟩ := pt_facts hz hz' hT hT' hsec hζ
  set μ := NF.muZ k r μsec ζ with hμ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hU : μ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (μ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r (μ⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0 := fun j => hFr.2.2 j z' (by simp)
  have hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 := fun j => hFr.2.2 j _ (by simp)

  have hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0 := by
    intro j
    rw [FrameEntries.herm_inv hU]
    set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ)
      with ht
    have hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z) := rfl
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hν', h0, zero_smul] at hν'ν'
      simp [herm] at hν'ν'
    have h1 := hFν' j
    rw [hν', DU.hsmul_r] at h1
    have h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0
      · exact h
    rw [DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero] at h2
    exact h2
  refine ⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩
  intro j
  set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)
  have hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z') := rfl
  rw [hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]
  simp

theorem frame'_exists (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr := by
  obtain ⟨-, -, -, -, hW', hz'0, h11, -⟩ := pt_facts hz hz' hT hT' hsec hζ
  exact Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11

end pt

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFHypS (Cb Cc : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) : Prop :=
  NFHyp Cb Cc p f A₀ p₀ χ N ∧ B.JF p.T.base f ∈ FFKB p ∧
    ∀ n : ℕ, B.JF p.T.base (fun g => cutN P.k P.r n g • f g) ∈ FFKB p

def NFJCutFF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ n : ℕ, B.JF p.T.base (fun g => cutN P.k P.r n g • f g) ∈ FFKB p

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_R : RDSOpR := rDSOpR_of_parts spectral_right_group_action spectral_operator_X spectral_right_rho_action spectral_composition_zero

theorem spectral_operator_R_adjoint : RDSOpRv := rDSOpRv_of_parts spectral_adjoint_right_group spectral_operator_X spectral_adjoint_rho_action spectral_composition_zero

theorem actual_compact_theorem : Formalism.FourierDecayAlt.P5.ThmPActualCpt := thmPActualCpt_of_R spectral_operator_R spectral_operator_R_adjoint

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SsnRepOfOpen2
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_open2 (hPE : PRho.PRhoExists) (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open hPE theta_facts_hold hMC hLN hPoly

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_Proof
section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem type_norm_measurability_holds : TDM.TypeNormMeas :=
  TNM.typeNormMeas_of_typeComm_houseMeas TNM.type_commutation_holds TNM.HM.householder_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP
end

