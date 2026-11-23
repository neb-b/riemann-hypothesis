module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoAssembly
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0290
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0285
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2TruncationBoundHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0291

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem rho_projection_existence : PRho.PRhoExists :=
  PRhoCut.pRhoExists_of_cut PRhoCut.rho_projection_assembly PRhoCut.frame_locality_holds PRhoCut.capacity_smoothness_holds
    PRhoCut.eigenvector_orthogonality_holds PRhoCut.lagrange_annihilation

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitExists
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

theorem frame_family_middle_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : i.val = r) : fam k r (mk3 k v0 F zz) i = v0 := by
  rw [fam_in (by omega), three_part_frame_zero (by show i.val - r = 0; omega)]

theorem frame_family_last_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k)
    {i : Fin (2 * r + k + 1)} (hi : i.val = r + k) : fam k r (mk3 k v0 F zz) i = zz := by
  rw [fam_in (by omega), three_part_frame_last hk (by show i.val - r = k; omega)]

theorem frame_family_middle_range {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : r + 1 ≤ i.val ∧ i.val < r + k) :
    fam k r (mk3 k v0 F zz) i = F ⟨i.val - r - 1, by omega⟩ := by
  rw [fam_in (by omega), three_part_frame_middle (by show i.val - r ≠ 0; omega) (by show i.val - r ≠ k; omega)]

theorem blockProjection_basisVector_eq_zero {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) : SSn.wbP k r (bvec i) = 0 := by
  funext p
  unfold SSn.wbP bvec
  split_ifs with hp
  · rw [Pi.single_apply, if_neg (by rintro rfl; omega)]; rfl
  · rfl

theorem prWv_bvec_out (z' : Fin (2 * r + k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    SSn.prWv k r z' (bvec i) = 0 := by
  unfold SSn.prWv
  rw [blockProjection_basisVector_eq_zero hi]
  simp [herm]

theorem prWv_self {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    SSn.prWv k r z' z' = 0 := by
  rw [DU.prWv_of hz', FrameEntries.herm_self]
  have hT0 : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  rw [neg_div, div_self hT0, neg_smul, one_smul, add_neg_cancel]

theorem herm_zero_l (w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 w = 0 := by simp [herm]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem io_fam (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) (c : ℂ)
    (i : Fin (2 * r + k + 1)) :
    SSn.io0 k r z z' μsec ζ *ᵥ fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ) Fr (c • z')) i =
      if h : r + 1 ≤ i.val ∧ i.val < r + k then NF.muZ k r μsec ζ *ᵥ Fr ⟨i.val - r - 1, by omega⟩ else 0 := by
  obtain ⟨-, -, -, -, -, -, h11, hfix⟩ := pt_facts hz hz' hT hT' hsec hζ
  rw [ioMulVec]
  by_cases hout : i.val < r ∨ r + k < i.val
  · rw [fam_out hout, prWv_bvec_out z' hout, herm_zero_l, zero_smul, sub_zero, Matrix.mulVec_zero,
      dite_eq_right (by omega)]
  · by_cases h0 : i.val = r
    · rw [frame_family_middle_index h0, hfix, h11, one_smul, sub_self, Matrix.mulVec_zero, dite_eq_right (by omega)]
    · by_cases hl : i.val = r + k
      · rw [frame_family_last_index (by omega) hl, TF.prWv_smul, prWv_self hz' hT', smul_zero, herm_zero_l, zero_smul, sub_zero,
          Matrix.mulVec_zero, dite_eq_right (by omega)]
      · have hm : r + 1 ≤ i.val ∧ i.val < r + k := by omega
        rw [frame_family_middle_range hm, dite_eq_left hm,
          DU.prWv_fix (hFr.1 _) (hFr.2.2 _ z' (by simp)), hFr.2.2 _ _ (by simp), zero_smul, sub_zero]

end pt

theorem hpk_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem cz_facts {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    inWb k r ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ∧
    herm (Hpk k r) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) = -1 ∧
    (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hs : 0 < Real.sqrt (Tz k r z) := Real.sqrt_pos.2 hT
  refine ⟨Qx8.inWb_smul hz _, ?_, by exact_mod_cast (inv_pos.2 hs).ne'⟩
  rw [DU.hsmul_l, DU.hsmul_r, FrameEntries.herm_self, Complex.conj_ofReal]
  have hsq : Real.sqrt (Tz k r z) ^ 2 = Tz k r z := Real.sq_sqrt hT.le
  have hsq' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ^ 2 = ((Tz k r z : ℝ) : ℂ) := by exact_mod_cast hsq
  have hne : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  rw [hsq']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

noncomputable section

open DT in
theorem datum_transit_existence : DTExists := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨Fr₁, hFr₁⟩ := frame'_exists hk hz hz' hT hT' hsec h₁
  obtain ⟨Fr₂, hFr₂⟩ := frame'_exists hk hz hz' hT hT' hsec h₂
  obtain ⟨hW₁, hνz₁, hνν₁, -, hW₁', hνz₁', hνν₁', -⟩ := pt_facts hz hz' hT hT' hsec h₁
  obtain ⟨hW₂, hνz₂, hνν₂, -, hW₂', hνz₂', hνν₂', -⟩ := pt_facts hz hz' hT hT' hsec h₂
  obtain ⟨mW₁, mO₁, mz₁, mν₁⟩ := mu_frame hz hz' hT hT' hsec h₁ hFr₁
  obtain ⟨mW₂, mO₂, mz₂, mν₂⟩ := mu_frame hz hz' hT hT' hsec h₂ hFr₂
  obtain ⟨czW, czz, cz0⟩ := cz_facts hz hT
  obtain ⟨czW', czz', cz0'⟩ := cz_facts hz' hT'
  set c := (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) with hc
  set c' := (((Real.sqrt (Tz k r z'))⁻¹ : ℝ) : ℂ) with hc'
  have hνc : ∀ ν, herm (Hpk k r) ν z = 0 → herm (Hpk k r) ν (c • z) = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hνc' : ∀ ν, herm (Hpk k r) ν z' = 0 → herm (Hpk k r) ν (c' • z') = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hFz' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) z' = 0 :=
    fun hF j => hF.2.2 j z' (by simp)
  have hFν' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 :=
    fun hF j => hF.2.2 j _ (by simp)

  have oX' := three_part_frame_orthonormal hk hW₁' czW' hFr₁.1 hνν₁' czz' (hνc' _ hνz₁') (hFν' hFr₁) (fun j => hνc' _ (hFz' hFr₁ j)) hFr₁.2.1
  have oY' := three_part_frame_orthonormal hk hW₂' czW' hFr₂.1 hνν₂' czz' (hνc' _ hνz₂') (hFν' hFr₂) (fun j => hνc' _ (hFz' hFr₂ j)) hFr₂.2.1
  have oX := three_part_frame_orthonormal hk hW₁ czW mW₁ hνν₁ czz (hνc _ hνz₁) mν₁ (fun j => hνc _ (mz₁ j)) mO₁
  have oY := three_part_frame_orthonormal hk hW₂ czW mW₂ hνν₂ czz (hνc _ hνz₂) mν₂ (fun j => hνc _ (mz₂ j)) mO₂
  set x' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₁) Fr₁ (c' • z')) with hx'
  set y' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₂) Fr₂ (c' • z')) with hy'
  set x := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₁) (fun j => NF.muZ k r μsec ζ₁ *ᵥ Fr₁ j) (c • z)) with hx
  set y := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₂) (fun j => NF.muZ k r μsec ζ₂ *ᵥ Fr₂ j) (c • z)) with hy
  obtain ⟨h', hh'U, hh'⟩ := wittGram _ (Hpk k r) hpk_det_unit x' y' (famGram oX') (famGram oY')
  obtain ⟨h, hhU, hh⟩ := wittGram _ (Hpk k r) hpk_det_unit x y (famGram oX) (famGram oY)
  have pr : r ≤ r ∧ r ≤ r + k := by omega
  let iR : Fin (2 * r + k + 1) := ⟨r, by omega⟩
  let iL : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
  have fixOut : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (e e' : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ), (∀ i, g *ᵥ fam k r e i = fam k r e' i) →
      ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro g e e' hg a
    have h1 := hg (eI k r a)
    have h2 := hg (esI k r a)
    rw [fam_out (by simp [eI]), fam_out (by simp [eI])] at h1
    rw [fam_out (by simp [esI]; omega), fam_out (by simp [esI]; omega)] at h2
    exact ⟨h1, h2⟩
  have fixZ : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (w : Fin (2 * r + k + 1) → ℂ) (t : ℂ),
      t ≠ 0 → g *ᵥ (t • w) = t • w → g *ᵥ w = w := by
    intro g w t ht h
    rw [Matrix.mulVec_smul] at h
    exact smul_right_injective _ ht h
  have hhz : h *ᵥ z = z := by
    have := hh iL
    rw [hx, hy, frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h z c cz0 this
  have hh'z : h' *ᵥ z' = z' := by
    have := hh' iL
    rw [hx', hy', frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h' z' c' cz0' this
  have hmem : h ∈ UWset k r z := ⟨hhU, fixOut h _ _ hh, hhz⟩
  have hmem' : h' ∈ UWset k r z' := ⟨hh'U, fixOut h' _ _ hh', hh'z⟩
  refine ⟨h, hmem, h', hmem', ?_, ?_, ?_⟩
  · have := hh iR
    rw [hx, hy, frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have := hh' iR
    rw [hx', hy', frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have key : h * SSn.io0 k r z z' μsec ζ₁ = SSn.io0 k r z z' μsec ζ₂ * h' := by
      refine extGram _ (Hpk k r) hpk_det_unit x' (famGram oX') _ _ fun i => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh' i, hx', io_fam hk hz hz' hT hT' hsec h₁ hFr₁ c' i,
        hy', io_fam hk hz hz' hT hT' hsec h₂ hFr₂ c' i]
      by_cases hm : r + 1 ≤ i.val ∧ i.val < r + k
      · rw [dite_eq_left hm, dite_eq_left hm]
        have := hh i
        rw [hx, hy, frame_family_middle_range hm, frame_family_middle_range hm] at this
        exact this
      · rw [dite_eq_right hm, dite_eq_right hm, Matrix.mulVec_zero]
    rw [key, Matrix.mul_assoc, FrameEntries.mul_inv_uh hh'U, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormDone
section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem top_domination_measurable_compact : TopDMeasCpt := TDM.topDMeasCpt_of_typeNormMeas type_norm_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThtAdapted
section
open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {n r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nu0'_facts (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ) {m : ℕ}
    {Fr' : Fin m → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr') :
    inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) ∧
      herm (Hpk (n + 1) r) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Bs.z' = 0 ∧
      IsFrameOf (n + 1) r [Bs.z', SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ] Fr' := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  obtain ⟨-, -, hfix, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb (n + 1) r ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) := Qx8.inWb_mulVec hGi hz
  have hW : inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) := by
    show inWb (n + 1) r (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hy) _
  refine ⟨hW, ?_, hFr'.1, hFr'.2.1, fun a w hw => ?_⟩
  · rw [← hfix]; exact DU.prWv_perp Bs.T'_pos hW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hFr'.2.2 a _ (by simp)
    · show herm (Hpk (n + 1) r) (Fr' a)
        (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z))) = 0
      have h0 : herm (Hpk (n + 1) r) (Fr' a)
          (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)) = 0 := by
        rw [DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFr'.2.2 a ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) (by simp),
          hFr'.2.2 a Bs.z' (by simp), mul_zero, add_zero]
      unfold SSn.unitH
      rw [DU.hsmul_r, h0, mul_zero]

theorem tht_adapted (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ)
    {Bw Bw' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ} (hBw : IsFrameOf (n + 1) r [Bs.z] Bw)
    (hBw' : IsFrameOf (n + 1) r [Bs.z'] Bw') {Fr : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hB₁ : IsFrameOf (n + 1) r [Bs.z]
      (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)))
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z']
      (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a)) (X : Wq →L[ℂ] Wp) (v : Wq) :
    tht (n + 1) r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)
        (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) X v =
      ∑ c : Fin n, etaK (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr
          (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c
        (X (yK (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ)
          (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c v)) := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
  have hR : IsRepW (n + 1) r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hR' : IsRepW (n + 1) r Bs.z' Bs.π' := ⟨Bs.π'_rep, Bs.π'_cont⟩
  obtain ⟨hνfix, hνν, hν'fix, hν'ν'⟩ := DU.base hz hz' hT hT' Bs.sec hζ
  obtain ⟨hν'W, hν'z, hFr2⟩ := nu0'_facts Bs hζ hFr'
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ (n + 1) r Bs.μsec ζ ∈ UH (Hpk (n + 1) r) := hG.1
  have hmm : NF.muZ (n + 1) r Bs.μsec ζ * (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  set μ := NF.muZ (n + 1) r Bs.μsec ζ with hμ
  set ν := SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν
  set ν' := SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν'
  have hB₁' := FrameExtension.frame_snoc hFr2 hν'W hν'z hν'ν'
  set B₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν with hB₁def
  set B₁' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν' with hB₁'def
  have hBc : ∀ c : Fin n, B₁ c.castSucc = Fr c := fun c => by rw [hB₁def, Fin.snoc_castSucc]
  have hBl : B₁ (Fin.last n) = ν := by rw [hB₁def, Fin.snoc_last]
  have hBc' : ∀ c : Fin n, B₁' c.castSucc = μ⁻¹ *ᵥ Fr c := fun c => by rw [hB₁'def, Fin.snoc_castSucc]
  have hBl' : B₁' (Fin.last n) = ν' := by rw [hB₁'def, Fin.snoc_last]
  rw [TF.tht_indep hz hT hR hz' hT' hR' hBw hB₁ hBw' hB₁' ν ν' _, TF.tht_form hz hT hR hB₁, hνfix, hν'fix]
  simp only [ContinuousLinearMap.sum_apply, TF.sandw_apply, ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_castSucc]
  have hlast : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' (Fin.last n) = 0 := by
    rw [section_embedding_mul_vec, hBl', ← hν', hν'fix, hν'ν', one_smul, sub_self, Matrix.mulVec_zero]
  have hpr0 : SSn.prWv (n + 1) r Bs.z (0 : Fin (2 * r + (n + 1) + 1) → ℂ) = 0 := by
    have := TF.prWv_smul (k := n + 1) (r := r) Bs.z 0 0
    simpa using this
  rw [hlast, hpr0, TF.ebM_zero_left, TF.ecOp_zero, ContinuousLinearMap.zero_apply, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' c.castSucc = Fr c := by
    rw [section_embedding_mul_vec, hBc', ← hν', DU.prWv_fix (hFr2.1 c) (hFr2.2.2 c Bs.z' (by simp)), hFr2.2.2 c ν' (by simp),
      zero_smul, sub_zero, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  have hFc : SSn.prWv (n + 1) r Bs.z (Fr c) = Fr c := by
    rw [← hBc c]
    exact DU.prWv_fix (hB₁.1 _) (hB₁.2.2 _ Bs.z (by simp))
  rw [hc, hFc]
  have e1 : ebM (n + 1) r (Fr c) ν = unitB (Hpk (n + 1) r) B₁ c.castSucc (Fin.last n) := by
    rw [← TF.ebM_frame, hBc, hBl]
  have e2 : ebM (n + 1) r ν' (B₁' c.castSucc) = unitB (Hpk (n + 1) r) B₁' (Fin.last n) c.castSucc := by
    rw [← TF.ebM_frame, hBl']
  rw [e1, e2]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end

