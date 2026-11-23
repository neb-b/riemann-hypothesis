module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0236
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0204
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0196

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section zfull

variable {j : ℕ}

theorem zfull_apply (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (i l : Fin (j + 1)) :
    zfull Z τ i l = if h : i.val < j ∧ l.val < j then Z ⟨i.val, h.1⟩ ⟨l.val, h.2⟩
      else if i.val = j ∧ l.val = j then τ else 0 := by
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨l', rfl⟩ := finSumFinEquiv.surjective l
  unfold zfull U.blk2
  rcases i' with a | a <;> rcases l' with b | b <;>
    simp [Matrix.reindex_apply] <;> omega

theorem zfull_det (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end zfull

section point

variable {k r j : ℕ}

theorem x0_GV (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hM := (Formalism.FourierDecayAlt.P.slice_membership k (j + 1) (r - (j + 1))).1 _ γ hZf hγ
  exact Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM

theorem upper_minor_of_level_point (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.xi0 (x0 k r j hj Z τ γ) a' q =
      if hq : q.val < j + 1 then zfull Z τ ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0 := by
  unfold PBG.xi0
  rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  unfold x0
  rw [LeftFubiniLemmas.castM_apply']
  have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j + 1 - 1 - a'.val, by omega⟩) := by
    ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
  rw [hi, LeftFubiniLemmas.embedding_map_apply_last_block]
  by_cases hq : q.val < j + 1
  · rw [dite_eq_left (by simpa using hq), dite_eq_left hq]
    congr 1; ext; simp [Fin.val_rev]; omega
  · rw [dite_eq_right (by simpa using hq), dite_eq_right hq]

theorem lower_minor_of_level_point (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.y0 (x0 k r j hj Z τ γ) a' q =
      if hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1 then
        star (zfull Z τ ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0 := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  unfold PBG.y0
  rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  have hgu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  unfold x0
  rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZf) hgu,
    LeftFubiniLemmas.castM_apply']
  have hjj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
    ext; rw [Ux3.block_index_first_val]; simp [eI]
  rw [hjj, LeftFubiniLemmas.embedding_map_apply_first_block]
  by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1
  · rw [dite_eq_left (by simp; omega), dite_eq_left hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
    congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
  · rw [dite_eq_right (by simp; omega), dite_eq_right hq]

end point

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalPositiveCompactSupport
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField

def WaveLocBC : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC → KB.DegWave → KB.SizeStdCpt → KB.VIsoCpt → FormPosCpt →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

def WaveLocBPCpt : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

end Formalism.FourierDecayAlt.P.PBL


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBL in
theorem Formalism.FourierDecayAlt.P.wave_local_compact_support_route : Formalism.FourierDecayAlt.P.PBL.WaveLocBC := by
  intro hA hPSC hDW hSS hVI hFP Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hCc hB
  refine ⟨fun i v => Xw S i v, thr_wave hCc hB, fun F hF v => ?_⟩
  intro i hi1 hir a ha haK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hir' : j + 1 ≤ S.G.r + 1 := hir
  have hj : j ≤ S.G.r := by omega
  have haK' : a.length + C.Kst ≤ S.Ntop := haK
  have ha' : D.AdmAt S v a := ha
  have haN : a.length ≤ S.Ntop := by omega
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨grid, hinj, hl1, hnodes, hlp, hlm⟩ := nodes_level hB v a ha' C.Kst haK' j hj
  have hwa : KB.CutWord (D.parOf S v) (S.l + 1) a :=
    (Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst 0 ha' haK' (by omega)).1
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a),
    PBD.pushU grid (fun ys => KB.minusW ys a), PBD.pushTh grid (fun ys => KB.minusW ys a), hlp, hlm,
    fun ε hε l Y hY => ⟨?_, Complex.I ^ C.Kst, by simp, ?_⟩⟩
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have h0 := block0C hA hPSC hVI hFP hB F hF v ε hε j hj a hwa l Y hY'
    rw [Nat.add_sub_cancel]
    exact h0
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have hK := blockK_waveC hA hPSC hDW hSS hVI hFP hB F hF v ε hε j hj a ha' haN hwa C.Kst grid hinj hnodes
      (Xw S (j + 1) v) (xw_nonneg hB _ v) (xw_K hB v j C.Kst grid hl1) l Y hY'
    refine blockPSD_congr (fun p' _ q' _ => ?_) (fun _ _ _ _ => rfl) (fun p' _ q' _ => ?_) hK
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.minusW ys a) (PBD.pushTh grid fun ys => KB.minusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]

theorem Formalism.FourierDecayAlt.P.wave_local_positive_compact_support : Formalism.FourierDecayAlt.P.PBL.WaveLocBPCpt := fun hA hPSC =>
  Formalism.FourierDecayAlt.P.wave_local_compact_support_route hA hPSC Formalism.FourierDecayAlt.P.degree_of_plane_wave Formalism.FourierDecayAlt.P.size_standard_compact
    Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support Formalism.FourierDecayAlt.P.module_form_pos_compact_support
end

