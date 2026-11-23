module

public import Mathlib
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementU
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HpkConjTranspose
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open GlobalTheory.LeadingMinorInv

namespace OmgRight

end OmgRight

open OmgRight

open Matrix in
variable {k r : ℕ} in
private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH {x : _root_.Formalism.FourierDecayAlt.Q.Mx k r} (hx : x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    x⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx

open Matrix in
variable {k r : ℕ} in
private lemma hpk_mul_hpk_mul_eq_self (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) :
    _root_.Formalism.QuantumDeterminants.Hpk k r * (_root_.Formalism.QuantumDeterminants.Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma hpk_conjTranspose_eq_self' : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

open Matrix in
variable {k r : ℕ} in
private lemma adjugate_upUni_last_apply {m : ℕ} {U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) (a : Fin (m + 1)) :
    U.adjugate (Fin.last m) a = if a = Fin.last m then 1 else 0 := by
  rw [adjugate_apply, det_of_upperTriangular]
  · simp [updateRow_apply, Pi.single_apply, hU.2]
  · intro i j hij
    simp only [updateRow_apply]
    split_ifs with h
    · subst h
      rw [Pi.single_apply, if_neg]
      exact (hij.trans_le (Fin.le_last _)).ne
    · exact hU.1 i j hij

open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_smul_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_conjTranspose_hpk_mul_flagMat_mul (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma prW_mulVec_eq_of_mem_nset_of_tail_eq_zero {z' : Fin (2 * r + k + 1) → ℂ} {m : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hm : m ∈ _root_.Formalism.QuantumDeterminants.Nset k r) {p : Fin (2 * r + k + 1) → ℂ}
    (hp : ∀ j : Fin (2 * r + k + 1), r + k < ↑j → p j = 0) :
    _root_.Formalism.FourierDecayAlt.D.prW k r z' (m *ᵥ p) = _root_.Formalism.FourierDecayAlt.D.prW k r z' p := by
  have hNC := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2
  have hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0) := by
    ext i
    split_ifs with hi
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hNC i i hi.2 (min_le_left _ _)]
        simp
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ r + k
        · rw [hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]
          simp
        · rw [hp j (by omega)]
          simp
      · simp
    · rfl
  simp only [_root_.Formalism.FourierDecayAlt.D.prW]
  rw [hb]

open Matrix in
variable {k r : ℕ} in
private lemma mulVec_adjugate_single_last_apply_eq_zero_of_lt (z' : Fin (2 * r + k + 1) → ℂ)
    (Q : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) (j : Fin (2 * r + k + 1))
    (hj : r + k < ↑j) :
    (Q *ᵥ ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ *ᵥ
      Pi.single (Fin.last r) 1)) j = 0 := by
  have hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c,
      (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c := by
    intro X i c
    have hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l =
        if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0 :=
      fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l
    rw [Matrix.mul_apply]
    simp only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hj2 := j.isLt
  obtain ⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j := ⟨⟨2 * r + k - j, by omega⟩, rfl⟩
  have hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j := by
    have hb2 := b.isLt
    apply Fin.ext
    rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega
  have key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ *
      (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) =
      ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugate *
        (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')))ᴴ := by
    rw [conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 := congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)
  rw [adjugate_mul] at h1
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
  rw [conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)] at h1
  · rw [hJP, hpi] at h1
    have heps := _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)
    have hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1 := by
      simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]
    rw [hF, one_mul] at h1
    simp only [Matrix.one_apply, if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
    rw [mulVec_mulVec]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul] at heps
      exact absurd heps zero_ne_one
    · exact h
  · intro l _ hl
    simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]
  · simp


open Matrix in
theorem _root_.GlobalTheory.WigSh.omg_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g m _ hz' _ hm
  obtain ⟨U, hU, hmF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm
  have hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1
  have hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) := by
    rw [inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]
  have hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') =
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
        (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')) * U := by
    rw [conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
      Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]
  have he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
    ext a
    simp [mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]
  rw [rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul,
    ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]
  exact prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm)
    (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace DualFRep

theorem gram_transpose (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᵀ = Formalism.QuantumDeterminants.Hpk k r := by
  have h := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [conjTranspose_apply] at h1
  rw [transpose_apply, ← h1]
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> simp

variable {n : ℕ}

theorem left_inv {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, h2]

theorem inv_eq {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H :=
  Matrix.inv_eq_left_inv (left_inv h2 hg)

theorem entry_le {k r : ℕ} (g : Mx k r) (a b : Fin (2 * r + k + 1)) : ‖g a b‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g a b) ≤ ∑ j, Complex.normSq (g a j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (g a j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end DualFRep


open DualFRep in
theorem isFRep_dualM (k r : ℕ) : IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  have h1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 := gram_transpose k r
  have hmem : ∀ g ∈ GG k r, gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := fun g hg => hg
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 h3 hmem ⊢
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dualM]
  · intro g hg h hh
    simp only [dualM]
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  · intro g hg
    have key : g⁻¹ * H * (g⁻¹)ᴴ = H := by
      rw [inv_eq h2 (hmem g hg)]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1]
      calc H * gᴴ * H * H * (H * (g * H)) = H * (gᴴ * (H * H) * H * g) * H := by
            simp only [Matrix.mul_assoc]
        _ = H := by rw [h2, Matrix.mul_one, hmem g hg, h2, Matrix.one_mul]
    have e : ((g⁻¹)ᵀ)ᴴ = ((g⁻¹)ᴴ)ᵀ := rfl
    have := congrArg Matrix.transpose key
    rw [transpose_mul, transpose_mul, h3] at this
    simp only [dualM]
    rw [e, Matrix.mul_assoc, this]
  · intro i j
    have hc : Continuous (fun g : Mx k r => (H * gᴴ * H) j i) := by
      have : Continuous (fun g : Mx k r => H * gᴴ * H) :=
        (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
      exact this.matrix_elem j i
    refine hc.continuousOn.congr ?_
    intro g hg
    simp only [dualM, transpose_apply]
    rw [inv_eq h2 (hmem g hg)]
  · refine ⟨∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖, ?_⟩
    intro g hg i j
    simp only [dualM, transpose_apply, pow_one]
    rw [inv_eq h2 (hmem g hg)]
    have hN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc ‖(H * gᴴ * H) j i‖ = ‖∑ b, ∑ a, H j a * star (g b a) * H b i‖ := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
      _ ≤ ∑ b, ∑ a, ‖H j a * star (g b a) * H b i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
      _ ≤ ∑ b, ∑ a, ‖H j a‖ * ‖H b i‖ * B.gN g := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul, norm_star, mul_right_comm]
          exact mul_le_mul_of_nonneg_left (entry_le g b a) (by positivity)
      _ = (∑ b, ∑ a, ‖H j a‖ * ‖H b i‖) * B.gN g := by simp only [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact Finset.single_le_sum
            (f := fun p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖)
            (fun p _ => by positivity) (Finset.mem_univ (i, j))
  · intro g hg hu
    have hl : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
    have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv hl
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [dualM]
    rw [hinv]
    have e : star ((star g)ᵀ) = gᵀ := by
      ext a b
      simp [Matrix.star_apply]
    rw [e, ← transpose_mul, (Matrix.mem_unitaryGroup_iff).1 hu, transpose_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarNotions


open Formalism.FourierDecayAlt.P.B2x1 in
theorem finite_compact_of_sigmaFinite {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [SigmaFinite μ] (hc : μ Uᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) (K : Set (Formalism.QuantumDeterminants.Mt k r)) (hK : IsCompact K) : μ K < ∞ := by
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have : SigmaFinite (pull hU μ) := by
    have h : SigmaFinite ((pull hU μ).map inc) := by rw [map_pull μ hc]; infer_instance
    exact SigmaFinite.of_map _ inc_memb.measurable.aemeasurable h
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Gp U hU)) := inferInstance
  have huniq := Measure.haarMeasure_unique (pull hU μ) K₀
  have hfin : pull hU μ K₀ ≠ ∞ := by
    intro hinf
    rw [hinf] at huniq
    have hzero : ∀ n, Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) = 0 := by
      intro n
      by_contra hne
      have h1 := measure_spanningSets_lt_top (pull hU μ) n
      have h2 : pull hU μ (spanningSets (pull hU μ) n) =
          ∞ * Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) :=
        congrArg (fun m : Measure (Gp U hU) => m (spanningSets (pull hU μ) n)) huniq
      rw [h2, ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have huniv : Measure.haarMeasure K₀ Set.univ = 0 := by
      rw [← iUnion_spanningSets (pull hU μ)]
      exact measure_iUnion_null hzero
    have h1 : Measure.haarMeasure K₀ K₀ = 0 := measure_mono_null (Set.subset_univ _) huniv
    rw [Measure.haarMeasure_self] at h1
    exact one_ne_zero h1
  have hK' : IsCompact ((inc : Gp U hU → Formalism.QuantumDeterminants.Mt k r) ⁻¹' K) := inc_closedEmb.isCompact_preimage hK
  have h3 : pull hU μ (inc ⁻¹' K) = pull hU μ K₀ * Measure.haarMeasure K₀ (inc ⁻¹' K) :=
    congrArg (fun m : Measure (Gp U hU) => m (inc ⁻¹' K)) huniq
  rw [← map_pull (hU := hU) μ hc, inc_memb.map_apply, h3]
  exact ENNReal.mul_lt_top hfin.lt_top hK'.measure_lt_top

theorem isHaarOn_iff {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (hex : ∃ ν : Measure (Formalism.QuantumDeterminants.Mt k r), B.IsHaarOn U ν) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ B.IsHaarOn U μ := by
  constructor
  · rintro ⟨hσ, h0, hc, hl⟩
    obtain ⟨ν, hν⟩ := hex
    have hfin := finite_compact_of_sigmaFinite hU μ hc hl
    obtain ⟨c, hcν⟩ := P.haar_measure_unique_up_to_scalar k r U ν μ hU hν hc hl hfin
    refine { ne_zero := h0, conc := hc, left := hl, right := ?_, finite_compact := hfin }
    intro a ha
    rw [hcν, Measure.map_smul, hν.right a ha]
    exact (show Continuous (B.rmulF a) from by
      unfold B.rmulF
      exact continuous_id.matrix_mul continuous_const).measurable.aemeasurable
  · intro h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem isHaarOn_iff_groups : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) :=
  fun k r μ =>
    ⟨isHaarOn_iff (P.unitary_group_closed k r) (P.unitary_group_haar_exists k r) μ,
      isHaarOn_iff (P.unipotent_radical_closed k r) (P.unipotent_haar_exists k r) μ,
      fun z hz hT _ => isHaarOn_iff (P.weyl_subgroup_closed k r z) (P.weyl_haar_exists k r z hz hT) μ⟩

end GlobalTheory.HaarNotions
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarInversion

def mulM {m : ℕ} (x y : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x * Matrix.of y) i j

noncomputable def invM {m : ℕ} (x : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x)⁻¹ i j

lemma of_mulM {m : ℕ} (x y : PI.MtM m) : Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl

lemma of_invM {m : ℕ} (x : PI.MtM m) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl

lemma measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → PI.MtM m}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)

lemma measurable_invM {m : ℕ} : Measurable (invM : PI.MtM m → PI.MtM m) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hof : Continuous fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : PI.MtM m => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : PI.MtM m => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2

theorem lintegral_inv_eq : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  intro m S μ hS hμ hR f hf
  obtain ⟨hσ, hne, hc, hL⟩ := hμ
  obtain ⟨-, -, -, hinv⟩ := hS
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := hc
  have left : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM (measurable_const (a := a)) measurable_id)
    have e : (fun y : PI.MtM m => mulM a (id y)) = PI.lmulQ (Matrix.of a) := rfl
    rw [e, hL _ ha] at h
    exact h.symm
  have right : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM measurable_id (measurable_const (a := a)))
    have e : (fun y : PI.MtM m => mulM (id y) a) = PI.rmulQ (Matrix.of a) := rfl
    rw [e, hR _ ha] at h
    exact h.symm
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : PI.MtM m → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            (hinv _ hy).2, Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst (measurable_invM.comp measurable_snd))).mul
            (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          rw [lintegral_mul_const _ hm, right (invM x) (hinv _ hx).1 f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key

end GlobalTheory.HaarInversion
end

