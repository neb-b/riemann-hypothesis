module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCharB

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.DerivSmulConstAll
section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SmulConstantLinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  by_cases hT : T = 0
  · simp [hT]
  have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
    intro hd'
    apply hd
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
    have hT' : g T ≠ 0 := by
      rw [hg]; simpa using hT
    have heq : h = fun t => (g T)⁻¹ * g (h t • T) := by
      funext t
      rw [map_smul, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hT', mul_one]
    rw [heq]
    exact ((g.restrictScalars ℝ).differentiableAt.comp 0 hd').const_mul _
  rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ldV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

theorem rdV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

theorem rw_smul_const (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih, rdV_smul_const]

theorem dLR_smul_const (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact rw_smul_const v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih, ldV_smul_const]

theorem ccle_smul_const {A : ℝ} {m : ℕ} {f : Mat k r → ℂ} {c : ℝ} (T : E) (hf : CCle A m f c) :
    CCle A m (fun g => f g • T) (c * ‖T‖) := by
  obtain ⟨hCk, hb⟩ := hf
  refine ⟨fun g₀ hg₀ => ?_, fun u v hu hv hl g hg => ?_⟩
  · obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hCk g₀ hg₀
    refine ⟨U, fun g => f' g • T, hU, hgU, hcd.smul contDiffOn_const, fun g hgU hgG => ?_⟩
    show f g • T = f' g • T
    rw [heq g hgU hgG]
  · have h1 := hb u v hu hv hl g hg
    have hd : dLR u v (fun g => f g • T) g = dLR u v f g • T := by
      rw [dLR_smul_const]
    rw [hd, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg T)

end SmulConstantLinearity

theorem stCut1p (h : UnitaryGroupStructuralFacts) : StCut1p := by
  intro k r Wp _ _ _ A m f X₀ hf
  obtain ⟨c, hc⟩ := hf
  exact ⟨c * ‖X₀‖, SmulConstantLinearity.ccle_smul_const X₀ hc⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HilbertSchmidtContinuousFunctional
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hilbertSchmidt_vec_add (A B : Wp →L[ℂ] Wp) : hsVec (A + B) = hsVec A + hsVec B := by
  ext i
  simp [hsVec]

theorem hilbertSchmidt_vec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := by
  ext i
  simp [hsVec]

def hilbertSchmidtFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun T := hsInner T X₀
  map_add' A B := by simp only [hsInner, hilbertSchmidt_vec_add, inner_add_right]
  map_smul' c A := by simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]

def hilbertSchmidtContinuousFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (hilbertSchmidtFunctional X₀)

theorem hilbertSchmidt_functional_apply (X₀ T : Wp →L[ℂ] Wp) : hilbertSchmidtContinuousFunctional X₀ T = hsInner T X₀ := by
  rfl

theorem hilbertSchmidt_inner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right]

section adj

variable [CompleteSpace Wp] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

theorem integrable_adjoint {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    Integrable (fun a => ContinuousLinearMap.adjoint (U a)) μ := by
  refine hU.congr' (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hU.1) ?_
  exact Filter.Eventually.of_forall fun a => (ContinuousLinearMap.adjoint.norm_map (U a)).symm

theorem integral_adjoint_comm {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    ∫ a, ContinuousLinearMap.adjoint (U a) ∂μ = ContinuousLinearMap.adjoint (∫ a, U a ∂μ) := by
  exact ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul
    (ContinuousLinearMap.adjoint : (Wp →L[ℂ] Wp) ≃ₗᵢ⋆[ℂ] (Wp →L[ℂ] Wp)).toContinuousLinearEquiv.toContinuousLinearMap hU

variable [SFinite μ] [SFinite ν]

theorem integrable_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    Integrable (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) := by
  have hG : Continuous fun x : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) =>
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint x.1).comp x.2) :=
    (hilbertSchmidtContinuousFunctional X₀).continuous.comp
      ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_comp continuous_snd)
  have hm : AEStronglyMeasurable
      (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun A B : Wp →L[ℂ] Wp => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint A).comp B)) hG
      (hU.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
      (hV.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hb : Integrable (fun q : α × β => ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖)) (μ.prod ν) :=
    (hU.norm.mul_prod hV.norm).const_mul _
  refine hb.mono' hm (Filter.Eventually.of_forall fun q => ?_)
  calc ‖hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))‖
      ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖ :=
        (hilbertSchmidtContinuousFunctional X₀).le_opNorm _
    _ ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖) := by
        gcongr
        calc ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖
            ≤ ‖ContinuousLinearMap.adjoint (U q.1)‖ * ‖V q.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖U q.1‖ * ‖V q.2‖ := by rw [ContinuousLinearMap.adjoint.norm_map]

theorem integral_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    ∫ q, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)) ∂(μ.prod ν) =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (∫ a, U a ∂μ)).comp (∫ b, V b ∂ν)) := by
  rw [integral_prod _ (integrable_hilbertSchmidt_pairing X₀ hU hV)]
  have hin : ∀ a, ∫ b, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (V b)) ∂ν =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (∫ b, V b ∂ν)) := fun a =>
    ((hilbertSchmidtContinuousFunctional X₀).comp (ContinuousLinearMap.compL ℂ Wp Wp Wp (ContinuousLinearMap.adjoint (U a)))).integral_comp_comm hV
  simp_rw [hin]
  have hout := ((hilbertSchmidtContinuousFunctional X₀).comp
    ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (∫ b, V b ∂ν))).integral_comp_comm (integrable_adjoint hU)
  rw [integral_adjoint_comm hU] at hout
  exact hout

end adj

theorem sigmaFinite_of_haar_on {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem ae_mem_big_cell (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sigmaFinite_of_haar_on D.haarW
  have := sigmaFinite_of_haar_on D.haarN
  have := sigmaFinite_of_haar_on D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have h2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have h3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have h4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [h1, h2, h3, h4] with p a b c d
  exact ⟨a, b, c, d⟩

theorem linear_form_continuous (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]
    exact continuous_id.matrix_elem _ _
  · simp only [h, dite_false]
    exact (continuous_apply (eI k r a)).comp (continuous_id.matrix_mulVec continuous_const)

theorem character_continuous (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) : Continuous (xiTau D τ) := by
  have hl : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun n : Mt k r => lam k r z (Matrix.of n) :=
    fun z => Complex.continuous_re.comp (continuous_const.mul ((linear_form_continuous z).comp continuous_id))
  unfold xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul ((hl D.z).comp (continuous_snd.comp continuous_fst))).sub
    (continuous_const.mul ((hl D.z').comp (continuous_snd.comp continuous_snd)))

theorem norm_character_eq_one (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem star_character_mul_self (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) :
    star (xiTau D τ p) * xiTau D τ p = 1 := by
  rw [Complex.star_def, Complex.conj_mul', norm_character_eq_one]
  simp

theorem character_at_one_eq_product (D : RealPlaceData k r Wp Wp) (hz : D.z' = D.z) (p : SS k r) :
    xiTau D (1, 1) p = psiD D (Matrix.of p.1.2) * star (psiD D (Matrix.of p.2.2)) := by
  unfold xiTau psiD psi lam
  rw [hz, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem adjoint_representation_inv [CompleteSpace Wp] (D : RealPlaceData k r Wp Wp) (hCW : IsClosedSubgroup (UWset k r D.z))
    {h : Mat k r} (hh : h ∈ UWset k r D.z) : ContinuousLinearMap.adjoint (D.π h⁻¹) = D.π h := by
  have hi : h⁻¹ ∈ UWset k r D.z := hCW.inv_mem h hh
  have h1 : (D.π h).comp (D.π h⁻¹) = 1 := by
    rw [← D.π_rep.2 h hh h⁻¹ hi, Matrix.mul_nonsing_inv _ (hCW.unit h hh), D.π_rep.1]
  have hA : (ContinuousLinearMap.adjoint (D.π h)).comp (D.π h) = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (D.π h)).1 (D.π_unitary h hh)
  have hadj : ContinuousLinearMap.adjoint (D.π h) = D.π h⁻¹ := by
    calc ContinuousLinearMap.adjoint (D.π h)
        = (ContinuousLinearMap.adjoint (D.π h)).comp ((D.π h).comp (D.π h⁻¹)) := by
          rw [h1]; rfl
      _ = ((ContinuousLinearMap.adjoint (D.π h)).comp (D.π h)).comp (D.π h⁻¹) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = D.π h⁻¹ := by rw [hA]; rfl
  rw [← hadj, ContinuousLinearMap.adjoint_adjoint]

end ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HsInnerSmulRight
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

end hpk

variable {k r : ℕ}

theorem GV_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [Matrix.inv_eq_left_inv (UH_left_inv k r hg)]; exact UH_left_inv k r hg

theorem GV_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (GV_inv_mul hg)

theorem GV_mul_mem {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem GV_inv_mem {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [← Matrix.conjTranspose_mul, GV_mul_inv hg, Matrix.conjTranspose_one, Matrix.one_mul,
          Matrix.mul_one]

theorem sig_mul (X : SigData k r) {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) :
    X.σ (a * b) = (X.σ a).comp (X.σ b) := X.rep.1.2 a ha b hb

theorem sig_inv (X : SigData k r) {a : Mat k r} (ha : a ∈ GV k r) :
    X.σ a⁻¹ = ContinuousLinearMap.adjoint (X.σ a) := by
  have h1 : ContinuousLinearMap.adjoint (X.σ a) ∘L X.σ a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (X.rep.2.1 a ha)
  have h2 : X.σ a ∘L X.σ a⁻¹ = 1 := by
    rw [← X.rep.1.2 a ha _ (GV_inv_mem ha), GV_mul_inv ha, X.rep.1.1]
  ext v
  have e1 := congrArg (fun T => T (X.σ a⁻¹ v)) h1
  have e2 := congrArg (fun T => T v) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [← e1, e2]

theorem mc_conj (X : SigData k r) (x y : X.Hs) {s g s' : Mat k r} (hs : s ∈ GV k r) (hg : g ∈ GV k r)
    (hs' : s' ∈ GV k r) : mc X x y (s⁻¹ * g * s') = mc X (X.σ s' x) (X.σ s y) g := by
  have h1 : s⁻¹ * g ∈ GV k r := GV_mul_mem (GV_inv_mem hs) hg
  simp only [mc]
  rw [sig_mul X h1 hs', sig_mul X (GV_inv_mem hs) hg, sig_inv X hs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  simp only [sgs, Matrix.mul_inv_rev, Matrix.mul_assoc]

section hs

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

theorem hsInner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_right]

theorem hsInner_smul_right (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner A (c • B) = conj c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_left]

theorem rho_scal (D : RealPlaceData k r Wp Wp) (p : SS k r) (f : Mat k r → ℂ) (g : Mat k r) :
    rho D p (scalF Wp f) g = f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π' (Matrix.of p.2.1)⁻¹) := by
  simp only [rho, scalF, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_smul]

end hs

end GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GroupMatrixMembership

theorem stCut1 (h : UnitaryGroupStructuralFacts) : StCut1 := by
  unfold StCut1
  intro k r Wp _ _ _ D X hD d hd f x y a₂ b₂ X₀ hf p hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hs : Matrix.of p.1.2 * Matrix.of p.1.1 ∈ GV k r := GV_mul_mem hn.1 hh.1
  have hs' : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := GV_mul_mem hn'.1 hh'.1
  have hG : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r :=
    ae_iff.2 (measure_mono_null (fun g hg => hg) D.haarG.conc)
  have key : ∀ᵐ g ∂D.μG, hsInner (rho D p (scalF Wp f) (Matrix.of g)) (mc X a₂ b₂ (Matrix.of g) • X₀) =
      (mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
          (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g))) *
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ := by
    filter_upwards [hG] with g hg
    rw [rho_scal, hD.π_eq, hsInner_smul_left, hsInner_smul_right, sgs_eq,
      hf _ (GV_mul_mem (GV_mul_mem (GV_inv_mem hs) hg) hs'), mc_conj X x y hs hg hs']
    ring
  simp only [Ph]
  rw [integral_congr_ae key, integral_mul_const]
  have hS := (hd.2 (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
    a₂ b₂).2
  have e1 : ∫ g : Mt k r, mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x)
      (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y) (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g)) ∂D.μG =
      ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ * ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ /
        (d : ℂ) := hS
  have e2 : star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1)) =
      ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ := inner_conj_symm _ _
  have e3 : mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) = ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ :=
    rfl
  rw [e1, e2, e3]
  ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquiv
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stBeEquiv (h : UnitaryGroupStructuralFacts) : StBeEquiv := by
  intro k r Wp _ _ _ D X _ _ u u' hI h0 hh0 m hm
  exact ⟨BeEquiv.beOp_left D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm,
    BeEquiv.beOp_right D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stInvChar : StInvChar := by
  intro k r Wp _ _ _ D X _ _ γ hγ m hm
  have hE : IsUnit (embWb k r γ).det := InvChr.unit_embWb (InvChr.unit_of_frame hγ.1)
  have hcc : InvChr.cc γ D.z = D.z := InvChr.frame_conjugation_fixes_vector hE D.z D.T_pos hγ.2
  have hbar : ∀ n : Mat k r, ell k r D.z (gbar k r γ n) = starRingEnd ℂ (ell k r D.z n) :=
    fun n => InvChr.ell_gbar hE D.z hcc n
  have hdet : IsUnit m.det := by
    have hU : m.conjTranspose * Hpk k r * m = Hpk k r := hm.1
    refine Matrix.isUnit_det_of_left_inverse (B := Hpk k r * m.conjTranspose * Hpk k r) ?_
    calc Hpk k r * m.conjTranspose * Hpk k r * m = Hpk k r * (m.conjTranspose * Hpk k r * m) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, InvChr.Hpk_sq k r]
  have hinv : ell k r D.z m⁻¹ = -ell k r D.z m :=
    InvChr.ell_inv_N D.z D.z_mem m m⁻¹ hm (Matrix.nonsing_inv_mul m hdet)
  have hth : th k r γ m = gbar k r γ m⁻¹ := (InvChr.gbar_inv hE m hdet).symm
  refine ⟨?_, ?_⟩
  · simp only [lam, hbar, InvChr.cStd_conj_re]
  · simp only [psiD, psi, hth, hbar, hinv, map_neg, mul_neg, Complex.neg_re,
      InvChr.cStd_conj_re, neg_neg]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

