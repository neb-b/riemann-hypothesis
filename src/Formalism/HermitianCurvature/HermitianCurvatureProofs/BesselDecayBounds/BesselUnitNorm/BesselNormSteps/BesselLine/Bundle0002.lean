module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.Bundle0001
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvMeas
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Meas

variable {k r : ℕ}

theorem measurable_matInv : Measurable (fun x : Mt k r => (fun i j => (Matrix.of x)⁻¹ i j : Mt k r)) := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hc.matrix_det.measurable.inv.mul (hc.matrix_adjugate.matrix_elem i j).measurable

def minvM (x : Mt k r) : Mt k r := fun i j => (Matrix.of x)⁻¹ i j

def tripleMatrixProduct (q : Mt k r × Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of q.1 * Matrix.of q.2.1 * Matrix.of q.2.2) i j

theorem measurable_minvM : Measurable (minvM (k := k) (r := r)) := measurable_matInv

theorem triple_matrix_product_continuous : Continuous (tripleMatrixProduct (k := k) (r := r)) := by
  have h1 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.1 : Mx k r)) := continuous_fst
  have h2 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.2.1 : Mx k r)) :=
    continuous_fst.comp continuous_snd
  have h3 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.2.2 : Mx k r)) :=
    continuous_snd.comp continuous_snd
  exact (h1.matrix_mul h2).matrix_mul h3

theorem uh_inv_eq {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ = Hpk k r * aᴴ * Hpk k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc aᴴ, ha', hpk_sq]
  exact Matrix.inv_eq_left_inv h1

theorem isClosed_uw (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  simp only [UWset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine (isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc)
    continuous_const).inter ((isClosed_iInter fun a => (isClosed_eq
      (hc.matrix_mulVec continuous_const) continuous_const).inter (isClosed_eq
      (hc.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const))

theorem piInv_aesm {z : Fin (2 * r + k + 1) → ℂ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] {π : Mx k r → (Wp →L[ℂ] Wp)} (hπc : ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z))
    {μW : Measure (Mt k r)} (hμ : μW {x | Matrix.of x ∉ UWset k r z} = 0) :
    AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  have hS : MeasurableSet {x : Mt k r | Matrix.of x ∈ UWset k r z} := (isClosed_uw z).measurableSet
  have hμS : μW.restrict {x : Mt k r | Matrix.of x ∈ UWset k r z} = μW :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  rw [← hμS]
  have hπ' : ContinuousOn π (UWset k r z) := continuousOn_clm_apply.mpr hπc
  have hcont : ContinuousOn (fun x : Mt k r => π (Hpk k r * (Matrix.of x)ᴴ * Hpk k r))
      {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
    refine hπ'.comp (Continuous.continuousOn
      ((continuous_const.matrix_mul hc.matrix_conjTranspose).matrix_mul continuous_const)) ?_
    intro x hx
    have hx' : Matrix.of x ∈ UWset k r z := hx
    show Hpk k r * (Matrix.of x)ᴴ * Hpk k r ∈ UWset k r z
    rw [← uh_inv_eq hx'.1]
    exact uw_inv hx'
  refine (hcont.aestronglyMeasurable hS).congr ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  have hx' : Matrix.of x ∈ UWset k r z := hx
  show π (Hpk k r * (Matrix.of x)ᴴ * Hpk k r) = π (Matrix.of x)⁻¹
  rw [uh_inv_eq hx'.1]

theorem measF_of {z : Fin (2 * r + k + 1) → ℂ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)} [SigmaFinite μW]
    [SFinite μN]
    (hWr : ∀ h ∈ UWset k r z, MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x * h) i j) μW μW)
    (hWi : MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x)⁻¹ i j) μW μW)
    (hW0 : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN0 : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hNc : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r,
      MeasurePreserving (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m) i j) μN μN)
    (hNi : ∀ h ∈ UWset k r z,
      MeasurePreserving (fun x : Mt k r => fun i j => (h * (Matrix.of x)⁻¹ * h⁻¹) i j) μN μN)
    (hπc : ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z)) : MeasF z π μW μN := by
  refine ⟨?_, ?_, ?_, piInv_aesm hπc hW0⟩
  · have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW0)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN0)
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  · intro h hh m hm
    exact (hWr h hh).prod (hNc h hh m hm)
  · have hgm : Measurable (Function.uncurry fun (x : Mt k r) (y : Mt k r) =>
        (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) := by
      have e : (Function.uncurry fun (x : Mt k r) (y : Mt k r) =>
          (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) =
          tripleMatrixProduct ∘ (fun p : Mt k r × Mt k r => (p.1, minvM p.2, minvM p.1)) := by
        funext p
        rfl
      rw [e]
      exact triple_matrix_product_continuous.measurable.comp (measurable_fst.prodMk
        ((measurable_minvM.comp measurable_snd).prodMk (measurable_minvM.comp measurable_fst)))
    have hg : ∀ᵐ x ∂μW, Measure.map (fun (y : Mt k r) =>
        (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) μN = μN := by
      filter_upwards [ae_iff.mpr hW0] with x hx
      exact (hNi _ hx).map_eq
    exact hWi.skew_product hgm hg

end Meas

end PI.WBL.Cv
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Psi

variable {k r : ℕ}

def ellT (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (eI k r a) (eI k r ⟨a.val + 1, h⟩) else (g *ᵥ z) (eI k r a)

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : ell k r z g = ∑ a, ellT k r z g a := rfl

theorem uw_coordX {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z)
    (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) : (h *ᵥ y) (eI k r b) = y (eI k r b) := by
  rw [← herm_esI (h *ᵥ y) b, ← (hh.2.1 b).2, herm_inv hh.1, herm_esI]

theorem ellT_conj {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (g : Mx k r) (a : Fin r) :
    ellT k r z (h⁻¹ * g * h) a = ellT k r z g a := by
  have hh' := uw_inv hh
  have hrow : ∀ l, h⁻¹ (eI k r a) l = if eI k r a = l then 1 else 0 := fun l => by
    have h1 := uw_coordX hh' (bvec l) a
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using h1
  unfold ellT
  split_ifs with hlt
  · have hcol : ∀ l, h l (eI k r ⟨a.val + 1, hlt⟩) = if l = eI k r ⟨a.val + 1, hlt⟩ then 1 else 0 := by
      intro l
      have h1 := congrFun (hh.2.1 ⟨a.val + 1, hlt⟩).1 l
      simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using h1
    simp [Matrix.mul_apply, hcol, hrow]
  · rw [← Matrix.mulVec_mulVec, hh.2.2, ← Matrix.mulVec_mulVec, uw_coordX hh' _ a]

theorem ell_conj {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (g : Mx k r) :
    ell k r z (h⁻¹ * g * h) = ell k r z g := by
  rw [ell_eq, ell_eq]
  exact Finset.sum_congr rfl fun a _ => ellT_conj hh g a

theorem n_last {n : Mx k r} (hn : n ∈ Nset k r) {d : Fin (2 * r + k + 1) → ℂ} (hd : d ∈ lowS k r r)
    (a : Fin r) (ha : ¬ a.val + 1 < r) : (n *ᵥ d) (eI k r a) = d (eI k r a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · rw [hn.2.1 a (eI k r a) le_rfl, if_pos rfl, one_mul]
  · intro j _ hj
    by_cases hjr : r ≤ j.val
    · rw [hd j hjr, mul_zero]
    · push_neg at hjr
      have h1 := hn.2.1 ⟨j.val, hjr⟩ (eI k r a) (by simp only [eI]; omega)
      rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl, if_neg (Ne.symm hj)] at h1
      rw [h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ellT_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n m : Mx k r} (hn : n ∈ Nset k r)
    (hm : m ∈ Nset k r) (a : Fin r) : ellT k r z (n * m) a = ellT k r z n a + ellT k r z m a := by
  unfold ellT
  split_ifs with hlt
  · rw [Matrix.mul_apply]
    have hab : eI k r a ≠ eI k r ⟨a.val + 1, hlt⟩ := by
      intro h
      have h1 := congrArg Fin.val h
      simp [eI] at h1
    rw [Finset.sum_eq_add (eI k r a) (eI k r ⟨a.val + 1, hlt⟩) hab]
    · rw [hn.2.1 a (eI k r a) le_rfl, if_pos rfl, one_mul,
        hm.2.1 ⟨a.val + 1, hlt⟩ (eI k r ⟨a.val + 1, hlt⟩) le_rfl, if_pos rfl, mul_one, add_comm]
    · intro c _ hc
      by_cases hcb : a.val + 1 ≤ c.val
      · rw [hm.2.1 ⟨a.val + 1, hlt⟩ c hcb, if_neg hc.2, mul_zero]
      · push_neg at hcb
        have hcr : c.val < r := by omega
        have h1 := hn.2.1 ⟨c.val, hcr⟩ (eI k r a) (by simp only [eI]; omega)
        rw [show eI k r ⟨c.val, hcr⟩ = c from Fin.ext rfl, if_neg (Ne.symm hc.1)] at h1
        rw [h1, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hd := n_on_Wb hm hz
    have hz0 : z (eI k r a) = 0 := hz _ (Or.inl (by simp [eI]))
    have key : n *ᵥ (m *ᵥ z) = n *ᵥ z + n *ᵥ (m *ᵥ z - z) := by
      rw [← Matrix.mulVec_add]
      congr 1
      abel
    rw [← Matrix.mulVec_mulVec, key, Pi.add_apply, n_last hn hd a hlt, Pi.sub_apply, hz0, sub_zero]

theorem ell_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n m : Mx k r} (hn : n ∈ Nset k r)
    (hm : m ∈ Nset k r) : ell k r z (n * m) = ell k r z n + ell k r z m := by
  rw [ell_eq, ell_eq, ell_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => ellT_mul hz hn hm a

theorem ell_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : ell k r z 1 = 0 := by
  rw [ell_eq]
  apply Finset.sum_eq_zero
  intro a _
  unfold ellT
  split_ifs with hlt
  · rw [Matrix.one_apply, if_neg]
    intro h
    have h1 := congrArg Fin.val h
    simp [eI] at h1
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [eI]))

theorem psi_add (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {g g' g'' : Mx k r}
    (h : ell k r z g = ell k r z g' + ell k r z g'') :
    psi k r z c g = psi k r z c g' * psi k r z c g'' := by
  unfold psi
  rw [h, mul_add, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem psiAll : PsiAll := by
  intro k r z c hz
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h0 : ∀ g, ell k 0 z g = 0 := fun g => by simp [ell_eq]
    refine ⟨fun n _ m _ => ?_, fun h _ n _ => ?_, fun h _ n _ => ?_, fun n _ => ?_⟩ <;> simp [psi, h0]
  have hunitW : ∀ h ∈ UWset k r z, IsUnit h.det := fun h hh => by
    by_contra hdet
    have h0 : h⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit h hdet
    have h1 := congrFun ((uw_inv hh).2.1 ⟨0, hr⟩).1 (eI k r ⟨0, hr⟩)
    rw [h0, Matrix.zero_mulVec] at h1
    simp [bvec] at h1
  have hunitN : ∀ n ∈ Nset k r, IsUnit n.det := fun n hn => by
    by_contra hdet
    have h0 : n⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit n hdet
    have h1 := (n_inv hn).2.1 ⟨0, hr⟩ (eI k r ⟨0, hr⟩) le_rfl
    rw [h0, if_pos rfl] at h1
    simp at h1
  refine ⟨fun n hn m hm => psi_add z c (ell_mul hz hn hm), fun h hh n hn => ?_, fun h hh n hn => ?_,
    fun n hn => ?_⟩
  · unfold psi
    rw [ell_conj hh n]
  · have hh' := uw_inv hh
    have hinv : (h⁻¹)⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h (hunitW h hh)
    have h1 := ell_conj hh' n
    rw [hinv] at h1
    unfold psi
    rw [h1]
  · have h1 : ell k r z (n * n⁻¹) = ell k r z n + ell k r z n⁻¹ := ell_mul hz hn (n_inv hn)
    rw [Matrix.mul_nonsing_inv n (hunitN n hn), ell_one hz] at h1
    have h2 : ell k r z n⁻¹ = -ell k r z n := by linear_combination (-1 : ℂ) * h1
    unfold psi
    rw [h2, mul_neg, Complex.neg_re, Complex.ofReal_neg, mul_neg]
    show _ = (starRingEnd ℂ) _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]

end Psi

end PI.WBL.Cv
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFdeg
section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

theorem fdegH_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μG : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {d : ℝ}
    (hS : 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w : H} (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, h⟩ := hS
  obtain ⟨_, heq⟩ := h w w w w
  have h1 : ∀ x : Mt k r, ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ =
      ((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← h1]
      rw [heq, inner_self_eq_norm_sq_to_K, Complex.ofReal_div, Complex.ofReal_pow]
      ring_nf
      try exact mul_comm _ _
    exact_mod_cast h3
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  show ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = d
  rw [hR]
  field_simp

end PI.WBL.FSW
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSWeil
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Weil

variable {k r : ℕ}

def psiMap (q : Mt k r × (Mt k r × Mt k r)) : Mt k r := fun i j => (sM q.2 * Matrix.of q.1) i j

theorem continuous_psiMap : Continuous (psiMap (k := k) (r := r)) := by
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (sM q.2 * Matrix.of q.1 : Mx k r) :=
    ((PI.WUN.continuous_of.comp (continuous_fst.comp continuous_snd)).matrix_mul
      (PI.WUN.continuous_of.comp (continuous_snd.comp continuous_snd))).matrix_mul
      (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem measurable_psiMap : Measurable (psiMap (k := k) (r := r)) := continuous_psiMap.measurable

theorem continuous_mulT : Continuous fun q : Mt k r × Mt k r => (fun i j => (Matrix.of q.2 * Matrix.of q.1) i j : Mt k r) := by
  have hc : Continuous fun q : Mt k r × Mt k r => (Matrix.of q.2 * Matrix.of q.1 : Mx k r) :=
    (PI.WUN.continuous_of.comp continuous_snd).matrix_mul (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem muS_ne_zero {μG μS ν : Measure (Mt k r)} (hG0 : μG ≠ 0) (hq : IsQuotMeas μG μS ν) : μS ≠ 0 := by
  intro h0
  subst h0
  apply hG0
  have h1 := hq (fun _ => 1) measurable_const
  simpa using h1

theorem sfinite_quot {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS] (hG0 : μG ≠ 0)
    (hq : IsQuotMeas μG μS ν) : SFinite ν := by
  have hS0 := muS_ne_zero hG0 hq
  obtain ⟨f, hfpos, hfm, hfint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set F : Mt k r → ENNReal := fun x => (f x : ENNReal) with hFdef
  have hFm : Measurable F := hfm.coe_nnreal_ennreal
  have hmul : ∀ x : Mt k r, Measurable fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) :=
    fun x => (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  set h : Mt k r → ENNReal := fun x => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS with hdef
  have hhm : Measurable h := (hFm.comp continuous_mulT.measurable).lintegral_prod_right'
  have hint : ∫⁻ x, h x ∂ν < ⊤ := by
    rw [hdef, ← hq F hFm]
    exact hfint.trans ENNReal.one_lt_top
  have hpos : ∀ x, h x ≠ 0 := by
    intro x hx
    have hx' := (lintegral_eq_zero_iff (hFm.comp (hmul x))).1 hx
    have hfalse : ∀ᵐ s ∂μS, False := hx'.mono fun s hs => by
      simp only [Function.comp_apply, Pi.zero_apply, hFdef, ENNReal.coe_eq_zero] at hs
      exact (hfpos _).ne' hs
    exact hS0 (by simpa using ae_iff.1 hfalse)
  have hfin : IsFiniteMeasure (ν.withDensity h) := isFiniteMeasure_withDensity hint.ne
  have heq : ν = (ν.withDensity h).withDensity h⁻¹ := by
    rw [← withDensity_mul ν hhm hhm.inv]
    conv_lhs => rw [← withDensity_one (μ := ν)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_lt_top hhm hint.ne] with x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact (ENNReal.mul_inv_cancel (hpos x) hx.ne).symm
  rw [heq]
  infer_instance

theorem quot_map {μG μW μN ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite ν]
    (hq : IsQuotMeas μG (muSof μW μN) ν) : μG = (ν.prod (μW.prod μN)).map psiMap := by
  ext A hA
  have hf : Measurable (A.indicator (1 : Mt k r → ENNReal)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA, hq _ hf,
    lintegral_map hf measurable_psiMap,
    lintegral_prod (fun w => A.indicator 1 (psiMap w)) (hf.comp measurable_psiMap).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hf1 : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ENNReal)
      (fun i j => (Matrix.of s * Matrix.of x) i j) :=
    hf.comp (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  have hg1 : Measurable fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) :=
    (continuous_mulT.comp continuous_swap).measurable
  rw [muSof, lintegral_map hf1 hg1]
  rfl

end Weil

end PI.WBL.FSW
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SmoothStep
section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conj_mem_UJ {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hJ := hP.1.2
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * _ * (P * g * P⁻¹) = _
  have e1 : (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) =
      (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg', ← hJ]
  calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hinv']; simp

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) (g : Mx k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hinv]; simp

theorem ds_rep {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      (∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖) ∧
      ∀ v : H, ContinuousOn (fun g => σ g v) (UH (Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, -⟩ := hDS
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hinv] using h1
  · intro a ha b hb
    have h := hmul _ (conj_mem_UJ hP ha) _ (conj_mem_UJ hP hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [e, conj_back hP] at h
    exact h
  · intro a ha v
    have h := hnorm _ (conj_mem_UJ hP ha) v
    simp only [conj_back hP] at h
    exact h
  · intro v
    have hc : Continuous (fun g : Mx k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h := (hcont v).comp hc.continuousOn (fun g hg => conj_mem_UJ hP hg)
    refine h.congr (fun g _ => ?_)
    show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
    rw [conj_back hP]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end PI.WBL.FSW
end
end

