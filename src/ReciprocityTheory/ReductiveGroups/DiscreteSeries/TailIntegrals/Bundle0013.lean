module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DelFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SphericalFunctionFixedUnitaryEqOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DetEqMulMinorOfColZero

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IndexEmbeddingBijective
section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

theorem shear_mp {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) (c : ℂ) :
    MeasurePreserving (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) volume volume := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i
  have he : MeasurePreserving e volume ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i
  have h1 : MeasurePreserving (fun p : (Fin n → ℂ) × ℂ => (p.1, p.2 + c * p.1 j'))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
    refine (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).skew_product
      (g := fun x a => a + c * x j') ?_ ?_
    · exact measurable_snd.add (measurable_const.mul ((measurable_pi_apply j').comp measurable_fst))
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self (volume : Measure ℂ) (c * x j')
  have hS : MeasurePreserving (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ)))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    (Measure.measurePreserving_swap).comp (h1.comp Measure.measurePreserving_swap)
  have key : (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) =
      e.symm ∘ (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · show Function.update y i (y i + c * y j) i = y i + c * y (i.succAbove j')
      rw [hj']
      simp
    · funext m
      show Function.update y i (y i + c * y j) (i.succAbove m) = y (i.succAbove m)
      simp [Function.update_apply, Fin.succAbove_ne]
  rw [key]
  exact (MeasurePreserving.symm e he).comp (hS.comp he)

theorem fne {n : ℕ} (a b : Fin n) (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem w_ne (k r' : ℕ) (hk : 1 ≤ k) : wI k r' 0 ≠ wI k r' (Fin.last k) := by
  intro h
  have h' := congrArg Fin.val h
  simp [wI, Fin.last] at h'
  omega

def rotF (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ :=
  Function.update (Function.update y (wI k r' 0) (cc * (y (wI k r' 0) - y (wI k r' (Fin.last k)))))
    (wI k r' (Fin.last k)) (cc * (y (wI k r' 0) + y (wI k r' (Fin.last k))))

private lemma measurePreserving_update_update_cc_rotation_of_ne {N : ℕ} (a b : Fin (N + 1)) (hne : a ≠ b) :
    MeasurePreserving (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) volume volume := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = ((Real.sqrt 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hq : q ^ 2 = 2 := by
    rw [hqdef, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    norm_num at hq
  have hcc : cc = q / 2 := by
    have hinv : cc = q⁻¹ := by
      rw [hqdef]
    rw [hinv, eq_div_iff two_ne_zero, ← hq, pow_two, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  have key : (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) =
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b)) ∘
      ((fun y : Fin (N + 1) → ℂ => Function.update y b (y b + q / 2 * y a)) ∘
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b))) := by
    funext y m
    by_cases hma : m = a
    · simp [Function.update_apply, hma, hne, hne.symm, hcc]
      linear_combination (y a - (q - 2) * y b) / 2 * hq
    · by_cases hmb : m = b
      · simp [Function.update_apply, hmb, hne, hne.symm, hcc]
        linear_combination y b / 2 * hq
      · simp [Function.update_apply, hma, hmb]
  rw [key]
  exact (shear_mp a b hne _).comp ((shear_mp b a hne.symm _).comp (shear_mp a b hne _))

theorem rot_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (rotF k r') volume volume := by
  exact measurePreserving_update_update_cc_rotation_of_ne (wI k r' 0) (wI k r' (Fin.last k)) (w_ne k r' hk)

def ix2 (k r' : ℕ) : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩

theorem index_embedding_bijective (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix2 k r') := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro (a | a | a) (b | b | b) h <;>
      (have := a.isLt; have := b.isLt; simp [ix2, Fin.ext_iff] at h ⊢ <;> omega)
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

def permF (k r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ) :=
  (fun j => z (ix2 k r' (Sum.inl j)), fun j => z (ix2 k r' (Sum.inr (Sum.inl j))),
    fun i => z (ix2 k r' (Sum.inr (Sum.inr i))))

theorem perm_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (permF k r') volume volume := by
  let E := Equiv.ofBijective (ix2 k r') (index_embedding_bijective k r' hk)
  have h1 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Fin (2 * r' + k + 1) => (volume : Measure ℂ)) E)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (1 + r') ⊕ Fin (k - 1) => (volume : Measure ℂ))
  have h4 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod h3
  have h5 := h4.comp (h2.comp h1)
  first
    | exact h5
    | (convert h5 using 1; funext z; rfl)

theorem lin_eq (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    permF k r' (rotF k r' y) = ((hcoord k r' (y, 0)).1, (hcoord k r' (y, 0)).2.1, (hcoord k r' (y, 0)).2.2.1) := by
  have hne := w_ne k r' hk
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_) (funext fun i => ?_))
  · have := j.isLt
    show rotF k r' y ⟨j.val, by omega⟩ = (hcoord k r' (y, 0)).1 j
    rw [hc1 k r' hk, AN, dite_eq_left (by omega), aF]
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 :=
        Fin.ext (by simp only [wI, Fin.val_zero]; omega)
      rw [e, rotF, Function.update_of_ne hne, Function.update_self]
  · have := j.isLt
    show rotF k r' y ⟨2 * r' + k - j.val, by omega⟩ = (hcoord k r' (y, 0)).2.1 j
    rw [hc2, AN', dite_eq_left (by omega), aF']
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) :=
        Fin.ext (by simp only [wI, Fin.val_last]; omega)
      rw [e, rotF, Function.update_self]
  · have := i.isLt
    show rotF k r' y ⟨r' + i.val + 1, by omega⟩ = (hcoord k r' (y, 0)).2.2.1 i
    have n1 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
      fne _ _ (by simp only [wI, Fin.val_last]; omega)
    have n0 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
      fne _ _ (by simp only [wI, Fin.val_zero]; omega)
    rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
    try rfl

def imF (k r' : ℕ) (q : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) : ℝ :=
  (∑ j, q.2.1 j * star (q.1 j)).im

theorem imF_meas (k r' : ℕ) : Measurable (imF k r') := by
  apply Continuous.measurable
  unfold imF
  fun_prop

theorem hcoord_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (hcoord k r') volume volume := by
  have hL : MeasurePreserving (fun y => permF k r' (rotF k r' y)) volume volume :=
    (perm_mp k r' hk).comp (rot_mp k r' hk)
  have hP := hL.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hSk : MeasurePreserving
      (fun z : ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) × ℝ =>
        (z.1, z.2 + imF k r' z.1)) volume volume := by
    refine (MeasurePreserving.id
      (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)))).skew_product
      (g := fun q t => t + imF k r' q) ?_ ?_
    · exact measurable_snd.add ((imF_meas k r').comp measurable_fst)
    · exact Filter.Eventually.of_forall fun q => map_add_right_eq_self (volume : Measure ℝ) (imF k r' q)
  have hA1 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ))) (volume : Measure ℝ)
  have hA2 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure (Fin (k - 1) → ℂ)) (volume : Measure ℝ)
  have hA3 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod hA2
  have hAll := hA3.comp (hA1.comp (hSk.comp hP))
  have key : hcoord k r' = fun x : HPar k r' =>
      ((permF k r' (rotF k r' x.1)).1, (permF k r' (rotF k r' x.1)).2.1,
        (permF k r' (rotF k r' x.1)).2.2, x.2 + imF k r' (permF k r' (rotF k r' x.1))) := by
    funext x
    obtain ⟨y, t⟩ := x
    dsimp only
    rw [lin_eq k r' hk y]
    rfl
  rw [key]
  exact hAll

theorem formulaF_all : FormulaF := fun k r' hk => ⟨fun x l => del_formula k r' hk x l, hcoord_mp k r' hk⟩

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MeasurableHaarKernelTriple
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Base0

private def PhiA (k : ℕ) (A : ℝ) (g : Mt k 0) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g) ^ (-A))

private lemma phiA_ne_top (k : ℕ) (A : ℝ) (g : Mt k 0) : PhiA k A g ≠ ∞ := ENNReal.ofReal_ne_top

private lemma measurable_phiA (k : ℕ) (A : ℝ) : Measurable (PhiA k A) := by
  have hc : Continuous fun g : Mt k 0 => gN (Matrix.of g) := by
    unfold gN
    apply Continuous.sqrt
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  unfold PhiA
  exact ENNReal.measurable_ofReal.comp (hc.measurable.pow_const (-A))

private def Gf (k : ℕ) (σ : ℝ) (h g h' : Mt k 0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of h)ᴴ *ᵥ ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0)) (iW k) +
    ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)


set_option maxHeartbeats 800000 in
private lemma measurable_Gf (k : ℕ) (σ : ℝ) :
    Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => Gf k σ p.1 p.2.1 p.2.2) := by
  have hof : Continuous (fun M : Mt k 0 => (Matrix.of M : Mat k 0)) := continuous_id
  have h1 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.1 := hof.comp continuous_fst
  have h21 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.1 :=
    hof.comp (continuous_fst.comp continuous_snd)
  have h22 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.2 :=
    hof.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0 :=
    (h21.matrix_mul h22).matrix_mulVec continuous_const
  have hv : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) :=
    h1.matrix_conjTranspose.matrix_mulVec hw
  have hc : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖ :=
    continuous_const.mul ((((continuous_apply (iW k)).comp hv).add ((continuous_apply (iK k)).comp hw)).norm)
  have hm : Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => ENNReal.ofReal
      ((Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).pow_const (-σ)
  unfold Gf
  exact hm

private lemma s_facts {k : ℕ} (hk : 1 ≤ k) {s : Fin (0 + 1) → ℝ} (hs : SAdm k 0 s) :
    0 ≤ s 0 ∧ s 0 < k := by
  have h := hs 0
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp [s0] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> linarith

private lemma nsq_tr_lemma {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

private lemma gN_left_lemma_2 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

private lemma gN_right_lemma_3 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (X * κ) = gN X := by
  have hκ' : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.mp hκ
      | exact (Matrix.mul_eq_one_comm).1 hκ
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hκ
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]

private lemma phiA_inv (k : ℕ) (A : ℝ) : ∀ κ ∈ Kset k 0, ∀ g,
    PhiA k A (lmulM κ g) = PhiA k A g ∧ PhiA k A (rmulF κ g) = PhiA k A g := by
  intro κ hκ g
  have hu : κᴴ * κ = 1 := by
    simp only [Kset, Set.mem_setOf_eq] at hκ
    exact hκ.2
  refine ⟨?_, ?_⟩
  · simp only [PhiA, lmulM]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_left_lemma_2 hu (Matrix.of g))
  · simp only [PhiA, rmulF]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_right_lemma_3 hu (Matrix.of g))

private lemma avg_one {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {h h' : Mat k 0} (hh : h ∈ U0 k) (hh' : h' ∈ U0 k) :
    ∫⁻ g, PhiA k A g * FsE k 0 s (h⁻¹ * Matrix.of g * h') ∂μG = JInt μG A s := by
  rw [hT k 0 s μG (PhiA k A) hk hμG (measurable_phiA k A) (phiA_inv k A) h hh.1 h' hh'.1, sphericalFunction_fixedUnitary_eq_one hk hh,
    sphericalFunction_fixedUnitary_eq_one hk hh', mul_one, ENNReal.ofReal_one, one_mul]
  rfl

private lemma measurable_haarKernelTriple (k : ℕ) (A σ : ℝ) :
    Measurable (fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k σ q.2 q.1.2 q.1.1) := by
  have hs : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => q.1.2 := measurable_snd.comp measurable_fst
  have h1 := (measurable_phiA k A).comp hs
  have hm : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => (q.2, q.1.2, q.1.1) := by fun_prop
  have h2 := (measurable_Gf k σ).comp hm
  simp only [Function.comp_def] at h1 h2
  exact h1.mul h2

private lemma avg_key {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν)
    [IsFiniteMeasure ν] [SigmaFinite μG] :
    JInt μG A s * (ν Set.univ * ν Set.univ) =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
  have step1 : JInt μG A s * (ν Set.univ * ν Set.univ) = ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν := by
    rw [lintegral_const, lintegral_const, mul_assoc]
  have step2 : ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν =
      ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    rw [← avg_one hk hT hμG A hh hh']
    refine lintegral_congr (fun g => ?_)
    rw [fsE_avg hk hh]
    rfl
  have step3 : ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν =
      ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν := by
    refine lintegral_congr (fun h' => ?_)
    have hmap : Measurable (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    have hm : Measurable ((fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k (s 0) q.2 q.1.2 q.1.1) ∘
        (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1))) := Measurable.comp (measurable_haarKernelTriple k A (s 0)) hmap
    exact lintegral_lintegral_swap hm.aemeasurable
  have step4 : ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν =
      ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG :=
    lintegral_lintegral_swap (Measurable.lintegral_prod_right' (measurable_haarKernelTriple k A (s 0))).aemeasurable
  have step5 : ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
    refine lintegral_congr (fun g => ?_)
    rw [← lintegral_const_mul' _ _ (phiA_ne_top k A g)]
    refine lintegral_congr (fun h' => ?_)
    rw [lintegral_const_mul' _ _ (phiA_ne_top k A g)]
  rw [step1, step2, step3, step4, step5]

private lemma ptw {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 ≤ σ) {ν : Measure (Mt k 0)}
    (hν : IsHaarOn (U0 k) ν) (hK1f : C0 k σ ν + ν Set.univ ≠ ∞) (g : Mt k 0)
    (hg : (Matrix.of g : Mat k 0) ∈ GV k 0) :
    ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν ≤
      (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := by
  have hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hws := outer_ws hg
  have hgkk : 1 ≤ ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    have h1 : 1 ≤ Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := by
      nlinarith [sq_nonneg (tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))]
    rw [← Complex.sq_norm] at h1
    nlinarith [norm_nonneg ((Matrix.of g : Mat k 0) (iK k) (iK k))]
  have hbn : ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ = ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    rw [norm_neg, norm_star]
  have hb0 : -star ((Matrix.of g : Mat k 0) (iK k) (iK k)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hbn; linarith
  have hvb : tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)) ^ 2 ≤
      Complex.normSq (-star ((Matrix.of g : Mat k 0) (iK k) (iK k))) := by
    have : Complex.normSq (star ((Matrix.of g : Mat k 0) (iK k) (iK k))) =
        Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := Complex.normSq_conj _
    rw [Complex.normSq_neg, this]; linarith
  calc ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν
      ≤ ∫⁻ h', ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
          ‖((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖ / 2) ^ (-σ) *
            (C0 k σ ν + ν Set.univ) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        obtain ⟨e, hne⟩ := iso_y hk hg hh'.1
        unfold Gf
        exact bnd hk hν hσ (lam := (Real.sqrt 2)⁻¹) (by positivity)
          ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) _ hne (le_of_eq e)
    _ = (∫⁻ h', ENNReal.ofReal (1 / 4 * ‖((Matrix.of h')ᴴ *ᵥ (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))
          (iW k) + -star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖) ^ (-σ) ∂ν) * (C0 k σ ν + ν Set.univ) := by
        rw [lintegral_mul_const' _ _ hK1f]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        rw [outer_eq hk hh' (Matrix.of g)]
        congr 2
        rw [← mul_assoc, hc2]; ring
    _ ≤ (ENNReal.ofReal (1 / 4 * ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ / 2) ^ (-σ) *
          (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (bnd hk hν hσ (by norm_num) _ _ hb0 hvb) le_rfl
    _ ≤ (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (mul_le_mul' (ofReal_rpow_neg_anti hσ (by rw [hbn]; linarith)) le_rfl) le_rfl
    _ = (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := mul_comm _ _

theorem aStepBase_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) : AStepBase := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, hGN, -, -, -, -, -, -, -, -, hHW, -⟩ := hB2
  intro k hk s hs μG hμG A hA
  obtain ⟨hσ0, hσk⟩ := s_facts hk hs
  obtain ⟨ν, hν⟩ := hHW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hν' : IsHaarOn (U0 k) ν := hν
  have hνf := haar_univ_lt_top hCW hν'
  have hν0 : ν Set.univ ≠ 0 := fun h => hν.ne_zero (Measure.measure_univ_eq_zero.mp h)
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμG.finite_compact K hK⟩
  have hC0 := haarIntegralConstant_lt_top hk hν' hνf hσ0 hσk
  have hK1f : C0 k (s 0) ν + ν Set.univ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC0.ne, hνf.ne⟩
  have hKc : (C0 k (s 0) ν + ν Set.univ) *
      (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ)) ≠ ∞ := by
    refine ENNReal.mul_ne_top hK1f (ENNReal.mul_ne_top ?_ hK1f)
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]; exact ENNReal.ofReal_ne_top
  have key := avg_key hk hT (s := s) hμG A hν'
  have hfin : ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG < ∞ := by
    calc ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG
        ≤ ∫⁻ g, PhiA k A g * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) ∂μG := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμG.conc] with g hg
          exact mul_le_mul' le_rfl (ptw hk hσ0 hν' hK1f g (not_not.mp hg))
      _ = (∫⁻ g, PhiA k A g ∂μG) * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) :=
          lintegral_mul_const' _ _ hKc
      _ < ∞ := ENNReal.mul_lt_top (hGN k 0 μG A hμG hA) hKc.lt_top
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_mul (mul_ne_zero hν0 hν0)] at key
  rw [← key] at hfin
  exact lt_irrefl _ hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Phi2
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def phi2 (k r' : ℕ) (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  ιLev k 1 r' (Hpk k r') *ᵥ phiV k (1 + r') a

def Yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  (heis0 k r' x)⁻¹ *ᵥ phi2 k r' a

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

