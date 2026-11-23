module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ByParts
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem kByParts {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ε : Fin n → Bool) (F D : KG ε → E) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Z)) (hF : Continuous F) (hD : Continuous D)
    (hder : ∀ k, HasDerivAt (fun t => F (k * γ t)) (D k) 0) :
    ∫ k, D k ∂(muK ε) = 0 := by
  haveI := muK_rightInvariant ε
  haveI := compactSpace_KG ε
  obtain ⟨γ', -, hγ', hadd'⟩ := exists_oneParam ε hZ
  have hinj : ∀ a b : KG ε, toMK a = toMK b → a = b := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Units.ext h))
  have hγγ : ∀ t, γ t = γ' t := fun t => hinj _ _ (by rw [hγ, hγ'])
  have hadd : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    rw [hγγ, hγγ, hγγ, hadd']
  have h0 : γ 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (a := γ 0) (by rw [mul_one]; exact h00.symm)

  have hderiv : ∀ k t, HasDerivAt (fun u => F (k * γ u)) (D (k * γ t)) t := by
    intro k t
    have h1 := hder (k * γ t)
    have h2 : (fun s => F (k * γ t * γ s)) = fun s => F (k * γ (t + s)) := by
      funext s
      rw [hadd, mul_assoc]
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
    have h4 : (fun x => F (k * γ (t + (x - t)))) = fun u => F (k * γ u) := by
      funext x
      rw [show t + (x - t) = x by ring]
    rw [h4] at h3
    exact h3
  obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖D k‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range hD.norm).bddAbove
    exact ⟨C, fun k => hC ⟨k, rfl⟩⟩
  have hFm : ∀ t, Continuous fun k : KG ε => F (k * γ t) := fun t =>
    hF.comp (continuous_mul_const _)
  have hDm : Continuous fun k : KG ε => D (k * γ 0) := hD.comp (continuous_mul_const _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε)
    (F := fun t k => F (k * γ t)) (F' := fun t k => D (k * γ t)) (x₀ := (0 : ℝ))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((hFm t).stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    ((hFm 0).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)
    ((hDm.stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    (ae_of_all _ fun k t _ => hC _) (integrable_const C)
    (ae_of_all _ fun k t _ => hderiv k t)
  have key2 : HasDerivAt (fun t => ∫ k, F (k * γ t) ∂(muK ε)) (∫ k, D (k * γ 0) ∂(muK ε)) 0 :=
    key.2
  have hconst : (fun t => ∫ k, F (k * γ t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self (fun k => F k) (γ t)
  rw [hconst] at key2
  have huniq := key2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simpa [h0] using huniq

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChain
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eabV_of_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W)
    (hgu : inUJ ε g) :
    EabV ε a b f g = -(Lhol (Matrix.single a b 1) F (g⁻¹ * m)) := by
  have h1 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart1 ε (Matrix.single a b 1)) hg hgu
  have h2 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart2 ε (Matrix.single a b 1)) hg hgu
  simp only [EabV, EcV, RdV, Lhol]
  rw [h1.deriv, h2.deriv]
  conv_rhs => rw [← ccb_cpart_sum ε (Matrix.single a b 1)]
  rw [add_mul, smul_mul_assoc, map_add (f := _), map_smul, smul_neg, neg_add]

theorem contDiffOn_of_local [CompleteSpace E] {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) : ContDiffOn ℝ ∞ (fun g => F (g⁻¹ * m)) W := by
  classical
  have hent : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) := by
    intro i j
    fun_prop
  have hdet : ∀ {G : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ},
      (∀ i j, ContDiff ℂ ∞ (fun A => G A i j)) → ContDiff ℂ ∞ (fun A => (G A).det) := by
    intro G hG
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    exact contDiff_prod fun i _ => hG _ _
  have hadj : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate i j) := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine hdet fun k l => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact hent k l
  have hinv : ContDiffOn ℂ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W := by
    intro g hg
    have hdg : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp (hWV g hg).1).ne_zero
    have hid : ContDiffAt ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) g :=
      ((hdet fun i j => hent i j).contDiffAt).inv hdg
    refine ContDiffAt.contDiffWithinAt ?_
    refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
    simp only [Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact ContDiffAt.sum fun k _ => (hid.mul (hadj i k).contDiffAt).mul contDiffAt_const
  have hFc : ContDiffOn ℂ ∞ F V := cca_contDiffOn hV hF
  have hc : ContDiffOn ℂ ∞ (F ∘ fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W :=
    hFc.comp hinv fun g hg => (hWV g hg).2
  exact hc.restrict_scalars ℝ

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem op_inv_eq_adjoint (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  rw [KType.op, map_inv, ← ContinuousLinearMap.star_eq_adjoint]
  first
  | rfl
  | simp [Unitary.star_eq_inv]
  | simp [unitary.star_eq_inv]

private lemma commute_Jm_of_isBlock {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    Y * Jm ε = Jm ε * Y := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · simp [hY a b h]

lemma block_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inK ε A ∧ inK ε B ∧ X = A + Complex.I • B ∧
      Xᴴ = -A + Complex.I • B := by
  have hXH : IsBlock ε Xᴴ := fun a b h => by
    rw [Matrix.conjTranspose_apply, hX b a (Ne.symm h), star_zero]
  have hc1 := commute_Jm_of_isBlock hX
  have hc2 := commute_Jm_of_isBlock hXH
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
    norm_num
  have hIB : Complex.I • ((-Complex.I / 2) • (X + Xᴴ)) = (1 / 2 : ℂ) • (X + Xᴴ) := by
    rw [smul_smul, hI]
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by simp
  refine ⟨(1 / 2 : ℂ) • (X - Xᴴ), (-Complex.I / 2) • (X + Xᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hs1, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hs2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
  · rw [hIB]
    module
  · rw [hIB]
    module

lemma inK_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) : inK ε (-A) := by
  refine ⟨?_, by rw [neg_mul, mul_neg, hA.2]⟩
  have h := hA.1
  unfold inG at h ⊢
  rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, h, neg_zero]

lemma gamma_zero {γ : ℝ → KG ε} (hmul : ∀ s t, γ (s + t) = γ s * γ t) : γ 0 = 1 := by
  simpa using hmul 0 0

lemma dtau_skew (T : KType ε Λ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    ContinuousLinearMap.adjoint (T.dτ A) = -T.dτ A := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hA
  have h0 := gamma_zero hmul
  have hinv : ∀ t, γ (-t) = (γ t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_left (by rw [← hmul, neg_add_cancel, h0])
  have h1 := T.hasDeriv A hA γ hγ
  have h2 := T.hasDeriv (-A) (inK_neg hA) (fun t => γ (-t)) (fun t => by
    rw [hγ]; congr 1; push_cast; rw [neg_smul, smul_neg])
  have h3 := h1.star
  simp only [ContinuousLinearMap.star_eq_adjoint] at h3
  have e : (fun t => ContinuousLinearMap.adjoint (T.op (γ t))) = fun t => T.op (γ (-t)) :=
    funext fun t => by rw [← op_inv_eq_adjoint, hinv]
  rw [e] at h3
  rw [h3.unique h2, map_neg]

theorem dtau_adj (T : KType ε Λ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ContinuousLinearMap.adjoint (T.dτ X) = T.dτ Xᴴ := by
  obtain ⟨A, B, hA, hB, hX1, hX2⟩ := block_decomp hX
  rw [hX2, hX1]
  simp [map_add (f := _), map_neg, map_smul, LinearIsometryEquiv.map_smulₛₗ, dtau_skew T hA, dtau_skew T hB,
    Complex.conj_I]

lemma inK_conj (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    inK ε (toMK k * A * toMK k⁻¹) := by
  have hk : toMK k ∈ unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := k.2
  have hk' : toMK k⁻¹ ∈ unitaryGroup (Fin n) ℂ ∧ toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := (k⁻¹).2
  have e : toMK k * toMK k⁻¹ = 1 := by
    unfold toMK toM
    simp
  have hu : (toMK k)ᴴ * toMK k = 1 := by
    have h1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using h1
  have hUV : (toMK k)ᴴ = toMK k⁻¹ := by
    calc (toMK k)ᴴ = (toMK k)ᴴ * (toMK k * toMK k⁻¹) := by rw [e, Matrix.mul_one]
      _ = toMK k⁻¹ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hV : (toMK k⁻¹)ᴴ = toMK k := by
    rw [← hUV, Matrix.conjTranspose_conjTranspose]
  have hUJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, toMK k * (Jm ε * Y) = Jm ε * (toMK k * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]
  have hVJ : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := hk'.2
  have hA1 := hA.1
  unfold inG at hA1
  have hAJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Aᴴ * (Jm ε * Y) = -(Jm ε * (A * Y)) := by
    intro Y
    rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hA1, Matrix.neg_mul, Matrix.mul_assoc]
  have hAc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, A * (Jm ε * Y) = Jm ε * (A * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hA.2, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV, hUV]
    simp only [Matrix.mul_assoc, hVJ, hAJ, Matrix.mul_neg, hUJ, neg_add_cancel]
  · simp only [Matrix.mul_assoc, hVJ, hAc, hUJ]

lemma dtau_conj_inK (T : KType ε Λ) (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    T.op k * T.dτ A * T.op k⁻¹ = T.dτ (toMK k * A * toMK k⁻¹) := by
  obtain ⟨γ, -, hγ, -⟩ := exists_oneParam ε hA
  have h1 := ((T.hasDeriv A hA γ hγ).const_mul (T.op k)).mul_const (T.op k⁻¹)
  have h2 := T.hasDeriv _ (inK_conj k hA) (fun t => k * γ t * k⁻¹) (fun t => by
    have e : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e, hγ, show ((t : ℂ) • (toMK k * A * toMK k⁻¹)) = toMK k * ((t : ℂ) • A) * toMK k⁻¹ by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact (Matrix.exp_units_conj ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).symm)
  have e : (fun t => T.op (k * γ t * k⁻¹)) = fun t => T.op k * T.op (γ t) * T.op k⁻¹ :=
    funext fun t => by simp only [KType.op, map_mul]; rfl
  rw [e] at h2
  exact h1.unique h2

theorem dtau_conj (T : KType ε Λ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    T.op k * T.dτ X * T.op k⁻¹ = T.dτ (toMK k * X * toMK k⁻¹) := by
  obtain ⟨A, B, hA, hB, hX1, -⟩ := block_decomp hX
  subst hX1
  have e1 : toMK k * (A + Complex.I • B) * toMK k⁻¹ =
      toMK k * A * toMK k⁻¹ + Complex.I • (toMK k * B * toMK k⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, map_add (f := _), map_smul, map_add (f := _), map_smul, ← dtau_conj_inK T k hA, ← dtau_conj_inK T k hB,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

theorem hasDerivAt_op (T : KType ε Λ) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => T.op (k * γ t)) (T.op k * T.dτ Y) 0 := by
  have h1 := T.hasDeriv Y hY γ hγ
  have e : (fun t => T.op (k * γ t)) = fun t => T.op k * T.op (γ t) := by
    funext t
    exact congrArg Subtype.val (map_mul T.τ k (γ t))
  rw [e]
  exact h1.const_mul (T.op k)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsB
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma dm_swap4 (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := by
  calc ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ k, ∑ a, ∑ l, ∑ b, F k l a b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ a, ∑ k, ∑ l, ∑ b, F k l a b := Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ b, ∑ l, F k l a b :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}

lemma dm_Ye (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y a b = ∑ j, U a j * (y j : ℂ) * star (U b j) := by
  rw [hY, dm_entry]

lemma dm_herm (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y b a = star (Y a b) := by
  rw [dm_Ye hY, dm_Ye hY, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

lemma trace_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, (y k : ℂ) * dmK U i k k = ∑ a, dmChi i a * Y a a := by
  simp only [dmK, Finset.mul_sum, dm_Ye hY]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma trace_sq_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, dmChi i a * dmChi i b * (Y b a * Y a b) := by
  have hL : ∀ k l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, (y k : ℂ) * (y l : ℂ) *
        ((dmChi i a * (star (U a k) * U a l)) * (dmChi i b * (star (U b l) * U b k))) := by
    intro k l
    rw [dmK, dmK, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hR : ∀ a b, dmChi i a * dmChi i b * (Y b a * Y a b) =
      ∑ k, ∑ l, dmChi i a * dmChi i b *
        ((U b k * (y k : ℂ) * star (U a k)) * (U a l * (y l : ℂ) * star (U b l))) := by
    intro a b
    rw [dm_Ye hY b a, dm_Ye hY a b, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  simp only [hL, hR]
  rw [dm_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma trace_pow_two_diag_conj (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (i : ℕ) :
    ∑ k, (y k : ℂ) ^ 2 * dmK U i k k = ∑ a, dmChi i a * ∑ b, Y a b * Y b a := by
  have hYY : Y * Y = U * Matrix.diagonal (fun j => (y j : ℂ) ^ 2) * Uᴴ := by
    rw [hY]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, dm_UhU hU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have hrow : ∀ a, ∑ b, Y a b * Y b a = ∑ k, U a k * (y k : ℂ) ^ 2 * star (U a k) := by
    intro a
    rw [← Matrix.mul_apply, hYY, dm_entry]
  simp only [hrow, dmK, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma dm_S (J : Finset (Fin n)) : ((∑ j ∈ J, y j : ℝ) : ℂ) = ∑ k, dmInd J k * (y k : ℂ) := by
  push_cast
  unfold dmInd
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma dm_mean (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) = 0 := by
  simp only [dm_S, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * (y k : ℂ)) =
      (y k : ℂ) * dmK U i k k := by
    intro k
    rw [← sum_minorWeights_indicator hU hi k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring
  simp only [h, trace_diag_conj_eq hY, hd, mul_zero, Finset.sum_const_zero]

lemma dm_var (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2 =
      ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
  calc ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2
        = ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ k, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [dm_S, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = ∑ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ J : {J : Finset (Fin n) // J.card = i},
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
            if k = l then dmK U i k k else 0) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← dm_m hU hi k l, Finset.mul_sum]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
    _ = (∑ k, (y k : ℂ) * dmK U i k k) * (∑ l, (y l : ℂ) * dmK U i l l) -
          ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
          ∑ k, (y k : ℂ) ^ 2 * dmK U i k k := by
          have hk : ∀ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
              if k = l then dmK U i k k else 0) =
              ∑ l, ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
              ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) + (y k : ℂ) ^ 2 * dmK U i k k := by
            intro k
            have e : ∀ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
                if k = l then dmK U i k k else 0) =
                ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
                (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
                if k = l then (y k : ℂ) ^ 2 * dmK U i k k else 0 := by
              intro l
              split_ifs with h
              · subst h; ring
              · ring
            rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
          rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
          rw [trace_diag_conj_eq hY, trace_sq_diag_conj_eq hY, trace_pow_two_diag_conj hU hY]
          simp only [hd, mul_zero, Finset.sum_const_zero, zero_sub]
          have e : ∀ a b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
              dmChi i a * (Y a b * Y b a) - dmChi i a * dmChi i b * (Y b a * Y a b) := by
            intro a b; ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring

lemma dm_rhs (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
      ((∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  conv_lhs => rw [Finset.sum_comm]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : (b : ℕ) < i <;> by_cases ha : (a : ℕ) < i
  · rw [if_neg (fun h => absurd h.2 (not_le.mpr ha))]; simp [dmChi, hb, ha]
  · rw [if_pos ⟨hb, not_lt.mp ha⟩, dm_normsq, ← dm_herm hY a b]
    simp only [dmChi, if_pos hb, if_neg ha]; ring
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

