module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLineA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyTB
section
noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA

variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem ext_all (hE : Ext) [Fintype A] [Fintype B] {p : PV ι A B} (hp : IsInv p) (M : Matrix ι ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
  have key : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 →
      eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
    intro M hM
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h1 : M⁻¹ * (M.transpose).transpose = 1 := by
      rw [Matrix.transpose_transpose]; exact Matrix.nonsing_inv_mul M hu
    have hq := hE ι A B p hp M⁻¹ M.transpose h1
    conv_lhs => rw [← hq]
    rw [eval_sub, act_act, Matrix.nonsing_inv_mul M hu]
  let F : ℂ → ℂ := fun t => eval (act (M + t • 1) ((M + t • 1).map star) z) p -
    eval (act 1 ((M + t • (1 : Matrix ι ι ℂ)).transpose * (M + t • 1).map star) z) p
  have c1 : Continuous fun t : ℂ => M + t • (1 : Matrix ι ι ℂ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hF : Continuous F :=
    (continuous_act_eval c1 (c1.matrix_map continuous_star) z p).sub
      (continuous_act_eval continuous_const (c1.matrix_transpose.mul (c1.matrix_map continuous_star)) z p)
  let S := {t : ℂ | (Matrix.charpoly (-M)).IsRoot t}
  have hS : S.Countable := (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-M)).ne_zero).countable
  have hd : Dense Sᶜ := hS.dense_compl ℂ
  have hz : Set.EqOn F (fun _ => 0) Sᶜ := by
    intro t ht
    have hdet : (M + t • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
      intro h0
      apply ht
      show (Matrix.charpoly (-M)).eval t = 0
      rw [Matrix.eval_charpoly]
      have e : Matrix.scalar ι t - -M = M + t • (1 : Matrix ι ι ℂ) := by
        rw [sub_neg_eq_add, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_comm]
      rw [e]; exact h0
    simp only [F, key _ hdet, sub_self]
  have h0 := congrFun (hF.ext_on hd continuous_const hz) 0
  simp only [F, zero_smul, add_zero] at h0
  exact sub_eq_zero.mp h0

theorem pair_inv {q : PV ι A B} (hq : q ∈ pairAlg ι A B) : IsInv q := by
  intro u hu
  have hu' : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hle : pairAlg ι A B ≤ AlgHom.equalizer (sub u (u.map star)) (AlgHom.id ℂ (PV ι A B)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show sub u (u.map star) _ = _
    apply MvPolynomial.funext
    intro z
    rw [eval_sub]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_X, act, Sum.elim_inl, Sum.elim_inr, Matrix.map_apply, AlgHom.id_apply]
    have e : ∀ i, (∑ j, u i j * z (Sum.inl (j, a))) * (∑ l, star (u i l) * z (Sum.inr (l, b))) =
        ∑ j, ∑ l, (star (u i l) * u i j) * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro i
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e2 : ∀ l, ∑ i, star (u i l) * u i j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) =
        (star u * u) l j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro l
      rw [Matrix.mul_apply, Finset.sum_mul]
      rfl
    simp_rw [e2, hu', Matrix.one_apply]
    simp
  exact hle hq

theorem gip_integrable (hP : Pos) [Fintype A] [Fintype B] (f g : PV ι A B) :
    Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  have hG : Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ => Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := by fun_prop
  have hc : ∀ f g : PV ι A B, Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := fun f g =>
    ((MvPolynomial.continuous_eval f).mul ((MvPolynomial.continuous_eval g).star)).mul hG
  have h1 : ∀ f : PV ι A B, Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z f) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro f
    by_cases hf : f = 0
    · subst hf; simp
    · by_contra hn
      have h := (hP ι A B 1 Matrix.PosSemidef.one f).2.2 Matrix.PosDef.one hf
      rw [sub_one_one, gip, integral_undef hn] at h
      simp at h
  refine Integrable.mono' ((h1 f).norm.add (h1 g).norm) (hc f g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  have ha := norm_nonneg (eval z f)
  have hb := norm_nonneg (eval z g)
  have hcn := norm_nonneg (Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)))
  nlinarith [mul_nonneg hcn (sq_nonneg (‖eval z f‖ - ‖eval z g‖)), mul_nonneg (mul_nonneg ha hb) hcn]

def gipL (hP : Pos) [Fintype A] [Fintype B] (p : PV ι A B) : PV ι A B →ₗ[ℂ] ℂ where
  toFun q := gip q p
  map_add' q1 q2 := by
    simp only [gip, map_add (f := _), add_mul]
    exact integral_add (gip_integrable hP q1 p) (gip_integrable hP q2 p)
  map_smul' c q := by
    simp only [gip, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring

theorem exists_points {σ : Type} [Fintype σ] (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ c : (σ → ℂ) →₀ ℂ, ∀ q : W, ℓ q = c.sum fun z a => a * eval z (q : MvPolynomial σ ℂ) := by
  let ev : (σ → ℂ) → Module.Dual ℂ W := fun z => (MvPolynomial.aeval z).toLinearMap.comp W.subtype
  have hev : ∀ z (q : W), ev z q = eval z (q : MvPolynomial σ ℂ) := fun z q => by
    simp [ev]
  set S := Submodule.span ℂ (Set.range ev)
  have hco : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : MvPolynomial σ ℂ) = 0 := MvPolynomial.funext fun z => by
      rw [map_zero, ← hev]
      exact hw _ (Submodule.subset_span ⟨z, rfl⟩)
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    rw [hco, finrank_bot, add_zero] at h
    exact Submodule.eq_top_of_finrank_eq (h.trans (Subspace.dual_finrank_eq).symm)
  have hℓ : ℓ ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hℓ
  refine ⟨c, fun q => ?_⟩
  rw [← hc, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [LinearMap.smul_apply, hev, smul_eq_mul]

end PositivityTheory.Rg.Sw.FFTSteps.AsmA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousPhi
section
noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

abbrev Sg (ι A B : Type) := (ι × A) ⊕ (ι × B)

def Phi (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Sg ι A B → ℂ :=
  Sum.elim (fun x => z (Sum.inl x)) (fun y => ∑ j, g y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g : Matrix ι ι ℂ) (f : PV ι A B) (z : Sg ι A B → ℂ) :
    eval z (sub 1 g f) = eval (Phi g z) f := by
  have h : (eval z).comp (sub (A := A) (B := B) 1 g).toRingHom = eval (Phi g z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sub]
    · intro s
      rcases s with ⟨i, a⟩ | ⟨i, b⟩
      · simp [sub, Phi, Matrix.one_apply]
      · simp [sub, Phi]
  exact RingHom.congr_fun h f

theorem Phi_mul (g h : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Phi (g * h) z = Phi g (Phi h z) := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp only [Phi, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem Phi_one (z : Sg ι A B → ℂ) : Phi 1 z = z := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp [Phi, Matrix.one_apply]

theorem unitary_norm (U : Matrix ι ι ℂ) (hU : star U * U = 1) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : star (U.mulVec v) ⬝ᵥ U.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU,
      Matrix.one_mulVec]
  have e1' : ∀ w : ι → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [← e1', ← e1', ← key]
  rfl

theorem norm_Phi (U : Matrix ι ι ℂ) (hU : star U * U = 1) (z : Sg ι A B → ℂ) :
    ∑ s, ‖Phi U z s‖ ^ 2 = ∑ s, ‖z s‖ ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact unitary_norm U hU fun j => z (Sum.inr (j, b))

def PhiL (g : Matrix ι ι ℂ) : (Sg ι A B → ℂ) →ₗ[ℝ] (Sg ι A B → ℂ) where
  toFun := Phi g
  map_add' z w := by
    funext s
    rcases s with x | y
    · rfl
    · simp [Phi, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext s
    rcases s with x | y
    · rfl
    · simp only [Phi, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul, Complex.real_smul]
      ring

theorem PhiL_apply (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : PhiL g z = Phi g z := rfl

theorem map_PhiL (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) :
    Measure.map (PhiL (A := A) (B := B) U) volume = volume := by
  set L := PhiL (A := A) (B := B) U
  set S : Set (Sg ι A B → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 ≤ 1}
  have hU3 : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  have himg : L '' S = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [S, Set.mem_setOf_eq, L, PhiL_apply, norm_Phi U hU1] at hw ⊢
      exact hw
    · intro hz
      refine ⟨Phi (star U) z, ?_, ?_⟩
      · simp only [S, Set.mem_setOf_eq, norm_Phi (star U) hU3]
        exact hz
      · simp only [L, PhiL_apply, ← Phi_mul, hU2, Phi_one]
  have hpos : 0 < volume S := by
    have hopen : IsOpen {z : Sg ι A B → ℂ | ∑ s, ‖z s‖ ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨0, by simp⟩) (measure_mono fun z hz => show ∑ s, ‖z s‖ ^ 2 ≤ 1 from le_of_lt hz)
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Sg ι A B → ℂ)) (r := 1)).ne
      (measure_mono fun z hz => ?_)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    have h1 : ‖z s‖ ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (f := fun s => ‖z s‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ s)) hz
    nlinarith [norm_nonneg (z s)]
  have hdet : |LinearMap.det L| = 1 := by
    have h := Measure.addHaar_image_linearMap (volume : Measure (Sg ι A B → ℂ)) L S
    rw [himg] at h
    have h' : ENNReal.ofReal |LinearMap.det L| * volume S = 1 * volume S := by rw [← h, one_mul]
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact (ENNReal.ofReal_eq_one).1 this
  have hne : LinearMap.det L ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]

theorem integral_Phi (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (H : (Sg ι A B → ℂ) → ℂ) (hH : Continuous H) :
    ∫ z, H z = ∫ z, H (Phi U z) := by
  have hL : Continuous (PhiL (A := A) (B := B) U) := LinearMap.continuous_of_finiteDimensional _
  conv_lhs => rw [← map_PhiL (A := A) (B := B) U hU1 hU2]
  rw [integral_map hL.measurable.aemeasurable hH.aestronglyMeasurable]
  rfl

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFTB
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem sum_blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (blk ε β v a.1 b) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (v a j) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (v a j) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_star (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (star (blk ε β v a.1 b)) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (star (v a j)) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (star (v a j)) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_other (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (i : Fin n)
    (t : Bool) (st : Bool) :
    ∑ b, C (if st then star (blk ε β v a b) else blk ε β v a b) * (X (b, i, t) : PX m n) = X (a, i, t) := by
  simp only [blk_of_not β v ha]
  cases st <;> simp [apply_ite star, ite_mul]

theorem act_emb_same (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β) = (emb ε β).comp (sub v (v.map star)) := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [act, emb, sub, jv, sum_blk, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    · simpa [act, emb, sub, jv, map_sum] using sum_blk_star (n := n) β v i a true

theorem act_emb_other (β β' : Bool) (hne : β' ≠ β) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β') = emb ε β' := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a false false
    simp only [Bool.false_eq_true, if_false] at this
    simp [act, emb, jv, this]
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a true true
    simp only [if_true] at this
    simpa [act, emb, jv] using this

theorem emb_pair (β : Bool) (a b : Fin n) :
    emb ε β (∑ i : Rw ε β, (X (Sum.inl (i, a)) : PV (Rw ε β) (Fin n) (Fin n)) * X (Sum.inr (i, b))) = Qb ε β b a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, emb, rename_X, jv, Sum.elim_inl, Sum.elim_inr, Qb]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Fin m => ε x = β)) (p := fun x => ε x = β) (by simp)]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem emb_pairAlg (β : Bool) {p : PV (Rw ε β) (Fin n) (Fin n)} (hp : p ∈ pairAlg (Rw ε β) (Fin n) (Fin n)) :
    emb ε β p ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have h1 : emb ε β p ∈ (pairAlg (Rw ε β) (Fin n) (Fin n)).map (emb ε β) := Subalgebra.mem_map.2 ⟨p, hp, rfl⟩
  rw [pairAlg, AlgHom.map_adjoin] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
  exact ⟨(β, b, a), (emb_pair β a b).symm⟩

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLineB
section
noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates

variable {m n : ℕ}

lemma continuous_evX (P : PX m n) : Continuous (fun x : Fin m → Fin n → ℂ => evX P x) := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  by_cases h : k.2.2
  · simp only [h, if_true]
    exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · simp only [h]
    exact (continuous_apply k.2.1).comp (continuous_apply k.1)

lemma evX_bound (P : PX m n) : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x, ‖evX P x‖ ≤ C * (1 + sq x) ^ N := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨‖a‖, norm_nonneg _, 0, fun x => by simp [evX]⟩
  | add p q hp hq =>
    obtain ⟨C1, h1, N1, hp⟩ := hp
    obtain ⟨C2, h2, N2, hq⟩ := hq
    refine ⟨C1 + C2, by positivity, max N1 N2, fun x => ?_⟩
    have hs : 1 ≤ 1 + sq x := by linarith [sq_nonneg' x]
    have e1 : (1 + sq x) ^ N1 ≤ (1 + sq x) ^ (max N1 N2) := pow_le_pow_right₀ hs (le_max_left _ _)
    have e2 : (1 + sq x) ^ N2 ≤ (1 + sq x) ^ (max N1 N2) := pow_le_pow_right₀ hs (le_max_right _ _)
    calc ‖evX (p + q) x‖ = ‖evX p x + evX q x‖ := by simp [evX]
      _ ≤ ‖evX p x‖ + ‖evX q x‖ := norm_add_le _ _
      _ ≤ C1 * (1 + sq x) ^ N1 + C2 * (1 + sq x) ^ N2 := add_le_add (hp x) (hq x)
      _ ≤ C1 * (1 + sq x) ^ (max N1 N2) + C2 * (1 + sq x) ^ (max N1 N2) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * (1 + sq x) ^ (max N1 N2) := by ring
  | mul_X p k hp =>
    obtain ⟨C, h, N, hp⟩ := hp
    refine ⟨C, h, N + 1, fun x => ?_⟩
    have hk : ‖(if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)‖ ≤ 1 + sq x := by
      split_ifs
      · rw [norm_star]; exact coord_le x _ _
      · exact coord_le x _ _
    calc ‖evX (p * X k) x‖ = ‖evX p x‖ * ‖(if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)‖ := by
          rw [evX, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sq x) ^ N * (1 + sq x) :=
          mul_le_mul (hp x) hk (norm_nonneg _) (by have := sq_nonneg' x; positivity)
      _ = C * (1 + sq x) ^ (N + 1) := by ring

lemma gram_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * (star (x a i) * x a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, eval_X]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

lemma continuous_gram (ε : Fin m → Bool) (i j : Fin n) :
    Continuous (fun x : Fin m → Fin n → ℂ => gramX ε x i j) :=
  continuous_evX _

lemma norm_gram_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) : ‖gramX ε x i j‖ ≤ sq x := by
  rw [gram_apply]
  have hsg : ∀ a, ‖sgn ε a‖ = 1 := fun a => by unfold sgn; split_ifs <;> simp
  calc ‖∑ a, sgn ε a * (star (x a i) * x a j)‖ ≤ ∑ a, ‖sgn ε a * (star (x a i) * x a j)‖ := norm_sum_le _ _
    _ = ∑ a, ‖x a i‖ * ‖x a j‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_mul, norm_mul, hsg, norm_star, one_mul]
    _ ≤ ∑ a, (‖x a i‖ ^ 2 + ‖x a j‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        nlinarith [sq_nonneg (‖x a i‖ - ‖x a j‖)]
    _ = ((∑ a, ‖x a i‖ ^ 2) + ∑ a, ‖x a j‖ ^ 2) / 2 := by rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (sq x + sq x) / 2 := by gcongr <;> exact col_sq_le x _
    _ = sq x := by ring

lemma trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ i, ∑ j, b i j * gramX ε x j i := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma continuous_trace (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun x : Fin m → Fin n → ℂ => (b * gramX ε x).trace) := by
  simp only [trace_eq]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_gram ε j i)

def kb (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖b i j‖

lemma kb_nonneg (b : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ kb b := by unfold kb; positivity

lemma norm_trace_le (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    ‖(b * gramX ε x).trace‖ ≤ kb b * sq x := by
  rw [trace_eq, kb, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_gram_le ε x j i) (norm_nonneg _)

lemma trace_im (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) (x : Fin m → Fin n → ℂ) :
    ((b * gramX ε x).trace).im = 0 := by
  have hg : ∀ i j, star (gramX ε x j i) = gramX ε x i j := by
    intro i j
    rw [gram_apply, gram_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
    rw [star_mul', star_mul', hs, star_star]; ring
  have : star ((b * gramX ε x).trace) = (b * gramX ε x).trace := by
    rw [trace_eq, star_sum]
    simp_rw [star_sum, star_mul', hg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hb.apply]
  exact Complex.conj_eq_iff_im.1 this

end PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
end
end

