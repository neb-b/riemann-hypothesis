module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation
section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem tsb_mR_cont (n : ℕ) : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_lower_left_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_lower_right_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_first_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_lower_left_block_alt n).const_smul Complex.I).add (continuous_lower_right_block_alt n)

theorem continuous_second_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact (((continuous_lower_left_block_alt n).const_smul Complex.I).neg).add (continuous_lower_right_block_alt n)

theorem continuousAt_twisted_section {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) (h0 : M.det ≠ 0) (h1 : (u1 M).det ≠ 0)
    (h2 : (u2 M).det ≠ 0) : ContinuousAt (twistedScalarSection p q e) M := by
  unfold twistedScalarSection f0
  refine ContinuousAt.mul (ContinuousAt.zpow₀ (continuous_id.matrix_det).continuousAt e (Or.inl h0))
    (ContinuousAt.mul ?_ ?_)
  · exact ContinuousAt.zpow₀ ((continuous_first_cayley_block n).matrix_det).continuousAt _ (Or.inl h1)
  · exact ContinuousAt.zpow₀ ((continuous_second_cayley_block n).matrix_det).continuousAt _ (Or.inl h2)

theorem tsb_det_ne (n : ℕ) (g : GR n) : (mR g).det ≠ 0 := by
  have h := g.1.isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem continuous_spherical_section (hD : CayleyBlocksInvertible) (n p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have : (F0 p q e : GR n → ℂ) = twistedScalarSection p q e ∘ mR := rfl
  rw [this]
  exact (continuousAt_twisted_section p q e (mR g) (tsb_det_ne n g) (hD n g).1 (hD n g).2).comp (tsb_mR_cont n).continuousAt

def kSet (n : ℕ) : Set (M2 n) := (Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ : Set (M2 n)) ∩ {M | InG M}

theorem tsb_kSet_compact (n : ℕ) : IsCompact (kSet n) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hK (IsClosed.inter isClosed_unitary ?_) ?_
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · intro U hU
    exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
      mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU.1 i j)

theorem tsb_kSet_mem {n : ℕ} {M : M2 n} (h : M ∈ kSet n) : Mᴴ * M = 1 ∧ M * Mᴴ = 1 ∧ InG M := by
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := h.1
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 := (Matrix.mem_unitaryGroup_iff).1 hu
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using h1, by simpa [Matrix.star_eq_conjTranspose] using h2, h.2⟩

def kOf (n : ℕ) (M : kSet n) : KR n :=
  ⟨⟨⟨M.1, M.1ᴴ, (tsb_kSet_mem M.2).2.1, (tsb_kSet_mem M.2).1⟩, (tsb_kSet_mem M.2).2.2⟩,
    ⟨(tsb_kSet_mem M.2).2.2, (tsb_kSet_mem M.2).1⟩⟩

theorem tsb_kOf_cont (n : ℕ) : Continuous (kOf n) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.matrix_conjTranspose

theorem tsb_kOf_surj (n : ℕ) : Function.Surjective (kOf n) := by
  intro k
  have hk := k.2
  have hM : mR (k : GR n) ∈ kSet n := by
    refine ⟨?_, hk.1⟩
    show mR (k : GR n) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hk.2
  refine ⟨⟨mR (k : GR n), hM⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rfl

theorem tsb_compact (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.mp (tsb_kSet_compact n)
  exact ⟨by rw [← (tsb_kOf_surj n).range_eq]; exact isCompact_range (tsb_kOf_cont n)⟩

def dM {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.exp (t * X j) : ℂ)) 0 0 (diagonal fun j => (Real.exp (-(t * X j)) : ℂ))

theorem exp_diagonal_mul_inverse {n : ℕ} (X : Fin n → ℝ) (t : ℝ) :
    (diagonal fun j => (Real.exp (t * X j) : ℂ)) * (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) = 1 ∧
    (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) * (diagonal fun j => (Real.exp (t * X j) : ℂ)) = 1 := by
  constructor <;>
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp

theorem tsb_dM_mul {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : dM X t * dM X (-t) = 1 := by
  unfold dM
  rw [fromBlocks_multiply]
  have h := exp_diagonal_mul_inverse X t
  have e1 : (fun j => (Real.exp (-t * X j) : ℂ)) = fun j => (Real.exp (-(t * X j)) : ℂ) := by
    funext j; rw [neg_mul]
  have e2 : (fun j => (Real.exp (-(-t * X j)) : ℂ)) = fun j => (Real.exp (t * X j) : ℂ) := by
    funext j; rw [neg_mul, neg_neg]
  rw [e1, e2]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h.1, h.2, fromBlocks_one]

theorem tsb_dM_star {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : (dM X t)ᴴ = dM X t := by
  unfold dM
  rw [fromBlocks_conjTranspose, diagonal_conjTranspose, diagonal_conjTranspose, conjTranspose_zero]
  congr 2 <;> (funext j; simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal])

theorem tsb_dM_inG {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : InG (dM X t) := by
  unfold InG
  rw [tsb_dM_star]
  unfold dM JJ
  have h := exp_diagonal_mul_inverse X t
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.one_mul, h.1, h.2, neg_zero]

theorem tsb_dil_exists (n : ℕ) (X : Fin n → ℝ) (t : ℝ) : ∃ a : GR n, IsDil X t a := by
  have h1 := tsb_dM_mul X t
  have h2 : dM X (-t) * dM X t = 1 := by simpa using tsb_dM_mul X (-t)
  exact ⟨⟨⟨dM X t, dM X (-t), h1, h2⟩, tsb_dM_inG X t⟩, rfl⟩

theorem tsb_dil_aZ {n : ℕ} (X : Fin n → ℝ) (t : ℝ) (a : GR n) (h : IsDil X t a) : mR a = aZ X t := by
  rw [h]
  unfold aZ
  congr 2 <;> (funext j; push_cast [Complex.ofReal_exp]; ring_nf)

theorem tsb_aZ_entry {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) :
    (∀ z, aZ X z i j = match i, j with
      | Sum.inl a, Sum.inl b => if a = b then Complex.exp (z * X a) else 0
      | Sum.inr a, Sum.inr b => if a = b then Complex.exp (-(z * X a)) else 0
      | _, _ => 0) := by
  intro z
  rcases i with a | a <;> rcases j with b | b <;> simp [aZ, diagonal_apply]

theorem tsb_aZ_diff {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) : Differentiable ℂ (fun z => aZ X z i j) := by
  have h := tsb_aZ_entry X i j
  simp_rw [h]
  rcases i with a | a <;> rcases j with b | b <;> simp only
  · split_ifs
    · fun_prop
    · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_const _
  · split_ifs
    · exact (Complex.differentiable_exp.comp ((differentiable_id.mul (differentiable_const _)).neg))
    · exact differentiable_const _

theorem tsb_aZ_cont {n : ℕ} (X : Fin n → ℝ) : Continuous (fun z => aZ X z) :=
  continuous_pi fun i => continuous_pi fun j => (tsb_aZ_diff X i j).continuous

theorem tsb_det_diffAt {ι : Type} [Fintype ι] [DecidableEq ι] {A : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (h : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) z) : DifferentiableAt ℂ (fun w => (A w).det) z := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd fun i _ => h _ _)

theorem tsb_mul_diff {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n ⊕ Fin n) :
    Differentiable ℂ (fun z => (M * aZ X z) i j) := by
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (tsb_aZ_diff X k j)

theorem differentiable_first_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u1 (M * aZ X z) i j) := by
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (tsb_mul_diff X M _ _)).add (tsb_mul_diff X M _ _)

theorem differentiable_second_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u2 (M * aZ X z) i j) := by
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact (((differentiable_const _).mul (tsb_mul_diff X M _ _)).neg).add (tsb_mul_diff X M _ _)

theorem tsb_det_aZ_ne {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : (aZ X z).det ≠ 0 := by
  unfold aZ
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)
    (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)

theorem tsbFacts : TSBFacts := by
  intro hD n p q e
  refine ⟨tsb_compact n, tsb_mR_cont n, continuous_spherical_section hD n p q e, tsb_dil_exists n, tsb_dil_aZ, ?_⟩
  intro X C hC
  set Φ : GR n × ℂ → M2 n := fun yz => mR yz.1 * aZ X yz.2 with hΦ
  have hΦc : Continuous Φ := ((tsb_mR_cont n).comp continuous_fst).matrix_mul ((tsb_aZ_cont X).comp continuous_snd)
  set O : Set (GR n × ℂ) := {yz | (u1 (Φ yz)).det ≠ 0 ∧ (u2 (Φ yz)).det ≠ 0} with hO
  have hOo : IsOpen O := by
    change IsOpen ({yz : GR n × ℂ | (u1 (Φ yz)).det ≠ 0} ∩
      {yz : GR n × ℂ | (u2 (Φ yz)).det ≠ 0})
    refine IsOpen.inter ?_ ?_
    · exact isOpen_ne_fun (((continuous_first_cayley_block n).comp hΦc).matrix_det) continuous_const
    · exact isOpen_ne_fun (((continuous_second_cayley_block n).comp hΦc).matrix_det) continuous_const
  have hreal : ∀ (y : GR n) (t : ℝ), (y, (t : ℂ)) ∈ O := by
    intro y t
    obtain ⟨a, ha⟩ := tsb_dil_exists n X t
    have : Φ (y, (t : ℂ)) = mR (y * a) := by
      simp only [hΦ]; rw [← tsb_dil_aZ X t a ha]; rfl
    simp only [hO, Set.mem_setOf_eq, this]
    exact hD n (y * a)
  have tube : ∀ t : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (t : ℂ) ∈ v ∧ C ×ˢ v ⊆ O := by
    intro t
    obtain ⟨u, v, -, hv, hCu, htv, huv⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (t : ℂ))) hOo
      (by rintro ⟨y, z⟩ ⟨-, hz⟩; simp only [Set.mem_singleton_iff] at hz; subst hz; exact hreal y t)
    exact ⟨v, hv, htv rfl, fun yz hyz => huv ⟨hCu hyz.1, hyz.2⟩⟩
  choose v hvo hvt hvC using tube
  refine ⟨⋃ t, v t, isOpen_iUnion hvo, fun t => Set.mem_iUnion.2 ⟨t, hvt t⟩, ?_, ?_⟩
  · intro yz hyz
    obtain ⟨hy, hz⟩ := hyz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : yz ∈ O := hvC t ⟨hy, ht⟩
    have h0 : (Φ yz).det ≠ 0 := by
      simp only [hΦ]; rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    exact ((continuousAt_twisted_section p q e (Φ yz) h0 hmem.1 hmem.2).comp hΦc.continuousAt).continuousWithinAt
  · intro y hy z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : (y, z) ∈ O := hvC t (Set.mk_mem_prod hy ht)
    have h0 : (mR y * aZ X z).det ≠ 0 := by
      rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold twistedScalarSection f0
    refine DifferentiableAt.mul ?_ (DifferentiableAt.mul ?_ ?_)
    · exact (tsb_det_diffAt fun i j => (tsb_mul_diff X (mR y) i j).differentiableAt).zpow (Or.inl h0)
    · exact (tsb_det_diffAt fun i j => (differentiable_first_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.1)
    · exact (tsb_det_diffAt fun i j => (differentiable_second_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.2)

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtEvalCurve
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => (α j : ℂ) * x a j

def aH (X : Fin n → ℝ) (h : ℝ) : Fin n → ℝ := fun j => Real.exp (h * X j)

theorem ept_scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    ept (scal α x) = fun k => (α k.2.1 : ℂ) * ept x k := by
  funext k
  unfold ept scal
  split_ifs
  · simp [star_mul', Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_eval_curve {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : MvPolynomial σ ℂ) (w : ℝ → σ → ℂ)
    (w' : σ → ℂ) (h : ℝ) (hw : ∀ k, HasDerivAt (fun s => w s k) (w' k) h) :
    HasDerivAt (fun s => eval (w s) Q) (∑ k, eval (w h) (pderiv k Q) * w' k) h := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const h a
  | add p q hp hq =>
    have e : (∑ k, eval (w h) (pderiv k (p + q)) * w' k) =
        (∑ k, eval (w h) (pderiv k p) * w' k) + ∑ k, eval (w h) (pderiv k q) * w' k := by
      simp [map_add (f := _), add_mul, Finset.sum_add_distrib]
    rw [e]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p i hp =>
    have e : ∑ k, eval (w h) (pderiv k (p * X i)) * w' k =
        (∑ k, eval (w h) (pderiv k p) * w' k) * w h i + eval (w h) p * w' i := by
      have e1 : ∀ k, eval (w h) (pderiv k (p * X i)) * w' k =
          eval (w h) (pderiv k p) * w' k * w h i + (if k = i then eval (w h) p * w' i else 0) := by
        intro k
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, eval_X]
        by_cases hk : k = i
        · subst hk; simp; ring
        · simp [Pi.single_apply, hk]; ring
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [e]
    exact (hp.mul (hw i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)

theorem hasDerivAt_scal_coord (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun s => ept (scal (aH X s) y) k) ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k) h := by
  simp only [ept_scal, aH]
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * X k.2.1)) (Real.exp (h * X k.2.1) * X k.2.1) h := by
    simpa using ((hasDerivAt_id h).mul_const (X k.2.1)).exp
  have h2 := (h1.ofReal_comp).mul_const (ept y k)
  refine h2.congr_deriv ?_
  rw [Complex.ofReal_mul]; ring

theorem integral_scal (α : Fin n → ℝ) (hα : ∀ j, 0 < α j) (f : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ x, f x = (∏ j, α j ^ (2 * m) : ℝ) * ∫ y, f (scal α y) := by
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := LinearMap.pi fun j => (α j • LinearMap.id).comp (LinearMap.proj j)
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = scal α y := by
    intro y; funext a j; simp [L, Li, scal, Complex.real_smul]
  have hdetLi : LinearMap.det Li = ∏ j, α j ^ 2 := by
    simp only [Li, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]
  have hdet : LinearMap.det L = ∏ j, α j ^ (2 * m) := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hD : 0 < ∏ j, α j ^ (2 * m) := Finset.prod_pos fun j _ => pow_pos (hα j) _
  let Linv : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a =>
    (LinearMap.pi fun j => ((α j)⁻¹ • LinearMap.id).comp (LinearMap.proj j)).comp (LinearMap.proj a)
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearEquiv.ofLinear L Linv
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
  have hH1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by infer_instance
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = scal α y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hD.ne')
  have h1 : ∫ y, f (scal α y) = (∏ j, α j ^ (2 * m))⁻¹ * ∫ x, f x := by
    have := integral_map_equiv e f (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolomorphicSectionExtensionExists
section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_dil (X : Fin n → ℝ) (s : ℝ) (a : GR n) (h : IsDil X s a) : mR a = Ac X s := by
  rw [h]
  unfold Ac
  congr 2 <;> funext j <;> push_cast [Complex.ofReal_exp] <;> (try ring_nf)

theorem det_Ac (X : Fin n → ℝ) (z : ℂ) : (Ac X z).det = 1 := by
  unfold Ac
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add]
  try simp

theorem holomorphic_section_extension_eq (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n) (ha : ∀ s, IsDil X s (a s)) (h : GR n) (s : ℝ) :
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s) := by
  unfold holomorphicSectionExtension F0 f0
  rw [mR_mul, mR_dil X s (a s) (ha s), det_mul, det_Ac, mul_one, mul_assoc]

theorem continuous_Ac (X : Fin n → ℝ) : Continuous (Ac X) := by
  unfold Ac
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)

theorem differentiable_Ac_entry (X : Fin n → ℝ) (a b : Fin n ⊕ Fin n) : Differentiable ℂ fun z => Ac X z a b := by
  rcases a with a | a <;> rcases b with b | b <;> by_cases hab : a = b <;>
    simp [Ac, diagonal_apply, hab] <;> fun_prop

theorem differentiable_det_entries {m : Type} [Fintype m] [DecidableEq m] (A : ℂ → Matrix m m ℂ)
    (hA : ∀ i j, Differentiable ℂ fun z => A z i j) : Differentiable ℂ fun z => (A z).det := by
  have : (fun z => (A z).det) = fun z => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i := by
    funext z
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hA _ _)

theorem differentiable_u_det (M : M2 n) (X : Fin n → ℝ) (w : ℂ) :
    Differentiable ℂ fun z => (w • (M * Ac X z).toBlocks₂₁ + (M * Ac X z).toBlocks₂₂).det := by
  apply differentiable_det_entries
  intro i j
  have hm : ∀ a b, Differentiable ℂ fun z => (M * Ac X z) a b := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_Ac_entry X k b)
  simp only [Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (hm _ _)).add (hm _ _)

theorem continuous_u_det (X : Fin n → ℝ) (w : ℂ) :
    Continuous fun y : GR n × ℂ => (w • (mR y.1 * Ac X y.2).toBlocks₂₁ + (mR y.1 * Ac X y.2).toBlocks₂₂).det := by
  have hM : Continuous fun y : GR n × ℂ => mR y.1 * Ac X y.2 :=
    (continuous_mR.comp continuous_fst).matrix_mul ((continuous_Ac X).comp continuous_snd)
  have h21 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₁ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))
  have h22 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₂ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))
  exact ((h21.const_smul w).add h22).matrix_det

theorem first_cayley_block_eq (M : M2 n) : u1 M = Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂ := rfl

theorem second_cayley_block_eq (M : M2 n) : u2 M = (-Complex.I) • M.toBlocks₂₁ + M.toBlocks₂₂ := by
  simp [u2, neg_smul]

theorem holomorphic_section_extension_exists (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)) (hS : IsCompact S) :
    ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
      ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧
      ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V := by
  have c1 : Continuous fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det := by
    simpa only [first_cayley_block_eq] using continuous_u_det X Complex.I
  have c2 : Continuous fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det := by
    simpa only [second_cayley_block_eq] using continuous_u_det X (-Complex.I)
  set Z := {y : GR n × ℂ | (u1 (mR y.1 * Ac X y.2)).det ≠ 0 ∧ (u2 (mR y.1 * Ac X y.2)).det ≠ 0}
  have hZ : IsOpen Z := (isOpen_ne_fun c1 continuous_const).inter (isOpen_ne_fun c2 continuous_const)
  have hreal : ∀ (h : GR n) (s : ℝ), ((h, (s : ℂ)) : GR n × ℂ) ∈ Z := by
    intro h s
    have hm : mR h * Ac X s = mR (h * aD X s) := by rw [mR_mul, mR_dil X s _ (isDil_aD X s)]
    refine ⟨?_, ?_⟩
    · show (u1 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_first_det_ne_zero _
    · show (u2 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_second_det_ne_zero _
  have tube : ∀ s : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (s : ℂ) ∈ v ∧ S ×ˢ v ⊆ Z := by
    intro s
    obtain ⟨u, v, -, hv, hSu, hsv, huv⟩ := generalized_tube_lemma hS (isCompact_singleton (x := (s : ℂ))) hZ
      (by
        rintro ⟨h, z⟩ ⟨-, hz⟩
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hreal h s)
    exact ⟨v, hv, hsv rfl, (Set.prod_mono hSu le_rfl).trans huv⟩
  choose v hv hsv hSv using tube
  refine ⟨⋃ s, v s, isOpen_iUnion hv, fun s => Set.mem_iUnion.mpr ⟨s, hsv s⟩, ?_, ?_⟩
  · have hsub : S ×ˢ (⋃ s, v s) ⊆ Z := by
      rintro ⟨h, z⟩ ⟨hh, hz⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      exact hSv s (Set.mk_mem_prod hh hs)
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    have hyZ := hsub hy
    unfold holomorphicSectionExtension
    have e1 : ContinuousAt (fun y : GR n × ℂ => (mR y.1).det ^ e) y :=
      ((continuous_mR.comp continuous_fst).matrix_det.continuousAt).zpow₀ _ (Or.inl (det_mR_ne _))
    have e2 : ContinuousAt (fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det ^ (-(p : ℤ))) y :=
      c1.continuousAt.zpow₀ _ (Or.inl hyZ.1)
    have e3 : ContinuousAt (fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det ^ (-(q : ℤ))) y :=
      c2.continuousAt.zpow₀ _ (Or.inl hyZ.2)
    exact (e1.mul e2).mul e3
  · intro h hh z hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    have hyZ := hSv s (Set.mk_mem_prod hh hs)
    have d1 : Differentiable ℂ fun z => (u1 (mR h * Ac X z)).det := by
      simpa only [first_cayley_block_eq] using differentiable_u_det (mR h) X Complex.I
    have d2 : Differentiable ℂ fun z => (u2 (mR h * Ac X z)).det := by
      simpa only [second_cayley_block_eq] using differentiable_u_det (mR h) X (-Complex.I)
    unfold holomorphicSectionExtension
    have g1 : DifferentiableAt ℂ (fun z => (u1 (mR h * Ac X z)).det ^ (-(p : ℤ))) z := (d1 z).zpow (Or.inl hyZ.1)
    have g2 : DifferentiableAt ℂ (fun z => (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))) z := (d2 z).zpow (Or.inl hyZ.2)
    exact (((differentiableAt_const _).mul g1).mul g2).differentiableWithinAt

end PositivityTheory.Rg.Sw.AbsSt
end
end

