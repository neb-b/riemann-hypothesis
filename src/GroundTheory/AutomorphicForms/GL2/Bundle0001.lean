module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.GL2.GJGlobalEntire
section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

variable {J J' : ℝ → ℂ}

theorem locallyIntegrableOn_indicator_Ici (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ici (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ici

theorem locallyIntegrableOn_indicator_Ioi (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ioi (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ioi

theorem isBigO_indicator_atTop {A : Set ℝ} (hA : A ∈ atTop) {a : ℝ}
    (h : J =O[atTop] (· ^ (-a))) : A.indicator J =O[atTop] (· ^ (-a)) := by
  refine EventuallyEq.trans_isBigO ?_ h
  filter_upwards [hA] with t ht
  exact indicator_of_mem ht J

theorem isBigO_indicator_nhdsGT {A : Set ℝ} (hA : A ⊆ Ici 1) (b : ℝ) :
    A.indicator J =O[𝓝[>] 0] (· ^ (-b)) := by
  refine EventuallyEq.trans_isBigO (f₂ := fun _ => (0 : ℂ)) ?_ (isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact indicator_of_notMem (fun h => absurd (hA h) (not_le.2 ht.2)) J

theorem differentiable_mellin_indicator {A : Set ℝ} (hA : A ⊆ Ici 1) (hAt : A ∈ atTop)
    (hloc : LocallyIntegrableOn (A.indicator J) (Ioi 0))
    (hd : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) : Differentiable ℂ (mellin (A.indicator J)) := by
  intro w
  exact mellin_differentiableAt_of_isBigO_rpow hloc (isBigO_indicator_atTop hAt (hd (w.re + 1)))
    (lt_add_one _) (isBigO_indicator_nhdsGT hA (w.re - 1)) (sub_one_lt _)

theorem mellinConvergent_indicator {A : Set ℝ} (hA : MeasurableSet A) {w : ℂ}
    (hc : MellinConvergent J w) : MellinConvergent (A.indicator J) w := by
  have : (fun t : ℝ => (t : ℂ) ^ (w - 1) • A.indicator J t) =
      A.indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) := by
    funext t
    by_cases ht : t ∈ A <;> simp [ht]
  unfold MellinConvergent
  rw [this]
  exact hc.indicator hA

theorem mellin_eq_add_of_convergent {w : ℂ} (hc : MellinConvergent J w) :
    mellin J w = mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Iio (1 : ℝ)).indicator J) w := by
  have h1 := mellinConvergent_indicator (J := J) (A := Ici 1) measurableSet_Ici hc
  have h2 := mellinConvergent_indicator (J := J) (A := Iio 1) measurableSet_Iio hc
  unfold mellin
  rw [← integral_add h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← smul_add]
  congr 1
  have := Set.indicator_self_add_compl (Ici (1 : ℝ)) J
  rw [compl_Ici] at this
  exact (congrFun this t).symm

theorem mellin_indicator_Iio_eq {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (w : ℂ) :
    mellin ((Iio (1 : ℝ)).indicator J) w = mellin ((Ioi (1 : ℝ)).indicator J') (κ - w) := by
  have e : mellin ((Iio (1 : ℝ)).indicator J) w =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(κ : ℂ)) • (fun u : ℝ => (Ioi (1 : ℝ)).indicator J' u⁻¹) t) w := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [smul_eq_mul]
    congr 1
    by_cases h1 : t < 1
    · have : 1 < t⁻¹ := one_lt_inv₀ ht |>.2 h1
      rw [indicator_of_mem (show t ∈ Iio 1 from h1), indicator_of_mem (show t⁻¹ ∈ Ioi 1 from this),
        hsym t ht]
    · have : ¬ 1 < t⁻¹ := fun h => h1 ((one_lt_inv₀ ht).1 h)
      rw [indicator_of_notMem (show t ∉ Iio 1 from h1),
        indicator_of_notMem (show t⁻¹ ∉ Ioi 1 from this), mul_zero]
  rw [e, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

theorem mellin_indicator_Ici_eq_Ioi (f : ℝ → ℂ) (w : ℂ) :
    mellin ((Ici (1 : ℝ)).indicator f) w = mellin ((Ioi (1 : ℝ)).indicator f) w := by
  unfold mellin
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have h : ∀ᵐ t : ℝ, t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h] with t ht _
  congr 1
  by_cases h1 : 1 < t
  · rw [indicator_of_mem (show t ∈ Ici 1 from h1.le), indicator_of_mem (show t ∈ Ioi 1 from h1)]
  · have h2 : ¬ 1 ≤ t := fun h => h1 (lt_of_le_of_ne h (Ne.symm ht))
    rw [indicator_of_notMem (show t ∉ Ici 1 from h2), indicator_of_notMem (show t ∉ Ioi 1 from h1)]

theorem symm_of_symm {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹) :
    ∀ t : ℝ, 0 < t → J' t = (t : ℂ) ^ (-(κ : ℂ)) * J t⁻¹ := by
  intro t ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [hsym t⁻¹ (inv_pos.2 ht), inv_inv, ← mul_assoc, ofReal_inv, inv_cpow _ _ harg,
    mul_inv_cancel₀ (cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 ht.ne'))), one_mul]

theorem exists_entire_of_symm {κ : ℝ} (hJ : ContinuousOn J (Ioi 0)) (hJ' : ContinuousOn J' (Ioi 0))
    (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (hdJ : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) (hdJ' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a))) :
    ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ w, MellinConvergent J w → Λ w = mellin J w) ∧
      (∀ w, MellinConvergent J' w → Λ' w = mellin J' w) ∧ ∀ w, Λ w = Λ' (κ - w) := by
  have hsym' := symm_of_symm hsym
  have hIoi : Ioi (1 : ℝ) ∈ atTop := Ioi_mem_atTop 1
  have hIci : Ici (1 : ℝ) ∈ atTop := Ici_mem_atTop 1
  have d1 := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ) hdJ
  have d2 := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ') hdJ'
  have d1' := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ') hdJ'
  have d2' := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ) hdJ
  refine ⟨fun w => mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Ioi (1 : ℝ)).indicator J') (κ - w),
    fun w => mellin ((Ici (1 : ℝ)).indicator J') w + mellin ((Ioi (1 : ℝ)).indicator J) (κ - w),
    d1.add (d2.comp ((differentiable_const _).sub differentiable_id)),
    d1'.add (d2'.comp ((differentiable_const _).sub differentiable_id)), ?_, ?_, ?_⟩
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym]
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym']
  · intro w
    simp only [sub_sub_cancel]
    rw [add_comm, mellin_indicator_Ici_eq_Ioi J, mellin_indicator_Ici_eq_Ioi J']

end GJGlobal

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.GL2.GJGlobalRank
section
open Matrix

namespace GroundTheory.Automorphic

namespace GJGlobal

variable {K : Type*} [Field K] {n : ℕ}

theorem rank_eq_iff_isUnit_det (ξ : Matrix (Fin n) (Fin n) K) : ξ.rank = n ↔ IsUnit ξ.det := by
  constructor
  · intro h
    rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    have hs : Function.Surjective ξ.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact h
    exact LinearMap.injective_iff_surjective.2 hs
  · intro h
    have := rank_of_isUnit ξ ((isUnit_iff_isUnit_det ξ).2 h)
    rwa [Fintype.card_fin] at this

theorem rank_lt_of_det_eq_zero {ξ : Matrix (Fin n) (Fin n) K} (h : ξ.det = 0) : ξ.rank < n := by
  have hle : ξ.rank ≤ n := by
    have := rank_le_card_width ξ
    rwa [Fintype.card_fin] at this
  refine lt_of_le_of_ne hle fun he => ?_
  have := (rank_eq_iff_isUnit_det ξ).1 he
  rw [h] at this
  exact not_isUnit_zero this

theorem rank_eq_zero_iff {ξ : Matrix (Fin n) (Fin n) K} : ξ.rank = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range ξ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
    have hz : ξ.mulVecLin = 0 := LinearMap.range_eq_bot.1 hr
    ext i j
    have := congrFun (congrArg DFunLike.coe hz) (Pi.single j 1)
    simpa [mulVecLin_apply, mulVec_single_one] using congrFun this i
  · rintro rfl
    exact rank_zero

noncomputable def unitsEquiv : GL (Fin n) K ≃ {ξ : Matrix (Fin n) (Fin n) K // IsUnit ξ.det} where
  toFun γ := ⟨γ, (isUnit_iff_isUnit_det _).1 γ.isUnit⟩
  invFun ξ := ((isUnit_iff_isUnit_det _).2 ξ.2).unit
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem tsum_eq_tsum_GL_add {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ, f ξ = ∑' γ : GL (Fin n) K, f γ + ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {ξ | IsUnit ξ.det}]
  congr 1
  · exact ((unitsEquiv (K := K) (n := n)).tsum_eq (fun ξ => f ξ)).symm
  · have e : ({ξ | IsUnit ξ.det}ᶜ : Set (Matrix (Fin n) (Fin n) K)) = {ξ | ξ.det = 0} := by
      ext ξ
      simp [isUnit_iff_ne_zero]
    rw [e]
    rfl

theorem tsum_det_eq_zero_eq_sum_rank {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ =
      ∑ r : Fin n, ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, f ξ := by
  have e : {ξ : Matrix (Fin n) (Fin n) K | ξ.det = 0} =
      ⋃ r ∈ (Finset.univ : Finset (Fin n)), {ξ | ξ.rank = (r : ℕ)} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨ξ.rank, rank_lt_of_det_eq_zero h⟩, rfl⟩
    · rintro ⟨r, hr⟩
      by_contra h
      have := (rank_eq_iff_isUnit_det ξ).2 (isUnit_iff_ne_zero.2 h)
      have hr' := r.2
      omega
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Disjoint fun r : Fin n => {ξ : Matrix (Fin n) (Fin n) K | ξ.rank = (r : ℕ)}) := by
    intro r _ r' _ hrr'
    refine Set.disjoint_left.2 fun ξ h h' => hrr' (Fin.ext ?_)
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hsum := hasSum_sum_disjoint (f := f) Finset.univ hd fun r _ => (hf.subtype _).hasSum
  show ∑' ξ : ({ξ | ξ.det = 0} : Set (Matrix (Fin n) (Fin n) K)), f ξ = _
  rw [e]
  exact hsum.tsum_eq

end GJGlobal

end GroundTheory.Automorphic
end

