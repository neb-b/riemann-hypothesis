module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalLimitGlueOn
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology Set Function
open scoped ContDiff Manifold

theorem tendsto_of_forall_local_on_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι} (T : ι → (E → ℝ) → ℝ) (L : (E → ℝ) → ℝ)
    (hT : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → ∀ᶠ ε in l, T ε (f + g) = T ε f + T ε g)
    (hL : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → L (f + g) = L f + L g)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hloc : ∀ p ∈ tsupport f, ∃ N ∈ 𝓝 p, ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ N → Tendsto (fun ε => T ε g) l (𝓝 (L g))) :
    Tendsto (fun ε => T ε f) l (𝓝 (L f)) := by
  choose N hN hNf using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_tsupport f)
    (fun p : tsupport f => interior (N p.1 p.2)) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hN x hx)⟩)
  obtain ⟨g, hg⟩ : ∃ g : tsupport f → E → ℝ, g = fun i x => ρ i x * f x := ⟨_, rfl⟩
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => by
    rw [hg]; exact (ρ i).contMDiff.contDiff.mul hf
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => by
    rw [hg]; exact hfc.mul_left
  have hgN : ∀ i, tsupport (g i) ⊆ N i.1 i.2 := fun i => by
    rw [hg]; exact tsupport_mul_subset_left.trans ((hρ i).trans interior_subset)
  have hfin : {i | (support (ρ i) ∩ tsupport f).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hfc
  have hsum : f = ∑ i ∈ hfin.toFinset, g i := by
    funext x
    simp only [Finset.sum_apply, hg]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · rw [← finsum_eq_sum_of_support_subset (fun i => ρ i x), ρ.sum_eq_one hx, one_mul]
      intro i hi
      simp only [Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨x, hi, hx⟩
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hT0 : ∀ᶠ ε in l, T ε 0 = 0 := by
    filter_upwards [hT 0 0 contDiff_const HasCompactSupport.zero contDiff_const
      HasCompactSupport.zero] with ε h
    simpa using h
  have hL0 : L 0 = 0 := by
    simpa using hL 0 0 contDiff_const HasCompactSupport.zero contDiff_const HasCompactSupport.zero
  have key : ∀ s : Finset (tsupport f), ContDiff ℝ ∞ (∑ i ∈ s, g i) ∧
      HasCompactSupport (∑ i ∈ s, g i) ∧
      (∀ᶠ ε in l, T ε (∑ i ∈ s, g i) = ∑ i ∈ s, T ε (g i)) ∧
      L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨contDiff_const, HasCompactSupport.zero, hT0, hL0⟩
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [Finset.sum_insert ha]
      refine ⟨(hgs a).add h1, (hgc a).add h2, ?_, ?_⟩
      · filter_upwards [hT (g a) _ (hgs a) (hgc a) h1 h2, h3] with ε e1 e2
        rw [e1, e2]
      · rw [hL (g a) _ (hgs a) (hgc a) h1 h2, h4]
  obtain ⟨-, -, hTs, hLs⟩ := key hfin.toFinset
  rw [hsum, hLs]
  exact (tendsto_finsetSum _ fun i _ => hNf i.1 i.2 (g i) (hgs i) (hgc i) (hgN i)).congr'
    (hTs.mono fun ε h => h.symm)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MonicDifferenceQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

def monicDifferenceCoeff {d : ℕ} (C : Fin d → ℂ) (s : ℂ) (j : Fin d) : ℂ :=
  s ^ (d - 1 - (j : ℕ)) + ∑ k ∈ univ.filter (fun k : Fin d => (j : ℕ) < k), C k * s ^ ((k : ℕ) - 1 - j)

theorem sum_fin_ite_lt {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℂ) :
    ∑ j : Fin n, (if (j : ℕ) < m then f j else 0) = ∑ j ∈ range m, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0) n, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

theorem sub_pow_eq_mul_sum_fin {n m : ℕ} (hm : m ≤ n) (s t : ℂ) :
    (s - t) * ∑ j : Fin n, (if (j : ℕ) < m then s ^ (m - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) = s ^ m - t ^ m := by
  rw [sum_fin_ite_lt hm (fun j => s ^ (m - 1 - j) * t ^ j), mul_comm]
  have h := geom_sum₂_mul s t m
  rw [geom_sum₂_comm] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem monic_sub_eq_mul_sum {d : ℕ} (C : Fin d → ℂ) (s t : ℂ) :
    (s ^ d + ∑ k : Fin d, C k * s ^ (k : ℕ)) - (t ^ d + ∑ k : Fin d, C k * t ^ (k : ℕ)) =
      (s - t) * ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) := by
  have expand : ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) =
      ∑ j : Fin d, (if (j : ℕ) < d then s ^ (d - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) +
        ∑ k : Fin d, C k * ∑ j : Fin d,
          (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) := by
    simp only [monicDifferenceCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
  have h2 : ∑ k : Fin d, (s - t) * (C k * ∑ j : Fin d,
      (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)) =
      ∑ k : Fin d, (C k * s ^ (k : ℕ) - C k * t ^ (k : ℕ)) :=
    Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, sub_pow_eq_mul_sum_fin k.isLt.le, mul_sub]
  rw [expand, mul_add, sub_pow_eq_mul_sum_fin le_rfl, Finset.mul_sum, h2, Finset.sum_sub_distrib]
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChangeOfVariablesDegreePiola
section
set_option maxSynthPendingDepth 1

open scoped ContDiff
open MeasureTheory

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

variable {n : ℕ}

noncomputable def jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun k l => fderiv ℝ H x (Pi.single l 1) k

theorem det_fderiv_eq_det_jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    (fderiv ℝ H x).det = (Matrix.of (jacobian H x)).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1

theorem jacobian_eq_fderiv_apply (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hd : DifferentiableAt ℝ H x) (k l : Fin n) :
    jacobian H x k l = fderiv ℝ (fun y => H y k) x (Pi.single l 1) := by
  have hd' : HasFDerivAt (fun y => H y k) ((ContinuousLinearMap.proj k).comp (fderiv ℝ H x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp x
      hd.hasFDerivAt
  rw [hd'.fderiv]; rfl

noncomputable def detCML : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem detCML_apply (M : Fin n → Fin n → ℝ) : detCML M = Matrix.det (Matrix.of M) := rfl

theorem det_update_eq_sum (V : Fin n → Fin n → ℝ) (k : Fin n) (r : Fin n → ℝ) :
    Matrix.det (Matrix.of (Function.update V k r)) =
      ∑ l, r l * Matrix.det (Matrix.of (Function.update V k (Pi.single l 1))) := by
  have hr : r = ∑ l, r l • (Pi.single l 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hr]
  change (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap V k
    (∑ l, r l • (Pi.single l 1 : Fin n → ℝ)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]
  rfl

noncomputable def entriesCLM : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l =>
    (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1))

noncomputable def killRow (i : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => if k = i then 0 else ContinuousLinearMap.proj k

theorem killRow_apply_self (i : Fin n) (M : Fin n → Fin n → ℝ) : killRow i M i = 0 := by
  simp [killRow]

theorem killRow_apply_ne {i k : Fin n} (h : k ≠ i) (M : Fin n → Fin n → ℝ) :
    killRow i M k = M k := by
  simp [killRow, h]

theorem update_eq_killRow (M : Fin n → Fin n → ℝ) (i : Fin n) (c : Fin n → ℝ) :
    Function.update M i c = killRow i M + Pi.single i c := by
  funext k
  by_cases h : k = i
  · subst h; simp [killRow_apply_self]
  · simp [killRow_apply_ne h, h]

noncomputable def cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (i j : Fin n) (y : Fin n → ℝ) : ℝ :=
  Matrix.det (Matrix.of (Function.update (jacobian H y) i (Pi.single j 1)))

theorem hasFDerivAt_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (cofactorFn H i j)
      ((detCML.linearDeriv (Function.update (jacobian H x) i (Pi.single j 1))).comp
        ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x)))) x := by
  have h2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
    ((hH.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hM : HasFDerivAt
      (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ))
      ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x))) x := by
    have : (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ)) =
        fun y => killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1) := by
      funext y; exact update_eq_killRow _ _ _
    rw [this]
    exact ((killRow i).hasFDerivAt.comp x (entriesCLM.hasFDerivAt.comp x h2)).add_const _
  exact (detCML.hasFDerivAt _).comp x hM

theorem sum_det_symm_eq_zero (A : Fin n → Fin n → ℝ) {i k : Fin n} (hik : i ≠ k)
    (S : Fin n → Fin n → ℝ) (hS : ∀ j l, S j l = S l j) :
    ∑ j, Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k (S j))) =
      0 := by
  simp_rw [det_update_eq_sum _ k (S _)]
  set T : Fin n → Fin n → ℝ := fun j l =>
    Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single j 1)) k
      (Pi.single l 1))) with hTdef
  have hT : ∀ j l, T j l = - T l j := by
    intro j l
    have hw : (Function.update (Function.update A i (Pi.single l 1)) k (Pi.single j 1)) =
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) ∘
          Equiv.swap i k := by
      funext r
      by_cases hri : r = i
      · subst hri; simp [Equiv.swap_apply_left, hik]
      · by_cases hrk : r = k
        · subst hrk; simp [Equiv.swap_apply_right, hik]
        · simp [Equiv.swap_apply_of_ne_of_ne hri hrk, hri, hrk]
    have h1 : T l j = - T j l := by
      show Matrix.det (Matrix.of (Function.update (Function.update A i (Pi.single l 1)) k
        (Pi.single j 1))) = _
      rw [hw]
      exact (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).map_swap
        (Function.update (Function.update A i (Pi.single j 1)) k (Pi.single l 1)) hik
    linarith
  have hX : ∑ j, ∑ l, S j l * T j l = - ∑ j, ∑ l, S j l * T j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hS l j, hT l j]; ring
  change ∑ j, ∑ l, S j l * T j l = 0
  linarith

theorem sum_fderiv_cofactorFn_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i : Fin n)
    (x : Fin n → ℝ) :
    ∑ j, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) = 0 := by
  set D2 := fderiv ℝ (fderiv ℝ H) x with hD2
  have hsym : ∀ v w, D2 v w = D2 w v :=
    (hH.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  simp_rw [(hasFDerivAt_cofactorFn H hH i _ x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [killRow_apply_self, Function.update_idem]
    exact detCML.map_update_zero _ _
  · simp_rw [killRow_apply_ne hk]
    have := sum_det_symm_eq_zero (jacobian H x) (Ne.symm hk)
      (fun j l => D2 (Pi.single j 1) (Pi.single l 1) k)
      (fun j l => by simp only [hsym (Pi.single j 1)])
    exact this

theorem contDiff_cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H) (i j : Fin n) :
    ContDiff ℝ ∞ (cofactorFn H i j) := by
  have : cofactorFn H i j =
      fun y => detCML (killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1)) := by
    funext y; rw [detCML_apply, ← update_eq_killRow]; rfl
  rw [this]
  exact detCML.contDiff.comp (((killRow i).contDiff.comp
    (entriesCLM.contDiff.comp (hH.fderiv_right (m := ∞) le_rfl))).add contDiff_const)

theorem integral_det_fderiv_eq_zero (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin n) (hi : HasCompactSupport fun x => H x i) : ∫ x, (fderiv ℝ H x).det = 0 := by
  set h : (Fin n → ℝ) → ℝ := fun x => H x i with hh
  have hhs : ContDiff ℝ ∞ h := (contDiff_apply ℝ (fun _ => ℝ) i).comp hH
  have hJ : ∀ x j, jacobian H x i j = fderiv ℝ h x (Pi.single j 1) := fun x j =>
    jacobian_eq_fderiv_apply H x ((hH.differentiable (by simp)) x) i j
  have hexp : ∀ x, (fderiv ℝ H x).det =
      ∑ j, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) := by
    intro x
    rw [det_fderiv_eq_det_jacobian]
    have := det_update_eq_sum (jacobian H x) i (jacobian H x i)
    rw [Function.update_eq_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, mul_comm]; rfl
  have hcof := contDiff_cofactorFn H hH i
  have hcd : ∀ j, Continuous fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) := fun j =>
    ((hcof j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hhd : ∀ j, Continuous fun x => fderiv ℝ h x (Pi.single j 1) := fun j =>
    (hhs.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : ∀ j, Integrable (fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x) :=
    fun j => ((hcd j).mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have i2 : ∀ j, Integrable (fun x => cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1)) :=
    fun j => ((hcof j).continuous.mul (hhd j)).integrable_of_hasCompactSupport
      (hi.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)).mul_left
  have i3 : ∀ j, Integrable (fun x => cofactorFn H i j x * h x) :=
    fun j => ((hcof j).continuous.mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have hibp : ∀ j, ∫ x, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) =
      - ∫ x, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i1 j) (i2 j) (i3 j)
      (fun x _ => ((hcof j).differentiable (by simp)) x)
      (fun x _ => (hhs.differentiable (by simp)) x)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => i2 j]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => i1 j]
  simp_rw [← Finset.sum_mul, sum_fderiv_cofactorFn_eq_zero H hH i, zero_mul, integral_zero, neg_zero]

end ChangeOfVariablesDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothFrobeniusLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

section FrobeniusLift

variable {C : Type*} [CommRing C] {N : Ideal C} {p : ℕ}

theorem pow_prime_add_of_sq_eq_bot (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) {n : C}
    (hn : n ∈ N) : (c + n) ^ p = c ^ p := by
  have hn2 : n ^ 2 = 0 := by
    have := Ideal.pow_mem_pow hn 2
    rwa [hN, Ideal.mem_bot] at this
  have hnp : n ^ p = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp.two_le
    rw [hk, pow_add, hn2, zero_mul]
  rw [add_pow_prime_eq hp, hpC, hnp]
  simp

theorem pow_prime_eq_of_mk_eq (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) {c c' : C}
    (h : Ideal.Quotient.mk N c = Ideal.Quotient.mk N c') : c ^ p = c' ^ p := by
  have hmem : c - c' ∈ N := Ideal.Quotient.eq.mp h
  have := pow_prime_add_of_sq_eq_bot hp hpC hN c' hmem
  rwa [add_sub_cancel] at this

noncomputable def sqZeroFrobeniusLift (N : Ideal C) (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) :
    C ⧸ N →+* C where
  toFun y := (Ideal.Quotient.mk_surjective y).choose ^ p
  map_one' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 1) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_one]), one_pow]
  map_mul' x y := by
    rw [← mul_pow]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_mul, (Ideal.Quotient.mk_surjective _).choose_spec])
  map_zero' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 0) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_zero]), zero_pow hp.ne_zero]
  map_add' x y := by
    have hadd : ((Ideal.Quotient.mk_surjective x).choose + (Ideal.Quotient.mk_surjective y).choose) ^ p =
        (Ideal.Quotient.mk_surjective x).choose ^ p + (Ideal.Quotient.mk_surjective y).choose ^ p := by
      rw [add_pow_prime_eq hp, hpC]; simp
    rw [← hadd]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_add (f := _), (Ideal.Quotient.mk_surjective _).choose_spec])

theorem sqZeroFrobeniusLift_mk (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) :
    sqZeroFrobeniusLift N hp hpC hN (Ideal.Quotient.mk N c) = c ^ p :=
  pow_prime_eq_of_mk_eq hp hpC hN (Ideal.Quotient.mk_surjective _).choose_spec

end FrobeniusLift

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticImplicitChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticImplicitChart.Statement : Prop :=
  ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (h : ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ)),
    (∀ j, AnalyticAt ℂ (h j) a) → (∀ j, h j a = 0) →
    LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) → W ∈ 𝓝 a →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), d + Fintype.card ι = Fintype.card σ ∧ IsOpen O ∧ IsOpen V ∧ a ∈ V ∧
        V ⊆ W ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        {z | z ∈ V ∧ ∀ j, h j z = 0} = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AnalyticRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (t₀ : Fin d → ℂ) (τ₀ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) t₀) →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable →
    τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
    ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t₀ = τ₀ ∧
      ∀ t ∈ O, r t ^ N + ∑ j, a j t * r t ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticSimpleRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticSimpleRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (y : Fin d → ℂ) (τ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) y) →
    τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ AnalyticOnNhd ℂ ψ U ∧ ψ y = τ ∧
        ∀ y' ∈ U, ψ y' ∈ B ∧ ∀ s ∈ B, (s ^ N + ∑ j, a j y' * s ^ (j : ℕ) = 0 ↔ s = ψ y')

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPartition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPartition.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ r : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0, (∀ A, r A ≠ 0) →
        ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin k)))
          (A : ℕ → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ n, MeasurableSet (t n)) ∧ (∀ n, t n ⊆ U) ∧
            U ⊆ ⋃ n, t n ∧ (∀ n, ApproximatesLinearOn F (A n) (t n) (r (A n))) ∧
              ∀ n, ∀ x ∈ t n, ‖fderiv ℝ F x - A n‖₊ ≤ r (A n)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPerfectFieldExtensionFormallySmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PerfectFieldExtensionFormallySmooth.Statement : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [PerfectField F], Algebra.FormallySmooth F K

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

