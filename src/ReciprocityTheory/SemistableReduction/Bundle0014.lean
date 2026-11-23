module

public import ReciprocityTheory.SemistableReduction.Bundle0009
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import Lemmata.GeneralBFactSecond.Imports
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.SemistableReduction.Bundle0005
public import Lemmata.MiscLemmasR.Imports
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SJCoreC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem gauss_pair {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun x : EuclideanSpace ℂ (Fin n) ↦
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ *
        exp (-‖x‖ ^ 2) = s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), exp (-‖x‖ ^ 2) = s * gaussOneC ^ n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 (fun i => star (WithLp.ofLp c i)) with hvdef
  have hvx : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      inner ℂ v x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hvdef, RCLike.inner_apply] <;> ring
  have hvn : ‖v‖ = ‖c‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [hvdef]
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set u0 : EuclideanSpace ℂ (Fin (m + 1)) := ((‖c‖⁻¹ : ℝ) : ℂ) • v with hu0
  have hu0n : ‖u0‖ = 1 := by
    rw [hu0, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, hvn,
      inv_mul_cancel₀ hc0.ne']
  have hon : Orthonormal ℂ (Set.restrict ({0} : Set (Fin (m + 1))) (fun _ => u0)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j :=
      Subtype.ext (by rw [Set.mem_singleton_iff.mp i.2, Set.mem_singleton_iff.mp j.2])
    subst hij
    simp only [Set.restrict_apply, if_true]
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖u0‖ : ℝ) : ℂ) ^ 2 = 1
    rw [hu0n]; simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (by rw [finrank_euclideanSpace]) hon
  have hb0 : b 0 = u0 := hb 0 (Set.mem_singleton 0)
  let M : EuclideanSpace ℂ (Fin (m + 1)) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
    b.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (m + 1)) ℂ)
  have hMr : ∀ x i, M x i = b.repr x i := fun x i => rfl
  have hnorm1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ = ‖c‖ * ‖M x 0‖ := by
    intro x
    rw [hMr, OrthonormalBasis.repr_apply_apply, hb0, hu0, inner_smul_left, hvx, norm_mul,
      Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  have hnorm2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), ‖x‖ ^ 2 = ∑ i, ‖M x i‖ ^ 2 := by
    intro x
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    rfl
  let f : Fin (m + 1) → ℂ → ℝ := fun i z =>
    if i = 0 then log (‖c‖ * ‖z‖) * exp (-‖z‖ ^ 2) else exp (-‖z‖ ^ 2)
  let g : Fin (m + 1) → ℂ → ℝ := fun _ z => exp (-‖z‖ ^ 2)
  have hexp : ∀ y : Fin (m + 1) → ℂ, exp (-∑ i, ‖y i‖ ^ 2) = ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y; rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have hf : ∀ y : Fin (m + 1) → ℂ,
      ∏ i, f i (y i) = log (‖c‖ * ‖y 0‖) * ∏ i, exp (-‖y i‖ ^ 2) := by
    intro y
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun i => exp (-‖y i‖ ^ 2))]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false]
    ring
  have hF1 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)),
      log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2) = ∏ i, f i (M x i) := by
    intro x
    rw [hf (M x), hnorm1, hnorm2, hexp]
  have hF2 : ∀ x : EuclideanSpace ℂ (Fin (m + 1)), exp (-‖x‖ ^ 2) = ∏ i, g i (M x i) := by
    intro x
    rw [hnorm2, hexp]
  set μ := (volume : Measure (EuclideanSpace ℂ (Fin (m + 1)))) with hμ
  let Me := M.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map Me).IsAddHaarMeasure := by
    have h := M.isAddHaarMeasure_map μ
    exact h
  set k := (μ.map Me).addHaarScalarFactor (volume : Measure (Fin (m + 1) → ℂ))
  have hν : μ.map Me = k • (volume : Measure (Fin (m + 1) → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hk : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hint : ∀ H : (Fin (m + 1) → ℂ) → ℝ, ∫ x, H (M x) ∂μ = (k : ℝ) * ∫ y, H y := by
    intro H
    calc ∫ x, H (M x) ∂μ = ∫ x, H (Me x) ∂μ := rfl
      _ = ∫ y, H y ∂(μ.map Me) := (Me.measurableEmbedding.integral_map H).symm
      _ = (k : ℝ) * ∫ y, H y := by
        rw [hν, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hintg : ∀ H : (Fin (m + 1) → ℂ) → ℝ, Integrable H → Integrable (fun x => H (M x)) μ := by
    intro H hH
    have h1 : Integrable H (μ.map Me) := by rw [hν]; exact hH.smul_measure_nnreal
    exact Me.measurableEmbedding.integrable_map_iff.mp h1
  have hP1 : ∫ y : Fin (m + 1) → ℂ, ∏ i, f i (y i) = gaussLogC ‖c‖ * gaussOneC ^ m := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := f), Fin.prod_univ_succ]
    simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, gaussLogC, gaussOneC]
  have hP2 : ∫ y : Fin (m + 1) → ℂ, ∏ i, g i (y i) = gaussOneC ^ (m + 1) := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := g)]
    simp only [g, Finset.prod_const, Finset.card_univ, Fintype.card_fin, gaussOneC]
  have hI1 : Integrable (fun y : Fin (m + 1) → ℂ => ∏ i, f i (y i)) := by
    rw [volume_pi]
    refine Integrable.fintype_prod (f := f) fun i => ?_
    by_cases hi : i = 0
    · subst hi; simpa [f] using integrable_gaussLogC hc0
    · simpa [f, hi] using integrable_gaussOneC
  refine ⟨(k : ℝ), NNReal.coe_pos.mpr hk, ?_, ?_, ?_⟩
  · exact (hintg _ hI1).congr (Filter.Eventually.of_forall fun x => (hF1 x).symm)
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) =>
        log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, f i (M x i) from funext hF1]
    rw [hint (fun y => ∏ i, f i (y i)), hP1]
  · rw [show (fun x : EuclideanSpace ℂ (Fin (m + 1)) => exp (-‖x‖ ^ 2)) =
        fun x => ∏ i, g i (M x i) from funext hF2]
    rw [hint (fun y => ∏ i, g i (y i)), hP2]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiContractC
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

theorem sc_scale {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (x : Fin r → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)

theorem sc_li_scale {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hv : LinearIndependent K v) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent K (fun i => a i • v i) := by
  have := hv.units_smul (fun i => Units.mk0 (a i) (ha i))
  convert this using 1
  funext i
  simp [Units.smul_def]

theorem sc_kerfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by
  set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)
  choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0 := fun i h =>
    hd0 i (hinj (by rw [h, map_zero]))
  refine ⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L
    rw [algebraMap_smul]; exact hdL i
  · have h := (b0 i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [mulVec_smul, h, smul_zero]
  · exact sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
  · intro y hy
    have hy' : y ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hy
    have hsum := b0.sum_repr ⟨y, hy'⟩
    have hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K) := by
      calc y = ((⟨y, hy'⟩ : LinearMap.ker N.mulVecLin) : Fin r → K) := rfl
        _ = ((∑ i, b0.repr ⟨y, hy'⟩ i • b0 i : LinearMap.ker N.mulVecLin) : Fin r → K) := by
          rw [hsum]
        _ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
    rw [hsum']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hb : (b0 i : Fin r → K) =
        (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K)) := by
      rw [inv_smul_smul₀ (ha i)]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem sc_imfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ c : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin r → K,
      (∀ j, c j ∈ L) ∧ LinearIndependent K (fun j => N *ᵥ c j) := by
  set e := Module.finBasis K (LinearMap.range N.mulVecLin)
  have hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (e j).2
    exact ⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩
  choose y hy using hex
  choose d hd0 hdL using fun j => sc_scale L hL (y j)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0 := fun j h =>
    hd0 j (hinj (by rw [h, map_zero]))
  refine ⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d j) • y j ∈ L
    rw [algebraMap_smul]; exact hdL j
  · have := sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
    have heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j =>
        algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j := by
      funext j; simp [mulVec_smul, hy]
    rw [heq]; exact this

theorem sc_append_li {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0 := by
    have := congrArg N.mulVecLin hg
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_add (f := _), map_sum, map_smul, Matrix.mulVecLin_apply, hbN] using this
  have hc0 := Fintype.linearIndependent_iff.mp hc _ h1
  have hb0 : ∀ i, g (Fin.castAdd m i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa [hc0] using hg
  intro i
  exact Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i

theorem sc_rank_pos {K : Type} [Field K] [NumberField K] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (hN : N ≠ 0) : 0 < finrank K (LinearMap.range N.mulVecLin) := by
  refine Nat.pos_of_ne_zero fun h0 => hN ?_
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := LinearMap.toMatrix'_toLin' N
  rw [Matrix.toLin'_apply', h0, map_zero] at this
  exact this.symm

theorem sc_index {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (N : Matrix (Fin r) (Fin r) K)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) (hcL : ∀ j, c j ∈ L)
    (hbN : ∀ i, N *ᵥ b i = 0) (hker : ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).toAddSubgroup.relIndex
        (L.map (N.mulVecLin.restrictScalars (𝓞 K))).toAddSubgroup =
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex L.toAddSubgroup := by
  set f := N.mulVecLin.restrictScalars (𝓞 K) with hf
  have hfx : ∀ x, f x = N *ᵥ x := fun x => rfl
  have hspanb : Submodule.span K (Set.range b) ≤ LinearMap.ker N.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [hbN i]
  have hspanc : Submodule.span (𝓞 K) (Set.range c) ≤
      (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, (hfx (c j)).symm⟩
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap _ _),
    ← AddSubgroup.inf_relIndex_right (Submodule.toAddSubgroup _)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
    AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun (𝓞 K) |>.mp hx
    set z := ∑ j, a j • c j with hz
    have hzc : z ∈ Submodule.span (𝓞 K) (Set.range c) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hzL : z ∈ L := Submodule.sum_mem _ fun j _ => L.smul_mem _ (hcL j)
    have hfz : f (x - z) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hz, map_sum]
      simp only [map_smul]
      simp only [hfx] at ha ⊢
      rw [ha, sub_self]
    have hsat : x - z ∈ satSub L b := by
      refine ⟨L.sub_mem hxL hzL, ?_⟩
      exact hker _ (by rw [← hfx]; exact hfz)
    exact Submodule.mem_sup.mpr ⟨x - z, hsat, z, hzc, sub_add_cancel x z⟩
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : f y = 0 := by
      have h := hspanb hy.2
      rw [LinearMap.mem_ker] at h
      exact h
    rw [map_add (f := _), hy0, zero_add]
    exact hspanc hz

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegCC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a b : K) (u w : Fin r → K) : S.h (a • u) (b • w) = S.c a * b * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → K) (w : Fin r → K) :
    S.h (∑ i ∈ s, u i) w = ∑ i ∈ s, S.h (u i) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HermForm.h, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

theorem hermForm_conj {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.c (S.h u w) = S.h w u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HermForm.h, map_sum, map_mul, S.c_invol, S.G_herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def intInv {K : Type} [Field K] [NumberField K] (c : K →+* K) : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom c

theorem intInv_coe {K : Type} [Field K] [NumberField K] (c : K →+* K) (a : 𝓞 K) :
    algebraMap (𝓞 K) K (intInv c a) = c (algebraMap (𝓞 K) K a) := rfl

theorem mem_one_map {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
  exact Submodule.mem_one.mpr ⟨intInv c y, intInv_coe c y⟩

def cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K) :
    Submodule (𝓞 K) K := Bl.ThirdBlockLemmaC.goal1 c C

theorem mem_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K)
    {x : K} : x ∈ cImage c C ↔ c x ∈ C := Iff.rfl

theorem cImage_fg {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by
  haveI : RingHomSurjective (intInv c) :=
    ⟨fun y => ⟨intInv c y, by
      apply RingOfIntegers.ext
      show algebraMap (𝓞 K) K (intInv c (intInv c y)) = algebraMap (𝓞 K) K y
      rw [intInv_coe, intInv_coe, hc]⟩⟩
  let f : K →ₛₗ[intInv c] K :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, intInv_coe] }
  have h : cImage c C = C.map f := by
    ext x
    rw [mem_cImage, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨c x, hx, hc x⟩
    · rintro ⟨y, hy, rfl⟩
      show c (c y) ∈ C
      rw [hc]
      exact hy
  rw [h]
  exact hC.map f

theorem one_le_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (C : Submodule (𝓞 K) K) (h1 : 1 ≤ C) : 1 ≤ cImage c C := by
  intro x hx
  rw [mem_cImage]
  exact h1 (mem_one_map c hx)

theorem relIndex_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (hc : ∀ x, c (c x) = x) (C : Submodule (𝓞 K) K) :
    (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (cImage c C).toAddSubgroup =
      (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup := by
  have h1 : (1 : Submodule (𝓞 K) K).toAddSubgroup
      = (1 : Submodule (𝓞 K) K).toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      exact mem_one_map c hx
    · intro hx
      have h' : c (c x) ∈ (1 : Submodule (𝓞 K) K) := mem_one_map c hx
      rwa [hc] at h'
  have h2 : (cImage c C).toAddSubgroup = C.toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    exact mem_cImage c C
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  · rw [← h1]
  · exact fun y => ⟨c y, hc y⟩

theorem prod_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (x : Fin k → K) (hx : ∀ i, x i ∈ p i) :
    ∏ i, x i ∈ ∏ i, p i := by
  classical
  suffices h : ∀ s : Finset (Fin k), ∏ i ∈ s, x i ∈ ∏ i ∈ s, p i by exact h Finset.univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a) ih

theorem det_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (T : Matrix (Fin k) (Fin k) K)
    (hT : ∀ i j, T i j ∈ p i) : T.det ∈ ∏ i, p i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_prod_sub p (fun i => Tᵀ (σ i) i) fun i => hT i (σ i)) _

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wittMat {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j =>
    if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
    else if i = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0

def WittBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r), S.G.det ≠ 0 →
    ∃ (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K), P.det ≠ 0 ∧ 2 * m ≤ r ∧
      (P.map S.c)ᵀ * S.G * P = wittMat r m g ∧
      ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
        ∑ i, S.c (t i) * g i * t i = 0 → t = 0

def spanIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℕ :=
  (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup

def hGram {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => S.h (b i) (b j)

def LatDegBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b b' : Fin k → Fin r → K),
    (∀ σ, (H σ).PosDef) → B.FG → IsKBasisIn B b → IsKBasisIn B b' →
    latDeg H B b = latDeg H B b'

def IntegralIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (S : HermForm K r)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K),
    B.FG → IsKBasisIn B b → IsIntegralOn S B → (hGram S b).det ≠ 0 →
    ((spanIdx B b : ℕ) : ℝ) ^ 2 ≤ |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)|

def SelfDualIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin r → Fin r → K),
    IsLattice L → IsSelfDual S L → IsKBasisIn L b →
    |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| ≤ ((spanIdx L b : ℕ) : ℝ) ^ 2

def cutSub (K : Type) [Field K] [NumberField K] (r e : ℕ) : Submodule (𝓞 K) (Fin r → K) := UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub K r e

def projGe (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

def diagMet {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) :
    (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun σ => Matrix.diagonal fun i => ((δ σ i : ℝ) : ℂ)

def GradedExtStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r e k k₀ k₁ : ℕ) (δ : (K →+* ℂ) → Fin r → ℝ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (b₀ : Fin k₀ → Fin r → K)
    (b₁ : Fin k₁ → Fin r → K),
    (∀ σ i, 0 < δ σ i) → B.FG → IsKBasisIn B b → IsKBasisIn (B ⊓ cutSub K r e) b₀ →
    IsKBasisIn (B.map (projGe K r e)) b₁ →
    latDeg (diagMet δ) B b ≤
      latDeg (diagMet δ) (B ⊓ cutSub K r e) b₀ + latDeg (diagMet δ) (B.map (projGe K r e)) b₁

def AbsDetStatement : Prop :=
  ∀ (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ), A.PosDef → C.IsHermitian →
    (∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) → ‖C.det‖ ≤ A.det.re

end ReciprocityTheory.MultiplicativeHeights
end
end

