module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsBoundedMultipleNearInteger
section
namespace GlobalTheory.SimultaneousDiophantineApprox

open NumberField

theorem simultaneous_approx {ι : Type} [Fintype ι] (N : ℕ) (hN : 0 < N) (a : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
      ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
  classical
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN

  have hbox : ∀ (j : ℕ) (i : ι), (⌊Int.fract ((j : ℚ) * a i) * N⌋).toNat < N := by
    intro j i
    have h0 : 0 ≤ Int.fract ((j : ℚ) * a i) * N := mul_nonneg (Int.fract_nonneg _) hNq.le
    have h1 : Int.fract ((j : ℚ) * a i) * N < N := by
      have := Int.fract_lt_one ((j : ℚ) * a i)
      nlinarith
    have hlt : ⌊Int.fract ((j : ℚ) * a i) * N⌋ < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h1)
    have hnn : 0 ≤ ⌊Int.fract ((j : ℚ) * a i) * N⌋ := Int.floor_nonneg.mpr h0
    omega
  let f : Fin (N ^ Fintype.card ι + 1) → (ι → Fin N) := fun j i => ⟨_, hbox j i⟩

  have key : ∀ x y : Fin (N ^ Fintype.card ι + 1), x < y → f x = f y →
      ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
        ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
    intro x y hxy hf
    have hxy' : (x : ℕ) < y := hxy
    have hy := y.2
    refine ⟨y - x, by omega, by omega, fun i => ⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋, fun i => ?_⟩
    have hv := congrArg Fin.val (congrFun hf i)
    simp only [f] at hv
    have hx0 : 0 ≤ Int.fract ((x : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hy0 : 0 ≤ Int.fract ((y : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hfl : ⌊Int.fract (((x : ℕ) : ℚ) * a i) * N⌋ = ⌊Int.fract (((y : ℕ) : ℚ) * a i) * N⌋ := by
      have := Int.floor_nonneg.mpr hx0
      have := Int.floor_nonneg.mpr hy0
      omega
    have hclose := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have heq : (((y - x : ℕ) : ℕ) : ℚ) * a i - ((⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋ : ℤ) : ℚ) =
        Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i) := by
      rw [Nat.cast_sub hxy'.le]
      unfold Int.fract
      push_cast
      ring
    rw [heq, le_div_iff₀ hNq]
    have hm : |Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i)| * N =
        |Int.fract (((x : ℕ) : ℚ) * a i) * N - Int.fract (((y : ℕ) : ℚ) * a i) * N| := by
      rw [← sub_mul, abs_mul, abs_of_pos hNq, abs_sub_comm]
    rw [hm]
    exact hclose.le
  obtain ⟨x, y, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h hf
  · exact key y x h hf.symm

theorem exists_bounded_multiple_near_integer (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E ((m : E) * x - y)‖ < 1 := by
  classical
  set b := integralBasis E

  set C : ℝ := ∑ i, ∑ σ : E →+* ℂ, ‖σ (b i)‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => norm_nonneg _
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have hN0 : 0 < N := by exact_mod_cast hC0.trans_lt hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine ⟨N ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)), fun x => ?_⟩
  obtain ⟨m, hm0, hmN, z, hz⟩ := simultaneous_approx N hN0 (b.repr x)
  refine ⟨m, ∑ i, (z i : E) * b i, hm0, hmN, ?_, ?_⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E (z i)))
    · rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
  ·
    have hx : (m : E) * x - ∑ i, (z i : E) * b i =
        ∑ i, ((((m : ℚ) * b.repr x i - z i : ℚ)) : E) * b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [hx, pi_norm_lt_iff one_pos]
    intro σ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [canonicalEmbedding.apply_at, map_sum]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum (g := fun i => 1 / (N : ℝ) * ∑ τ : E →+* ℂ, ‖τ (b i)‖)
      fun i _ => ?_) ?_
    · rw [map_mul, norm_mul, map_ratCast, Complex.norm_ratCast]
      refine mul_le_mul ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)) (norm_nonneg _) (by positivity)
      have h := Rat.cast_le (K := ℝ) |>.mpr (hz i)
      rwa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] at h
    · rw [← Finset.mul_sum, ← hC, one_div_mul_eq_div, div_lt_one hNr]
      exact hN

end GlobalTheory.SimultaneousDiophantineApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCommonSmulMem
section
namespace GlobalTheory.CommonSmulMembership

theorem exists_common_smul_mem {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (P : Submonoid O) {L L' : Submodule O M} (hL : Submodule.FG L)
    (h : ∀ v ∈ L, ∃ s ∈ P, s • v ∈ L') : ∃ s ∈ P, ∀ v ∈ L, s • v ∈ L' := by
  classical
  obtain ⟨S, rfl⟩ := hL
  choose f hfP hf using h
  let g : S → O := fun x => f x (Submodule.subset_span x.2)
  refine ⟨∏ x : S, g x, P.prod_mem (fun x _ => hfP _ _), ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    have hx' : x ∈ S := hx
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact L'.smul_mem _ (hf x _)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L'.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L'.smul_mem a hx

end GlobalTheory.CommonSmulMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEqSumIndicatorOfRightInvariant
section
open Matrix

namespace GlobalTheory

namespace LatticeIndicator

theorem exists_injective_comp_eq_of_surjective {k V W : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] (f g : V →ₗ[k] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : V →ₗ[k] V, Function.Injective e ∧ g ∘ₗ e = f := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have hrk : Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker g) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hf] at h1
    rw [LinearMap.range_eq_top.2 hg] at h2
    omega
  let θ := LinearEquiv.ofFinrankEq _ _ hrk
  obtain ⟨p, hp⟩ := (LinearMap.ker f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  have hgs : ∀ w, g (s w) = w := fun w => LinearMap.congr_fun hs w
  have key : ∀ v, g (s (f v) + (θ (p v) : V)) = f v := fun v => by
    rw [map_add (f := _), hgs, (θ (p v)).2, add_zero]
  refine ⟨s ∘ₗ f + (LinearMap.ker g).subtype ∘ₗ θ.toLinearMap ∘ₗ p, ?_, LinearMap.ext key⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : s (f v) + (θ (p v) : V) = 0 := hv
  have hfv : f v = 0 := by rw [← key v, hv', map_zero]
  rw [hfv, map_zero, zero_add] at hv'
  have h1 : p v = 0 := θ.map_eq_zero_iff.1 (Subtype.ext hv')
  have h2 : p v = ⟨v, hfv⟩ := LinearMap.congr_fun hp ⟨v, hfv⟩
  rw [h2] at h1
  exact congrArg Subtype.val h1

theorem exists_matrix_of_span_eq_top_field {k W n : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Fintype n] [DecidableEq n] (a b : n → W) (ha : Submodule.span k (Set.range a) = ⊤)
    (hb : Submodule.span k (Set.range b) = ⊤) :
    ∃ g : Matrix n n k, g.det ≠ 0 ∧ ∀ j, a j = ∑ i, g i j • b i := by
  obtain ⟨e, he, hge⟩ := exists_injective_comp_eq_of_surjective
    (Fintype.linearCombination k a) (Fintype.linearCombination k b)
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ha])
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hb])
  refine ⟨LinearMap.toMatrix' e, ?_, fun j => ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact ((LinearMap.isUnit_iff_isUnit_det e).1
      ((LinearMap.isUnit_iff_ker_eq_bot e).2 (LinearMap.ker_eq_bot.2 he))).ne_zero
  · have := LinearMap.congr_fun hge (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul] at this
    rw [← this]
    simp [Fintype.linearCombination_apply, LinearMap.toMatrix'_apply]

end LatticeIndicator

open LatticeIndicator

section Main

variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

end Main

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableProdPi
section
namespace GlobalTheory.SummableProdPi

theorem summable_prod_pi {J A : Type} [inst : Fintype J] (f : J → A → ℝ)
    (h0 : ∀ (j : J) (a : A), (0 : ℝ) ≤ f j a) (hs : ∀ j : J, Summable (f j)) :
    Summable fun (n : J → A) ↦ ∏ j : J, f j (n j) := by
  classical
  have hnn : ∀ n : J → A, 0 ≤ ∏ j : J, f j (n j) :=
    fun n => Finset.prod_nonneg fun j _ => h0 j (n j)
  refine summable_of_sum_le (c := ∏ j : J, ∑' a, f j a) hnn fun s => ?_
  have hsub : s ⊆ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hn
  calc ∑ n ∈ s, ∏ j : J, f j (n j)
      ≤ ∑ n ∈ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)),
          ∏ j : J, f j (n j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hnn n
    _ = ∏ j : J, ∑ a ∈ s.image (fun n : J → A => n j), f j a :=
        (Finset.prod_univ_sum (fun j : J => s.image (fun n : J → A => n j)) f).symm
    _ ≤ ∏ j : J, ∑' a, f j a := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact Finset.sum_nonneg fun a _ => h0 j a
        · intro j _
          exact (hs j).sum_le_tsum _ fun a _ => h0 j a

end GlobalTheory.SummableProdPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TailSumLtOne
section
namespace GlobalTheory

theorem tail_sum_lt_one {ι : Type*} (idx : ι → ℕ) (ρ n : ℕ) (hn : 4 * ρ + 4 ≤ n) (h2 : ∀ i, 2 ≤ idx i)
    (hc : ∀ m, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (2 * ρ)) (c : ι → ℂ) (hcb : ∀ i, ‖c i‖ ≤ (idx i : ℝ) ^ (-(n : ℝ) / 2)) :
    Summable (fun i => ‖c i‖) ∧ ∑' i, ‖c i‖ ≤ 0.65 := by
  classical
  have hterm : ∀ i, ‖c i‖ ≤ 1 / ((idx i : ℝ) ^ (2 * ρ) * (idx i : ℝ) ^ 2) := by
    intro i
    have h1 : (1 : ℝ) ≤ idx i := by exact_mod_cast (le_trans (by norm_num) (h2 i))
    refine (hcb i).trans ?_
    have hn' : (4 * ρ + 4 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : -(n : ℝ) / 2 ≤ -((2 * ρ + 2 : ℕ) : ℝ) := by push_cast; linarith
    refine (Real.rpow_le_rpow_of_exponent_le h1 hle).trans (le_of_eq ?_)
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, pow_add, one_div]
  have hz := hasSum_zeta_two
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖c i‖ ≤ 0.65 := by
    intro s
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image idx) (g := idx)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    have hfib : ∀ m ∈ s.image idx, ∑ i ∈ s with idx i = m, ‖c i‖ ≤ 1 / (m : ℝ) ^ 2 := by
      intro m hm
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hm
      have hpos : (0 : ℝ) < idx j := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (h2 j))
      have hcard : ((s.filter (fun i => idx i = idx j)).card : ℝ) ≤ (idx j : ℝ) ^ (2 * ρ) := by
        have h3 : (s.filter (fun i => idx i = idx j)).card ≤ {i | idx i = idx j}.ncard := by
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard ?_ (hc _).1
          intro i hi
          simpa using (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
        exact_mod_cast h3.trans (hc _).2
      calc ∑ i ∈ s with idx i = idx j, ‖c i‖
          ≤ (s.filter (fun i => idx i = idx j)).card •
              (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            refine Finset.sum_le_card_nsmul _ _ _ ?_
            intro i hi
            have := hterm i
            rwa [(Finset.mem_filter.1 hi).2] at this
        _ ≤ (idx j : ℝ) ^ (2 * ρ) * (1 / ((idx j : ℝ) ^ (2 * ρ) * (idx j : ℝ) ^ 2)) := by
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1 / (idx j : ℝ) ^ 2 := by field_simp
    refine (Finset.sum_le_sum hfib).trans ?_
    have h1 : 1 ∉ s.image idx := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
      have := h2 j
      omega
    have h4 := sum_le_hasSum (insert 1 (s.image idx)) (fun m _ => by positivity) hz
    rw [Finset.sum_insert h1] at h4
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have h5 : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by gcongr
    norm_num at h4 h5 ⊢
    linarith
  have hs : Summable (fun i => ‖c i‖) := summable_of_sum_le (fun i => norm_nonneg _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end GlobalTheory
end

