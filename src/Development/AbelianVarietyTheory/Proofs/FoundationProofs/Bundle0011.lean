module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentFiniteOfTriangularSignedIndicators
section
namespace GlobalTheory.LaurentFinite

open AddMonoidAlgebra

def cut (j n : ℤ) : ℤ := if j ≤ |n| then Int.sign n else 0

theorem abs_cut_le (j n : ℤ) : |cut j n| ≤ 1 := by
  unfold cut
  split_ifs
  · rcases lt_trichotomy n 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  · simp

theorem pointwise_lt (j n k : ℤ) (hj : 2 ≤ j) (hn : |n| ≠ j - 1) (hk : |k| ≤ 1)
    (hne : k ≠ cut j n) :
    (2 * j - 2) * (|cut j n| - |k|) < n ^ 2 - (n - cut j n + k) ^ 2 := by
  have hk' : k = -1 ∨ k = 0 ∨ k = 1 := by
    rw [abs_le] at hk; omega
  unfold cut at *
  split_ifs at * with h
  · rcases lt_trichotomy n 0 with h0 | h0 | h0
    · rw [Int.sign_eq_neg_one_of_neg h0] at *
      rw [abs_of_neg h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · exact absurd rfl hne
      · norm_num; nlinarith
      · norm_num; nlinarith
    · subst h0; simp at h; omega
    · rw [Int.sign_eq_one_of_pos h0] at *
      rw [abs_of_pos h0] at h hn
      rcases hk' with rfl | rfl | rfl
      · norm_num; nlinarith
      · norm_num; nlinarith
      · exact absurd rfl hne
  · have h2 : |n| ≤ j - 2 := by omega
    rw [abs_le] at h2
    rcases hk' with rfl | rfl | rfl
    · norm_num; nlinarith [h2.1, h2.2]
    · exact absurd rfl hne
    · norm_num; nlinarith [h2.1, h2.2]

theorem sum_sq_lt {m : ℕ} (j : ℤ) (ν κ : Fin m → ℤ) (hj : 2 ≤ j) (hν : ∀ i, |ν i| ≠ j - 1)
    (hκ : ∀ i, |κ i| ≤ 1) (hs : ∑ i, |κ i| ≤ ∑ i, |cut j (ν i)|)
    (hne : κ ≠ fun i => cut j (ν i)) :
    ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 < ∑ i, ν i ^ 2 := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
  have h1 : ∑ i, (2 * j - 2) * (|cut j (ν i)| - |κ i|)
      < ∑ i, (ν i ^ 2 - (ν i - cut j (ν i) + κ i) ^ 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases h : κ i = cut j (ν i)
      · rw [h]; simp
      · exact (pointwise_lt j _ _ hj (hν i) (hκ i) h).le
    · exact ⟨i0, Finset.mem_univ _, pointwise_lt j _ _ hj (hν i0) (hκ i0) hi0⟩
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
  have : 0 ≤ (2 * j - 2) * (∑ i, |cut j (ν i)| - ∑ i, |κ i|) :=
    mul_nonneg (by omega) (by omega)
  omega

theorem exists_gap {m : ℕ} (ν : Fin m → ℤ) (i0 : Fin m) (h : (m : ℤ) < |ν i0|) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≤ |ν i0| ∧ ∀ i, |ν i| ≠ j - 1 := by
  have hcard : ((Finset.univ.erase i0).image fun i => |ν i|).card < (Finset.Icc (1 : ℤ) m).card := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    have := i0.pos
    simp
    omega
  obtain ⟨t, ht, ht'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Icc] at ht
  refine ⟨t + 1, by omega, by omega, fun i hi => ?_⟩
  by_cases h0 : i = i0
  · subst h0; omega
  · exact ht' (Finset.mem_image.mpr ⟨i, by simp [h0], by omega⟩)

theorem finite_of_triangular (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ)))
    (hB : ∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧
      ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) :
    Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  classical
  set S : Finset (AddMonoidAlgebra ℂ (Fin m → ℤ)) :=
    (Fintype.piFinset fun _ : Fin m => Finset.Icc (-(m : ℤ)) m).image fun ν => single ν 1 with hS
  set N : Submodule B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := Submodule.span B (S : Set _) with hN
  have hsm : ∀ (ν : Fin m → ℤ) (c : ℂ), single ν 1 ∈ N → single ν c ∈ N := by
    intro ν c h
    have := N.smul_of_tower_mem c h
    rwa [smul_single', mul_one] at this
  have key : ∀ (n : ℕ) (ν : Fin m → ℤ), ∑ i, ν i ^ 2 < n → single ν (1 : ℂ) ∈ N := by
    intro n
    induction n with
    | zero =>
      intro ν h
      have : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      simp at h
      omega
    | succ n ih =>
      intro ν h
      by_cases hb : ∀ i, |ν i| ≤ m
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ν, ?_, rfl⟩)
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_Icc.mpr (abs_le.mp (hb i))
      · push Not at hb
        obtain ⟨i0, hi0⟩ := hb
        obtain ⟨j, hj, hj0, hν⟩ := exists_gap ν i0 hi0
        set ε : Fin m → ℤ := fun i => cut j (ν i) with hε
        obtain ⟨s, hsB, hs0, hs⟩ := hB ε fun i => abs_cut_le _ _
        have step : ∀ κ : Fin m → ℤ, (∀ i, |κ i| ≤ 1) → ∑ i, |κ i| ≤ ∑ i, |ε i| → κ ≠ ε →
            single (κ + (ν - ε)) (1 : ℂ) ∈ N := by
          intro κ h1 h2 h3
          apply ih
          have := sum_sq_lt j ν κ hj hν h1 h2 h3
          have e : ∑ i, (κ + (ν - ε)) i ^ 2 = ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by simp [hε, add_comm]
          push_cast at h
          omega
        have h0 : single (ν - ε) (1 : ℂ) ∈ N := by
          have := step 0 (by simp) (by simpa using Finset.sum_nonneg fun i _ => abs_nonneg (ε i)) (by
            intro h0
            have h1 : ε i0 = 0 := by rw [← h0]; rfl
            simp only [hε, cut, hj0, if_true, Int.sign_eq_zero_iff_zero] at h1
            rw [h1] at hj0
            simp at hj0
            omega)
          rwa [zero_add] at this
        have h1 : s * single (ν - ε) (1 : ℂ) ∈ N := N.smul_mem ⟨s, hsB⟩ h0
        have h2 : s * single (ν - ε) (1 : ℂ)
            = ∑ κ ∈ s.coeff.support, single (κ + (ν - ε)) (s.coeff κ) := by
          conv_lhs => rw [← sum_coeff_single s, Finsupp.sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun κ _ => by rw [single_mul_single, mul_one]
        rw [h2, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hs0)] at h1
        have h3 : ∑ κ ∈ s.coeff.support.erase ε, single (κ + (ν - ε)) (s.coeff κ) ∈ N := by
          refine N.sum_mem fun κ hκ => hsm _ _ ?_
          rw [Finset.mem_erase, Finsupp.mem_support_iff] at hκ
          exact step κ (hs κ hκ.2).1 (hs κ hκ.2).2 hκ.1
        have h4 := N.smul_of_tower_mem (s.coeff ε)⁻¹ ((N.add_mem_iff_left h3).mp h1)
        rwa [smul_single', inv_mul_cancel₀ hs0, add_sub_cancel] at h4
  refine Module.Finite.of_fg_top ⟨S, ?_⟩
  rw [eq_top_iff]
  intro x _
  change x ∈ N
  induction x using induction_linear with
  | zero => exact N.zero_mem
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  | single ν c =>
    refine hsm _ _ (key ((∑ i, ν i ^ 2).toNat + 1) ν ?_)
    push_cast
    omega

end GlobalTheory.LaurentFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfDetMemNonZeroDivisors
section
open Module Submodule Function

namespace GlobalTheory

namespace MaximalMinor

section Cramer

variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]

theorem det_smul_eq_sum_det_update (b : Basis ι R F) (v : ι → F) (x : F) :
    b.det v • x = ∑ i, b.det (update v i x) • v i := by
  apply b.equivFun.injective
  have h := Matrix.mulVec_cramer (b.toMatrix v) (b.equivFun x)
  rw [map_smul, Basis.det_apply, ← h]
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Basis.equivFun_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.cramer_apply, Basis.det_apply,
    Basis.toMatrix_update, Basis.toMatrix_apply, mul_comm]

theorem mem_span_of_det_update_mem (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by
  choose a ha using fun i => mem_span_singleton.1 (hx i)
  refine (mem_span_range_iff_exists_fun A).2 ⟨a, ?_⟩
  have h1 : b.det v • (∑ i, a i • v i) = b.det v • x := by
    rw [det_smul_eq_sum_det_update b v x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, smul_assoc, ← algebraMap_smul R (a i), ← algebraMap_smul R (a i), smul_comm]
  apply b.equivFun.injective
  ext j
  have h2 := congrArg (fun y => b.equivFun y j) h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hv).1 h2

theorem span_range_comp_eq (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range _ _)) (span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine mem_span_of_det_update_mem b hσ fun i => ?_
  rw [← comp_update]
  exact h _

end Cramer

end MaximalMinor

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfJointEigenvectors
section
namespace GlobalTheory.JointEigenvectorsIndependent

theorem linearIndependent_of_joint_eigenvectors {ι α M : Type} [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (χ : ι → α → ℂ) (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ)
    (hop : ∀ (a : α) (i : ι), (op a : M → M) (f i) = χ i a • f i)
    (hf : ∀ i : ι, f i ≠ (0 : M)) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert j s hj ih =>
    intro g hg
    rw [Finset.sum_insert hj] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨a, ha⟩ : ∃ a, χ i a ≠ χ j a := Function.ne_iff.mp (fun h => hij (hχ h))
      have h1 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ k a) • f k = 0 := by
        have h := congrArg (op a) hg
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_zero, map_smul, hop, smul_smul] at h
        simpa only [map_smul, hop, smul_smul] using h
      have h2 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ j a) • f k = 0 := by
        have h := congrArg (fun x => χ j a • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (χ j a)] using h
      have h3 : ∑ k ∈ s, (g k * (χ k a - χ j a)) • f k = 0 := by
        have h4 : ∑ k ∈ s, (g k * χ k a) • f k = ∑ k ∈ s, (g k * χ j a) • f k :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun k => g k * (χ k a - χ j a)) h3 i hi
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr ha)
    have hsum : ∑ k ∈ s, g k • f k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hsum, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hf _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentVecMulOfSpanRat
section
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem linearIndependent_vecMul_of_span_rat :
    ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  intro E _ _ R _ _ _ τ hτ hrk n ι _ u hcard hu g
  classical
  have hq : ∀ c : ℚ, τ (algebraMap ℚ E c) = algebraMap ℝ R (algebraMap ℚ ℝ c) := by
    intro c
    have : τ.comp (algebraMap ℚ E) = (algebraMap ℝ R).comp (algebraMap ℚ ℝ) :=
      Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* R => f c) this
  set V : Submodule ℝ (Fin n → R) :=
    Submodule.span ℝ (Set.range fun k => (fun i => τ (u k i))) with hV
  have h1 : ∀ x : Fin n → E, (fun i => τ (x i)) ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range u) := by rw [hu]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero =>
      have : (fun i => τ ((0 : Fin n → E) i)) = 0 := by ext i; simp
      rw [this]; exact V.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => τ ((x + y) i)) = (fun i => τ (x i)) + (fun i => τ (y i)) := by
        ext i; simp
      rw [this]; exact V.add_mem hx hy
    | smul c x _ hx =>
      have : (fun i => τ ((c • x) i)) = (algebraMap ℚ ℝ c) • (fun i => τ (x i)) := by
        ext i
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hq]
      rw [this]; exact V.smul_mem _ hx
  have h2 : ∀ (i : Fin n) (r : R), Pi.single i r ∈ V := by
    intro i r
    have hle : Submodule.span ℝ (Set.range τ) ≤
        V.comap (LinearMap.single ℝ (fun _ : Fin n => R) i) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      have := h1 (Pi.single i e)
      have h' : (fun j => τ ((Pi.single i e : Fin n → E) j)) = Pi.single i (τ e) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      rw [h'] at this
      exact this
    have hr : r ∈ Submodule.span ℝ (Set.range τ) := by rw [hτ]; trivial
    exact hle hr
  have h3 : ∀ y : Fin n → R, y ∈ V := by
    intro y
    rw [← Finset.univ_sum_single y]
    exact V.sum_mem fun i _ => h2 i _
  let φ : (Fin n → R) →ₗ[ℝ] (Fin n → R) :=
    { toFun := fun v => v ᵥ* g.1
      map_add' := fun v w => Matrix.add_vecMul _ _ _
      map_smul' := fun c v => Matrix.smul_vecMul _ _ _ }
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro y _
    have hy : y = φ (y ᵥ* (g⁻¹).1) := by
      simp [φ, Matrix.vecMul_vecMul]
    have hm : φ (y ᵥ* (g⁻¹).1) ∈ V.map φ := Submodule.mem_map_of_mem (h3 _)
    rw [hV, Submodule.map_span, ← Set.range_comp] at hm
    rw [hy]
    exact hm
  · rw [hcard, Module.finrank_pi_fintype, ← hrk]
    simp [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogFactorialPowMulFactorialPowLe
section
namespace GlobalTheory

theorem log_factorial_pow_mul_factorial_pow_le :
    ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R →
      Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ)
        ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  intro n R₀ R hR hR₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hf2 : (0 : ℝ) < (R₀.factorial : ℝ) := by exact_mod_cast R₀.factorial_pos
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have h0 : (0 : ℝ) ≤ (R₀ : ℝ) := Nat.cast_nonneg _
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log hf1
    exact_mod_cast n.factorial_le_pow
  have h2 : Real.log (R₀.factorial : ℝ) ≤ R * Real.log R := by
    have h3 : (R₀.factorial : ℝ) ≤ R ^ R₀ := by
      calc (R₀.factorial : ℝ) ≤ (R₀ : ℝ) ^ R₀ := by exact_mod_cast R₀.factorial_le_pow
        _ ≤ R ^ R₀ := pow_le_pow_left₀ h0 hR₀ _
    calc Real.log (R₀.factorial : ℝ) ≤ Real.log (R ^ R₀) := Real.log_le_log hf2 h3
      _ = R₀ * Real.log R := Real.log_pow _ _
      _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hR₀ hlR
  have hlf : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast n.factorial_pos)
  push_cast
  rw [Real.log_mul (pow_pos hf1 _).ne' (pow_pos hf2 _).ne', Real.log_pow, Real.log_pow,
    Real.log_mul (by linarith) (by linarith)]
  push_cast
  have h4 : (R₀ : ℝ) * Real.log (n.factorial : ℝ) ≤ R * (n * Real.log n) :=
    mul_le_mul hR₀ h1 hlf (by linarith)
  have h5 : (n : ℝ) * Real.log (R₀.factorial : ℝ) ≤ n * (R * Real.log R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 0 ≤ R * (n * Real.log n) := by positivity
  have h7 : 0 ≤ (n : ℝ) * (R * Real.log R) := by positivity
  nlinarith [h4, h5, h6, h7]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwist
section
open Complex Filter Topology

namespace GlobalTheory

theorem lseries_shift_twist (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) :
    LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term_def]
  split_ifs with hn
  · rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast [Nat.cast_sub he]
    ring
  have h1 : (n : ℂ) ^ (e - 1) ≠ 0 := pow_ne_zero _ hn'
  have h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [key]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSquaresEq
section
open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSquares_term (e : ℕ) (c : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (d : ℕ) :
    LSeries.term (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
        c (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) (d * d)
      = LSeries.term c ((e + 1 : ℕ) + 2 * s) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]
  simp only [Nat.sqrt_eq, if_true]
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc,
    ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]
  congr 2
  have h3 : 1 ≤ 3 * e := by omega
  push_cast [Nat.cast_sub h3]
  ring

theorem lseriesSquares_eq : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  intro e χ ψ θ s he hs hb
  have hinj : Function.Injective (fun d : ℕ => d * d) := fun a b h => Nat.mul_self_inj.mp h
  have hterm := lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he
  set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
    χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) →
      LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0 := by
    intro n hn
    have hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n) := fun h => hn ⟨_, h⟩
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [hf, hn']
  have hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := hb n
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
    · have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp
      linarith
  constructor
  · refine (hinj.summable_iff hzero).mp ?_
    exact (show Summable _ from hsum).congr fun d => (hterm d).symm
  · unfold LSeries
    rw [← hinj.tsum_eq (fun n hn => by
      by_contra h
      exact hn (hzero n h))]
    exact tsum_congr hterm

end GlobalTheory
end

