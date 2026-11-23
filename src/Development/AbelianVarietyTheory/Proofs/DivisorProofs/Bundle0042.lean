module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankNormalFormMatrixField
section
open scoped Matrix

namespace GlobalTheory

theorem rank_normal_form_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalMultiplierOfComplexMultiplier
section
namespace GlobalTheory

open Module

theorem relation_descends_along_functional (K A B : Type) [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B)
    (hrd : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f) (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ W) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (φ : ℂ →+ K) (hφ : ∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c)
    {ι : Type} [Fintype ι] (x : ι → A) (hx : ∀ s, x s ∈ W) (c : ι → ℂ)
    (h : ∑ s, c s • rd (x s) = 0) : ∑ s, φ (c s) • x s = 0 := by
  classical
  obtain ⟨n, ⟨bW⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K W) := ⟨_, ⟨Module.finBasis K W⟩⟩
  have hli : LinearIndependent K (fun j => (bW j : A)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli' := hW n (fun j => (bW j : A)) (fun j => (bW j).2) hli
  have hcoord : ∃ α : ι → Fin n → K, ∀ s, x s = ∑ j, α s j • (bW j : A) := by
    refine ⟨fun s j => bW.repr ⟨x s, hx s⟩ j, fun s => ?_⟩
    have h1 := congrArg (fun v : W => (v : A)) (bW.sum_repr ⟨x s, hx s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := hcoord
  have hrdx : ∀ s, rd (x s) = ∑ j, σ (α s j) • rd (bW j : A) := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hα s, map_sum]
    simp only [hrd]
  have hcoef : ∀ j, ∑ s, c s * σ (α s j) = 0 := by
    have h' : ∑ j, (∑ s, c s * σ (α s j)) • rd (bW j : A) = 0 := by
      rw [← h]
      simp only [hrdx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => Fintype.linearIndependent_iff.mp hli' _ h' j
  have hgoal : ∑ s, φ (c s) • x s = ∑ j, (∑ s, φ (c s) * α s j) • (bW j : A) := by
    simp only [hα, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hgoal]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h5 : ∑ s, φ (c s) * α s j = φ (∑ s, c s * σ (α s j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm (c s), hφ]
    exact mul_comm _ _
  rw [h5, hcoef j, map_zero, zero_smul]

theorem exists_functional_ne_zero_of_embedding (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K ℂ, f m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff K m).mp hcon)
  refine ⟨f.toAddMonoidHom, fun a c => ?_, hf⟩
  have hsmul : σ a * c = a • c := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp only [LinearMap.toAddMonoidHom_coe, hsmul, LinearMap.map_smul, smul_eq_mul]

theorem exists_rational_multiplier_of_complex :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  classical
  intro K A B _ _ _ _ _ σ rd hrd V V' _ _ hVV h hspan hne
  have : FiniteDimensional K ↥(V * V') :=
    Module.Finite.iff_fg.mpr (Submodule.FG.mul (Module.Finite.iff_fg.mp inferInstance)
      (Module.Finite.iff_fg.mp inferInstance))
  have hrdsum : ∀ {m : ℕ} (a : Fin m → K) (v : Fin m → A),
      rd (∑ j, a j • v j) = ∑ j, σ (a j) • rd (v j) := by
    intro m a v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hrd]
  have hexp : ∀ {U : Submodule K A} {m : ℕ} (b : Basis (Fin m) K U) (u : U),
      (u : A) = ∑ j, b.repr u j • (b j : A) := by
    intro U m b u
    have h1 := congrArg (fun v : U => (v : A)) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨n, ⟨bV⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V) := ⟨_, ⟨Module.finBasis K V⟩⟩
  obtain ⟨n', ⟨bV'⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V') := ⟨_, ⟨Module.finBasis K V'⟩⟩
  have hC : ∀ i, ∃ C : Fin n' → ℂ, h * rd (bV i : A) = ∑ j, C j • rd (bV' j : A) := by
    intro i
    have hm := hspan _ (bV i).2
    have hsub : Submodule.span ℂ (rd '' (V' : Set A)) ≤
        Submodule.span ℂ (Set.range fun j => rd (bV' j : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have e : u = ∑ j, bV'.repr ⟨u, hu⟩ j • (bV' j : A) := hexp bV' ⟨u, hu⟩
      rw [e, hrdsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨C, hCe⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hsub hm)
    exact ⟨C, hCe.symm⟩
  choose C hC using hC
  have hi0 : ∃ i, h * rd (bV i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfne⟩ := hne
    apply hfne
    have e : f = ∑ j, bV.repr ⟨f, hf⟩ j • (bV j : A) := hexp bV ⟨f, hf⟩
    rw [e, hrdsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, hcon i, smul_zero]
  obtain ⟨i0, hi0⟩ := hi0
  have hj0 : ∃ j, C i0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hi0
    rw [hC i0]
    exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_smul]
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨φ, hφ, hφne⟩ := exists_functional_ne_zero_of_embedding K σ (C i0 j0) hj0
  obtain ⟨T, hT⟩ : ∃ T : V →ₗ[K] V', ∀ i, T (bV i) = ∑ j, φ (C i j) • bV' j :=
    ⟨bV.constr K (fun i => ∑ j, φ (C i j) • bV' j), fun i => bV.constr_basis K _ i⟩
  have hTA : ∀ i, ((T (bV i) : V') : A) = ∑ j, φ (C i j) • (bV' j : A) := by
    intro i
    rw [hT]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hbasis : ∀ i k, ((T (bV i) : V') : A) * (bV k : A) = (bV i : A) * ((T (bV k) : V') : A) := by
    intro i k
    have key := relation_descends_along_functional K A B σ rd hrd (V * V') hVV φ hφ
      (ι := Fin n' ⊕ Fin n')
      (Sum.elim (fun j => (bV k : A) * (bV' j : A)) (fun j => (bV i : A) * (bV' j : A)))
      (by
        rintro (j | j)
        · exact Submodule.mul_mem_mul (bV k).2 (bV' j).2
        · exact Submodule.mul_mem_mul (bV i).2 (bV' j).2)
      (Sum.elim (fun j => C i j) (fun j => - C k j))
      (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, map_mul, neg_smul, Finset.sum_neg_distrib]
        simp only [← mul_smul_comm, ← Finset.mul_sum, ← hC]
        ring)
    rw [Fintype.sum_sum_type] at key
    simp only [Sum.elim_inl, Sum.elim_inr, map_neg, neg_smul, Finset.sum_neg_distrib,
      ← mul_smul_comm, ← Finset.mul_sum] at key
    rw [hTA, hTA, mul_comm _ ((bV k : V) : A)]
    rw [mul_neg] at key
    exact add_neg_eq_zero.mp key
  have hleft : ∀ i (g : V), ((T (bV i) : V') : A) * (g : A) = (bV i : A) * ((T g : V') : A) := by
    intro i g
    have h2 := bV.ext (f₁ := (LinearMap.mulLeft K ((T (bV i) : V') : A)).comp V.subtype)
      (f₂ := (LinearMap.mulLeft K ((bV i : V) : A)).comp (V'.subtype.comp T))
      (fun k => by simpa using hbasis i k)
    simpa using LinearMap.congr_fun h2 g
  refine ⟨T, ?_, fun f g => ?_⟩
  · intro hT0
    have h1 : T (bV i0) = 0 := by rw [hT0, LinearMap.zero_apply]
    rw [hT] at h1
    exact hφne (Fintype.linearIndependent_iff.mp bV'.linearIndependent _ h1 j0)
  · have h2 := bV.ext (f₁ := (LinearMap.mulRight K (g : A)).comp (V'.subtype.comp T))
      (f₂ := (LinearMap.mulRight K ((T g : V') : A)).comp V.subtype)
      (fun i => by simpa using hleft i g)
    simpa using LinearMap.congr_fun h2 f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalOrthogonalProjectionSemilinear
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_rational_orthogonal_projection_of_finrank_le (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by
  intro d
  induction d with
  | zero =>
    intro N hN x
    refine ⟨0, N.zero_mem, ?_⟩
    have hb : N = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; omega
    intro m hm
    subst hb
    rw [Submodule.mem_bot] at hm
    subst hm
    simp
  | succ d ih =>
    intro N hN x
    by_cases h : ∃ v ∈ N, j v ≠ 0
    · obtain ⟨v, hvN, hv⟩ := h
      let f : (Fin n → K) →ₛₗ[σ] ℂ := (innerₛₗ ℂ (j v)).comp j
      have hf : ∀ z, f z = ⟪j v, j z⟫_ℂ := fun z => rfl
      let N' := N ⊓ LinearMap.ker f
      have hvv : ⟪j v, j v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
      have hlt : N' < N := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hvN' : v ∈ N' := heq ▸ hvN
        have h2 : f v = 0 := hvN'.2
        rw [hf] at h2
        exact hvv h2
      have hN' : Module.finrank K N' ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨a, ha⟩ := hj v v
      obtain ⟨b, hb⟩ := hj v x
      have hsa : σ a ≠ 0 := by rw [ha]; exact hvv
      obtain ⟨y', hy'N, hy'⟩ := ih N' hN' (x - (b / a) • v)
      refine ⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩
      have key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y' := by
        simp only [map_add (f := _), map_sub]; abel
      rw [key]
      have hy'k : ⟪j v, j y'⟫_ℂ = 0 := by
        have : f y' = 0 := hy'N.2
        rwa [hf] at this
      have hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0 := by
        rw [inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb,
          map_div₀, div_mul_cancel₀ _ hsa]
        ring
      intro m hm
      obtain ⟨e, he⟩ := hj v m
      have hm' : m - (e / a) • v ∈ N' := by
        refine ⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩
        show f (m - (e / a) • v) = 0
        rw [hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀,
          div_mul_cancel₀ _ hsa, sub_self]
      have hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v) := by
        rw [map_sub, map_smulₛₗ]; abel
      rw [hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]
      exact hy' _ hm'
    · push_neg at h
      refine ⟨0, N.zero_mem, ?_⟩
      intro m hm
      rw [h m hm, inner_zero_left]

theorem exists_mem_sub_mem_orthogonal_span_of_inner_mem_range : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  intro K _ σ W _ _ _ n j hj N x
  obtain ⟨y, hyN, hy⟩ := exists_rational_orthogonal_projection_of_finrank_le K σ W n j hj _ N le_rfl x
  refine ⟨y, hyN, ?_⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨m, hm, rfl⟩ := hu
    exact hy m hm
  | zero => exact inner_zero_left _
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularExponentOfSumSqEq
section
namespace GlobalTheory

theorem exists_regular_exponent_of_sum_sq_eq :
    ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d →
      (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) →
      ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d →
      (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) →
      ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by
  classical
  intro q d a hq hd hinv hsum hdiv
  have h1 : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
  have hN : 0 < q ^ d - 1 := by omega
  have hqd : q ^ d ≡ 1 [MOD q ^ d - 1] :=
    ((Nat.modEq_iff_dvd' h1.le).2 dvd_rfl).symm
  generalize q ^ d - 1 = N at *
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
    omega
  refine ⟨k, hk, fun i hi hid hki => ?_⟩
  have hex : ∃ e, 0 < e ∧ k * q ^ e ≡ k [MOD N] := ⟨i, hi, hki⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ i := Nat.find_min' hex ⟨hi, hki⟩
  have hmin : ∀ m, 0 < m → m < Nat.find hex → ¬ k * q ^ m ≡ k [MOD N] :=
    fun m hm hlt h => Nat.find_min hex hlt ⟨hm, h⟩
  generalize Nat.find hex = e at hspec hle hmin
  obtain ⟨he, hke⟩ := hspec
  have hmul : ∀ m, k * q ^ (e * m) ≡ k [MOD N] := by
    intro m
    induction m with
    | zero => simp [Nat.ModEq]
    | succ m ih =>
      have : k * q ^ (e * (m + 1)) = k * q ^ (e * m) * q ^ e := by ring
      rw [this]
      exact (ih.mul_right _).trans hke
  have hmod : d % e = 0 := by
    by_contra h
    apply hmin (d % e) (Nat.pos_of_ne_zero h) (Nat.mod_lt _ he)
    have h2 : k * q ^ d = k * q ^ (e * (d / e)) * q ^ (d % e) := by
      rw [mul_assoc, ← pow_add, Nat.div_add_mod]
    have h3 : k * q ^ d ≡ k [MOD N] := by simpa using hqd.mul_left k
    rw [h2] at h3
    exact ((hmul (d / e)).mul_right _).symm.trans h3
  obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s ≤ 1 := by omega
    have : e * s ≤ e * 1 := Nat.mul_le_mul_left _ this
    omega
  have hdv : (s : ℤ) ∣ a k := hdiv s e k (by rw [hs, mul_comm]) hke
  have hsq : (s : ℤ) ^ 2 ≤ a k ^ 2 :=
    Int.le_of_dvd (by positivity) (pow_dvd_pow_of_dvd hdv 2)
  have key : ∀ i j, i < j → j < e → ¬ k * q ^ i ≡ k * q ^ j [MOD N] := by
    intro i j hij hj h
    apply hmin (i + (e - j)) (by omega) (by omega)
    have h2 := h.mul_right (q ^ (e - j))
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, Nat.add_sub_cancel' hj.le] at h2
    exact h2.trans hke
  have hinj : Set.InjOn (fun i => k * q ^ i % N) (Finset.range e : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (key i j h' hj)
    · exact h'
    · exact absurd (Eq.symm h) (key j i h' hi)
  have hsub : (Finset.range e).image (fun i => k * q ^ i % N) ⊆ Finset.range N := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hN)
  have hle2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => a k ^ 2) hsub
    (fun _ _ _ => by positivity)
  rw [Finset.sum_image hinj, hsum] at hle2
  have heq : ∑ i ∈ Finset.range e, a (k * q ^ i % N) ^ 2 = (e : ℤ) * a k ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [← hinv k _ i (Nat.mod_modEq _ _).symm])]
    simp
  rw [heq, hs] at hle2
  push_cast at hle2
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs2
  have := le_of_mul_le_mul_left hle2 he'
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCompAlgebraMapEq
section
universe u_1 u_2 u_3

namespace GlobalTheory.InjectiveAlgebraHomExistence

theorem exists_algHom_of_injective {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hK
  exact ⟨IsAlgClosed.lift⟩

theorem exists_ringHom_comp_algebraMap_eq {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker ψ) ⊥ (by
      intro r hr
      have h0 : algebraMap R S r = 0 := by simpa using hr
      have : r = 0 := hinj (by simpa using h0)
      simp [this])
  let f : R ⧸ RingHom.ker ψ →+* S ⧸ Q := Ideal.quotientMap Q (algebraMap R S) hQp.ge
  have hf : Function.Injective f := Ideal.quotientMap_injective' hQp.le
  letI : Algebra (R ⧸ RingHom.ker ψ) (S ⧸ Q) := f.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker ψ) (S ⧸ Q) := by
    constructor
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hs⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨P.map (Ideal.Quotient.mk _), hP.map _, ?_⟩
    have hc : (algebraMap (R ⧸ RingHom.ker ψ) (S ⧸ Q)).comp (Ideal.Quotient.mk _)
        = (Ideal.Quotient.mk Q).comp (algebraMap R S) := by
      ext r
      rfl
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hs, map_zero]
  obtain ⟨g⟩ : Nonempty ((S ⧸ Q) →ₐ[R ⧸ RingHom.ker ψ] K) :=
    exists_algHom_of_injective hf (RingHom.kerLift_injective ψ)
  refine ⟨(g : (S ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := g.commutes (Ideal.Quotient.mk _ r)
  exact this

end GlobalTheory.InjectiveAlgebraHomExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfAdjointEndoRelatingHermitianForms
section
open Matrix

namespace GlobalTheory

theorem herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by
  funext i
  simp only [mulVec, dotProduct, Pi.star_apply, star_sum, map_apply, star_mul', star_star]

theorem herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hz : star v ≠ 0 := by
    intro h; apply hv; simpa using congrArg star h
  have := hpos (star v) hz
  rw [star_star, hHv, dotProduct_zero] at this
  simp at this

theorem herm_gamma : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  intro g H₁ H₂ h1 h2 hpos
  have hdet : IsUnit H₁.det := isUnit_iff_ne_zero.2 (herm_gamma_det_ne_zero H₁ hpos)
  refine ⟨Matrix.toLin' ((H₁⁻¹ * H₂).map star), ?_, ?_⟩
  · intro z w
    rw [Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · intro z w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec,
      herm_gamma_map_mulVec_dot, mulVec_mulVec]
    congr 2
    have hT : ((H₁⁻¹ * H₂).map star)ᵀ = (H₁⁻¹ * H₂)ᴴ := rfl
    rw [hT, conjTranspose_mul, h2.eq, conjTranspose_nonsing_inv, h1.eq, Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherBis
section
universe u_1 u_2

namespace GlobalTheory.BandLemmaFirst

theorem main :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ}
      {X Y : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j Y → d1 ℓ j (X + Y)) := by
  intro d1 k _ ι _ _ ℓ j X Y hX hY r s h
  show (X + Y) r s = 0
  rw [Matrix.add_apply, hX r s h, hY r s h, add_zero]

end GlobalTheory.BandLemmaFirst
end

