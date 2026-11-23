module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
section
namespace GlobalTheory.CompanionTheory.LuFields

open Matrix

theorem entries_mem_of_eq_mul {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (F : IntermediateField K L) (C v w : Matrix (Fin n) (Fin n) L) (hC : ∀ i k, C i k ∈ F)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0) (h : C = v * w) :
    (∀ i k, v i k ∈ F) ∧ (∀ i k, w i k ∈ F) := by
  have hC' : ∀ i k, ∑ l, v i l * w l k ∈ F := fun i k => by
    have := hC i k
    rwa [h, Matrix.mul_apply] at this
  have key : ∀ m : ℕ, ∀ i k : Fin n, ((i : ℕ) < m ∨ (k : ℕ) < m) → v i k ∈ F ∧ w i k ∈ F := by
    intro m
    induction m with
    | zero => intro i k hik; exact absurd hik (by omega)
    | succ m ih =>
      have hw : ∀ i k : Fin n, (i : ℕ) = m → i ≤ k → w i k ∈ F := by
        intro i k hi hik
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hv1, one_mul] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase i, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hv0 i l hgt, zero_mul]
            exact F.zero_mem
        simpa using F.sub_mem hsum hrest
      have hv : ∀ i k : Fin n, (k : ℕ) = m → k < i → v i k ∈ F := by
        intro i k hk hki
        have hwk : w k k ∈ F := hw k k hk le_rfl
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase k, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hw0 l k hgt, mul_zero]
            exact F.zero_mem
        have h1 : v i k * w k k ∈ F := by simpa using F.sub_mem hsum hrest
        have h2 := F.mul_mem h1 (F.inv_mem hwk)
        rwa [mul_assoc, mul_inv_cancel₀ (hwd k), mul_one] at h2
      intro i k hik
      by_cases h' : (i : ℕ) < m ∨ (k : ℕ) < m
      · exact ih i k h'
      · push_neg at h'
        rcases le_or_gt i k with hle | hlt
        · have hi : (i : ℕ) = m := by have := Fin.le_def.1 hle; omega
          refine ⟨?_, hw i k hi hle⟩
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq, hv1]
            exact F.one_mem
          · rw [hv0 i k hlt']
            exact F.zero_mem
        · have hk : (k : ℕ) = m := by have := Fin.lt_def.1 hlt; omega
          refine ⟨hv i k hk hlt, ?_⟩
          rw [hw0 i k hlt]
          exact F.zero_mem
  exact ⟨fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).1,
    fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).2⟩

theorem adjoin_entries_eq (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L) (hA : A.det ≠ 0)
    (hu1 : ∀ k, u k k = 1) (hu0 : ∀ l k, l < k → u l k = 0)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (h : A.map (algebraMap K L) * u = v * w) :
    IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) =
      IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  have hwT : w.BlockTriangular id := by
    intro l k hkl
    exact hw0 l k hkl
  have hdetw : w.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hwT]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hwd k
  have := Matrix.invertibleOfIsUnitDet w (isUnit_iff_ne_zero.2 hdetw)
  have hwiT : w⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hwT
  have hwwi : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w (isUnit_iff_ne_zero.2 hdetw)
  have hwid : ∀ k, w⁻¹ k k ≠ 0 := by
    intro k hk
    have e := congrFun (congrFun hwwi k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k, hk, mul_zero, Matrix.one_apply_eq] at e
    · exact zero_ne_one e
    · intro l _ hlk
      rcases lt_or_gt_of_ne hlk with hlt | hgt
      · rw [hw0 k l hlt, zero_mul]
      · rw [hwiT hgt, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA)
  have hBAm : A⁻¹.map (algebraMap K L) * A.map (algebraMap K L) = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC' : A⁻¹.map (algebraMap K L) * v = u * w⁻¹ := by
    have hu : u = A⁻¹.map (algebraMap K L) * v * w := by
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hBAm, Matrix.one_mul]
    rw [hu, Matrix.mul_assoc, hwwi, Matrix.mul_one]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A⁻¹.map (algebraMap K L) * v) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ u w⁻¹ hC hu1 hu0 (fun l k hkl => hwiT hkl) hwid hC').1 p.1 p.2
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A.map (algebraMap K L) * u) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ v w hC hv1 hv0 hw0 hwd h).1 p.1 p.2

end GlobalTheory.CompanionTheory.LuFields
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportional
section
namespace GlobalTheory.CompanionTheory.WedgeSpan

theorem span_of_wedge_proportional (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (b e : Fin n → V) (t : Ω) (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (hbe : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) := by
  classical
  by_contra hx
  have hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨he, hx⟩
  have hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e := by
    have := congrArg Subtype.val hbe
    simpa using this
  have htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b :=
    by funext k; simp [Matrix.vecTail]
  have hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e :=
    by funext k; simp [Matrix.vecTail]
  have h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0 :=
    (ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp) (Fin.succ_ne_zero i).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero] at h0
  have h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, hte]
    rcases h0 with h | h
    · exact absurd h ht
    · simpa using h
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv
  apply hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))
  rw [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
  exact Subtype.ext h1

end GlobalTheory.CompanionTheory.WedgeSpan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRank
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PowerDerivation

open Polynomial

theorem exists_natCast_of_pow_eq (k : Type) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (μ : k) (h : μ ^ p = μ) : ∃ i < p, μ = (i : k) := by
  classical
  have hone : 1 < p := hp.out.one_lt
  have hP : (X ^ p - X : k[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero (R := k) hone
  have hdeg : (X ^ p - X : k[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X (R := k) hone
  haveI : ExpChar k p := ExpChar.prime hp.out
  set S : Finset k := (Finset.range p).image (fun i : ℕ => (i : k)) with hS
  have hcard : S.card = p := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio k p (by simpa using ha) (by simpa using hb) hab
  have hsub : S ⊆ (X ^ p - X : k[X]).roots.toFinset := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    have hi : ((i : k)) ^ p = i := by
      have := map_natCast (frobenius k p) i
      rwa [frobenius_def] at this
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [IsRoot, hi]
  have hEq : S = (X ^ p - X : k[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard]
    calc _ ≤ Multiset.card (X ^ p - X : k[X]).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = p := hdeg
  have hμ : μ ∈ S := by
    rw [hEq, Multiset.mem_toFinset, mem_roots hP]
    simp [IsRoot, h]
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hμ
  exact ⟨i, Finset.mem_range.1 hi, rfl⟩

theorem iSup_eigenspace_eq_top (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (R : Type) [AddCommGroup R] [Module k R] [Module.Finite k R]
    (T : Module.End k R) (h : ∀ a : R, (⇑T)^[p] a = T a) :
    ⨆ μ : k, T.eigenspace μ = ⊤ := by
  have hsep : (X ^ p - X : k[X]).Separable := galois_poly_separable p p dvd_rfl
  have h0 : aeval T (X ^ p - X : k[X]) = 0 := by
    ext a
    simp [Module.End.pow_apply, h a]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree h0
  have := Module.End.iSup_maxGenEigenspace_eq_top T
  simpa [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using this

section Main

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

noncomputable def powerSum (D : Derivation k R R) (z : R) (p : ℕ) :
    (Fin p → LinearMap.ker (D : R →ₗ[k] R)) →ₗ[k] R where
  toFun a := ∑ i, (a i : R) * z ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

theorem powerSum_apply (D : Derivation k R R) (z : R) (p : ℕ)
    (a : Fin p → LinearMap.ker (D : R →ₗ[k] R)) :
    powerSum D z p a = ∑ i, (a i : R) * z ^ (i : ℕ) := rfl

theorem derivation_pow_of_eq (D : Derivation k R R) {z : R} (hz : D z = z) (n : ℕ) :
    D (z ^ n) = (n : R) * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, D.leibniz, ih, hz]
    simp only [smul_eq_mul]
    push_cast
    ring

theorem derivation_inv_of_eq (D : Derivation k R R) {z w : R} (hz : D z = z) (hw : z * w = 1) :
    D w = -w := by
  have h1 : D (z * w) = 0 := by rw [hw]; simp
  rw [D.leibniz, hz] at h1
  simp only [smul_eq_mul] at h1
  have h2 : w * (z * D w + w * z) = 0 := by rw [h1, mul_zero]
  have h3 : w * (z * D w + w * z) = (z * w) * D w + (z * w) * w := by ring
  rw [h3, hw] at h2
  linear_combination h2

theorem derivation_inv_pow_of_eq (D : Derivation k R R) {z w : R} (hz : D z = z)
    (hw : z * w = 1) (n : ℕ) : D (w ^ n) = -(n : R) * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, D.leibniz, ih, derivation_inv_of_eq D hz hw]
    simp only [smul_eq_mul]
    push_cast
    ring

theorem mem_eigenspace_of_mem_ker (D : Derivation k R R) {z : R} (hz : D z = z)
    (a : LinearMap.ker (D : R →ₗ[k] R)) (n : ℕ) :
    (a : R) * z ^ n ∈ Module.End.eigenspace (D : R →ₗ[k] R) (n : k) := by
  have ha : D (a : R) = 0 := a.2
  rw [Module.End.mem_eigenspace_iff]
  change D ((a : R) * z ^ n) = _
  rw [D.leibniz, derivation_pow_of_eq D hz, ha, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  simp only [smul_eq_mul, smul_zero, add_zero]
  ring

theorem powerSum_injective (p : ℕ) [CharP k p] (D : Derivation k R R) {z w : R}
    (hz : D z = z) (hw : z * w = 1) : Function.Injective (powerSum D z p) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hinj : Function.Injective (fun i : Fin p => ((i : ℕ) : k)) := fun i j hij =>
    Fin.ext (CharP.natCast_injOn_Iio k p i.2 j.2 hij)
  have hind := (Module.End.eigenspaces_iSupIndep (D : R →ₗ[k] R)).comp hinj
  have h0 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ
    (fun i => (a i : R) * z ^ (i : ℕ)) (fun i _ => mem_eigenspace_of_mem_ker D hz (a i) i) ha
  funext i
  have h1 := h0 i (Finset.mem_univ i)
  apply Subtype.ext
  have h2 : (a i : R) * z ^ (i : ℕ) * w ^ (i : ℕ) = a i := by
    rw [mul_assoc, ← mul_pow, hw, one_pow, mul_one]
  simpa [h1] using h2.symm

theorem powerSum_single (D : Derivation k R R) (z : R) (p : ℕ) (i : Fin p)
    (x : LinearMap.ker (D : R →ₗ[k] R)) :
    powerSum D z p (Pi.single i x) = (x : R) * z ^ (i : ℕ) := by
  classical
  rw [powerSum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem powerSum_surjective [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    [Module.Finite k R] (D : Derivation k R R) (hD : ∀ a : R, (⇑D)^[p] a = D a) {z w : R}
    (hz : D z = z) (hw : z * w = 1) : Function.Surjective (powerSum D z p) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← iSup_eigenspace_eq_top k p R (D : R →ₗ[k] R) hD, iSup_le_iff]
  intro μ v hv
  by_cases hv0 : v = 0
  · rw [hv0]; exact Submodule.zero_mem _
  have hev : Module.End.HasEigenvector (D : R →ₗ[k] R) μ v := ⟨hv, hv0⟩
  have hμ : μ ^ p = μ := by
    have h1 := hev.pow_apply p
    rw [Module.End.pow_apply] at h1
    have h2 : (⇑(D : R →ₗ[k] R))^[p] v = D v := hD v
    rw [h2] at h1
    have h3 : D v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    rw [h3] at h1
    exact (smul_left_injective k hv0 h1).symm
  obtain ⟨i, hi, rfl⟩ := exists_natCast_of_pow_eq k p μ hμ
  have h3 : D v = (i : R) * v := by
    rw [show D v = ((i : ℕ) : k) • v from Module.End.mem_eigenspace_iff.1 hv,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hx : v * w ^ i ∈ LinearMap.ker (D : R →ₗ[k] R) := by
    change D (v * w ^ i) = 0
    rw [D.leibniz, derivation_inv_pow_of_eq D hz hw, h3]
    simp only [smul_eq_mul]
    ring
  refine ⟨Pi.single ⟨i, hi⟩ ⟨v * w ^ i, hx⟩, ?_⟩
  rw [powerSum_single]
  change v * w ^ i * z ^ i = v
  rw [mul_assoc, ← mul_pow, mul_comm w z, hw, one_pow, mul_one]

theorem map_powerSum_eq_zero (D : Derivation k R R) (ε : R →ₐ[k] k) {z : R} (p : ℕ)
    (u : R →ₗ[k] k) (hu : ∀ a b : R, u (a * b) = u a * ε b + ε a * u b)
    (hk : ∀ a : R, D a = 0 → u a = 0) (huz : u z = 0)
    (a : Fin p → LinearMap.ker (D : R →ₗ[k] R)) : u (powerSum D z p a) = 0 := by
  have hpow : ∀ n : ℕ, u (z ^ n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hk 1 (by simp)
    | succ n ih => rw [pow_succ, hu, ih, huz]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [powerSum_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hu, hpow, hk _ (a i).2]
  simp

theorem finrank_eq_and_derivation_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = D a) → ∀ z₀ : R, IsUnit z₀ → D z₀ = z₀ →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  intro k _ _ p _ _ R _ _ _ D ε hD z₀ hu hz
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hinj := powerSum_injective p D hz hw
  have hsurj := powerSum_surjective p D hD hz hw
  refine ⟨?_, z₀, ?_, ?_⟩
  · rw [← (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
    simp
  · rw [hz]
    exact (hu.map ε).ne_zero
  · intro u h1 h2 h3
    ext r
    obtain ⟨a, rfl⟩ := hsurj r
    simpa using map_powerSum_eq_zero D ε p u h1 h2 h3 a

end Main

end GlobalTheory.CompanionTheory.PowerDerivation
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique
section
namespace GlobalTheory.CompanionTheory.Ggeo.TwoMaps

open Polynomial

theorem ringHom_eq_of_comp_eq (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B]
    [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B)
    (h : π.comp s = π.comp t) : s = t := by
  refine RingHom.ext fun a => ?_
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  obtain ⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  have hpd : p.derivative.eval a ≠ 0 := by
    rw [hp, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hst : p.map s = p.map t := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hx : (p.map s).eval (s a) = 0 := by
    rw [eval_map, eval₂_at_apply, hpa, map_zero]
  have hy : (p.map s).eval (t a) = 0 := by
    rw [hst, eval_map, eval₂_at_apply, hpa, map_zero]
  have hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
  have hunit : IsUnit ((p.map s).derivative.eval (s a)) := by
    rw [hdx]
    exact (IsUnit.mk0 _ hpd).map s
  obtain ⟨k, hk⟩ := binomExpansion (p.map s) (s a) (t a - s a)
  have hd : ¬ IsUnit (t a - s a) := by
    intro hu
    have h0 : π (t a - s a) = 0 := by
      have := RingHom.congr_fun h a
      simp only [RingHom.comp_apply] at this
      rw [map_sub, this, sub_self]
    exact (hu.map π).ne_zero h0
  have hkd : ¬ IsUnit (-(k * (t a - s a))) := by
    rw [IsUnit.neg_iff]
    exact fun hu => hd (isUnit_of_mul_isUnit_right hu)
  have hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a)) := by
    by_contra hc
    have hsum := IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a))
      (b := -(k * (t a - s a))) hc hkd
    apply hsum
    simpa using hunit
  have hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0 := by
    have e : s a + (t a - s a) = t a := by ring
    rw [e, hy, hx] at hk
    linear_combination -hk
  have hz : t a - s a = 0 := by
    simpa using (hu2.mul_left_eq_zero).1 hmul
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.CompanionTheory.Ggeo.TwoMaps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
section
namespace GlobalTheory.CompanionTheory.LocalSubringUnits

theorem mem_prime_iff_not_inv_mem :
    ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T),
      t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  intro K _ T P hP t
  have key : IsUnit (algebraMap T (LocalSubring.ofPrime T P).toSubring t) ↔ t ∉ P :=
    IsLocalization.AtPrime.isUnit_to_map_iff (LocalSubring.ofPrime T P).toSubring P t
  have hcoe : ((algebraMap T (LocalSubring.ofPrime T P).toSubring t :
      (LocalSubring.ofPrime T P).toSubring) : K) = (t : K) := rfl
  constructor
  · rintro ht ⟨h0, hinv⟩
    refine key.1 (IsUnit.of_mul_eq_one ⟨(t : K)⁻¹, hinv⟩ ?_) ht
    apply Subtype.ext
    rw [Subring.coe_mul, hcoe]
    exact mul_inv_cancel₀ h0
  · intro h
    by_contra ht
    obtain ⟨u, hu⟩ := (key.2 ht).exists_right_inv
    have hu' : (t : K) * (u : K) = 1 := by
      have := congrArg (fun x : (LocalSubring.ofPrime T P).toSubring => (x : K)) hu
      simpa only [Subring.coe_mul, hcoe, Subring.coe_one] using this
    have h0 : (t : K) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine h ⟨h0, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu']
    exact u.2

end GlobalTheory.CompanionTheory.LocalSubringUnits
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

def SncChart {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (e : ℕ) (h : Ω) : Prop :=
  ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ A) ∧ (∀ l, a l ∈ A) ∧ ∑ l, a l * f l = 1 ∧
    ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (A : Set Ω)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ s : S, (s : Ω) = h → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

