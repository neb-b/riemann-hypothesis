module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdMulMem
section
namespace UpperTheory.Reformulated.B.S3

private theorem prod_mul_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (s : Finset (Fin n)) :
    (fun j => (∏ l ∈ s, (d j - d l)) * v j) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | insert a s ha ih =>
    have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
    convert h using 1
    ext j
    simp [Matrix.mulVec_diagonal, Finset.prod_insert ha, smul_eq_mul]
    ring

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W := by
  have h := prod_mul_mem W d hW v hv (Finset.univ.erase i)
  have hc : (∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun l hl => ?_) hi
    exact sub_ne_zero.mpr fun e => (Finset.ne_of_mem_erase hl) (hd e).symm
  have h2 := W.smul_mem ((∏ l ∈ Finset.univ.erase i, (d i - d l)) * v i)⁻¹ h
  convert h2 using 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hc]
  · have hz : (∏ l ∈ Finset.univ.erase i, (d j - d l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (sub_self _)
    rw [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_eq_mul, hz, zero_mul, mul_zero]

end UpperTheory.Reformulated.B.S3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdPrimesDvd
section
theorem UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq :
    ∀ {M ι : Type} [inst : CommRing M] (f : ι → M) (y : M)
    (s : Finset ι),
    (∀ a ∈ s, Prime (f a)) → (∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) → (∀ a ∈ s, f a ∣ y) → ∏ a ∈ s, f a ∣ y := by
  intro M ι inst f y s
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro hp hd hy
    have hpa : Prime (f a) := hp a (Finset.mem_insert_self a s)
    obtain ⟨c, hc⟩ := ih (fun b hb => hp b (Finset.mem_insert_of_mem hb))
      (fun b hb d hd' => hd b (Finset.mem_insert_of_mem hb) d (Finset.mem_insert_of_mem hd'))
      (fun b hb => hy b (Finset.mem_insert_of_mem hb))
    have h1 : f a ∣ (∏ b ∈ s, f b) * c := hc ▸ hy a (Finset.mem_insert_self a s)
    rcases hpa.dvd_or_dvd h1 with h2 | h2
    · obtain ⟨b, hb, hab⟩ := hpa.exists_mem_finset_dvd h2
      have h3 : a = b := hd a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) hab
      exact absurd (h3 ▸ hb) ha
    · rw [Finset.prod_insert ha, hc, mul_comm (f a)]
      exact mul_dvd_mul_left _ h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductFirstParts
section
noncomputable def UpperTheory.Reformulated.B.product_first_partition.blockEmb.{u_1, u_2} :
    (K : Type u_1) →
      [inst : CommRing K] →
        {S : Type u_2} → {k n : ℕ} → S → MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × Fin k × Fin n) K :=
    fun (K : Type u_1) [CommRing K] {S : Type u_2} {k n : ℕ} (s : S) ↦ MvPolynomial.rename fun (v : Fin k × Fin n) ↦ (s, v)

noncomputable def UpperTheory.Reformulated.B.product_first_partition.tensorLat.{u_1, u_2, u_3} :
    (R : Type u_1) →
      (K : Type u_2) →
        [inst : CommRing R] →
          [inst_1 : CommRing K] →
            [inst_2 : Algebra R K] →
              {S : Type u_3} →
                [Fintype S] →
                  {k n : ℕ} →
                    (S → Submodule R (MvPolynomial (Fin k × Fin n) K)) → Submodule R (MvPolynomial (S × Fin k × Fin n) K) :=
    fun (R : Type u_1) (K : Type u_2) [CommRing R] [CommRing K] [Algebra R K] {S : Type u_3} [Fintype S] {k n : ℕ}
        (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) ↦
      Submodule.span R
        {P : MvPolynomial (S × Fin k × Fin n) K |
          ∃ (F : S → MvPolynomial (Fin k × Fin n) K),
            (∀ (s : S), F s ∈ M s) ∧
              P =
                ∏ s : S,
                  (UpperTheory.Reformulated.B.product_first_partition.blockEmb K s : MvPolynomial (Fin k × Fin n) K → MvPolynomial (S × Fin k × Fin n) K)
                    (F s)}

private theorem UpperTheory.Reformulated.B.product_first_partition.span_mul_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (M N : Submodule R A) :
    Submodule.span R {X : A | ∃ F ∈ M, ∃ G ∈ N, X = F * G} = M * N := by
  rw [Submodule.mul_def]
  congr 1
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]

private theorem UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (N : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    UpperTheory.Reformulated.B.product_first_partition.tensorLat R K N =
      ∏ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap := by
  have h : ∀ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap =
      Submodule.span R (((N s).map
        ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap : Submodule R _) : Set _) :=
    fun s => (Submodule.span_eq _).symm
  rw [Finset.prod_congr rfl fun s _ => h s, Submodule.prod_span]
  unfold UpperTheory.Reformulated.B.product_first_partition.tensorLat
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => UpperTheory.Reformulated.B.product_first_partition.blockEmb K s (F s), fun s => ⟨F s, hF s, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFg using hg
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFg s).symm⟩

theorem UpperTheory.Reformulated.B.product_first_partition.tensor_onto :
    ∀ {R K : Type} [inst : CommRing R] [inst_1 : Field K] [inst_2 : Algebra R K] {S : Type} [inst_3 : Fintype S]
      [DecidableEq S] {k n : ℕ} (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)),
      (∀ (s : S), M s ≤ Submodule.span R {X : MvPolynomial (Fin k × Fin n) K | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) →
        UpperTheory.Reformulated.B.product_first_partition.tensorLat R K M ≤
          Submodule.span R
            {X : MvPolynomial (S × Fin k × Fin n) K |
              ∃ P ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K A, ∃ Q ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K B, X = P * Q} := by
  intro R K _ _ _ S _ _ k n A B M h
  rw [UpperTheory.Reformulated.B.product_first_partition.span_mul_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq,
    UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← Submodule.map_mul]
  refine Submodule.map_mono ?_
  rw [← UpperTheory.Reformulated.B.product_first_partition.span_mul_eq]
  exact h s
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductMap
section
noncomputable def UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM :
    {R A : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing A] →
          [Algebra R A] →
            (e : R) → e * e = e → (ι : Type) → [inst : Fintype ι] → [inst_3 : DecidableEq ι] → Matrix ι ι A →* Matrix ι ι A :=
  fun {R A} _ _ _ e he ι _ _ =>
    { toFun := fun M => e • M + (1 - e) • (1 : Matrix ι ι A)
      map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
      map_mul' := fun M N => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
        have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
          smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjTrans
section
private def UpperTheory.Reformulated.B.Qi50.proj {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) : P j → P i :=
  Nat.leRec (motive := fun j _ => P j → P i) id (fun k _ f => f ∘ t k) h

private theorem UpperTheory.Reformulated.B.Qi50.proj_self {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i : ℕ} (h : i ≤ i) (a : P i) : UpperTheory.Reformulated.B.Qi50.proj t h a = a := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_self]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_succ {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (a : P (j + 1)) :
    UpperTheory.Reformulated.B.Qi50.proj t h' a = UpperTheory.Reformulated.B.Qi50.proj t h (t j a) := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_succ _ _ h]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_trans {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : P k) :
    UpperTheory.Reformulated.B.Qi50.proj t hij (UpperTheory.Reformulated.B.Qi50.proj t hjk a)
      = UpperTheory.Reformulated.B.Qi50.proj t (hij.trans hjk) a := by
  induction k, hjk using Nat.le_induction with
  | base => rw [UpperTheory.Reformulated.B.Qi50.proj_self]
  | succ k hk ih =>
    rw [UpperTheory.Reformulated.B.Qi50.proj_succ t hk, UpperTheory.Reformulated.B.Qi50.proj_succ t (hij.trans hk), ih]

theorem UpperTheory.Reformulated.B.Qi50.seq_sec :
    ∀ (P : ℕ → Type 1),
    (∀ (j : ℕ), Finite (P j)) →
      (∀ (j : ℕ), Nonempty (P j)) →
        ∀ (t : (j : ℕ) → P (j + (1 : ℕ)) → P j), ∃ (s : (j : ℕ) → P j), ∀ (j : ℕ), t j (s (j + (1 : ℕ))) = s j := by
  intro P hfin hne t
  obtain ⟨s, hs⟩ := exists_seq_forall_proj_of_forall_finite (α := P)
    (fun h => UpperTheory.Reformulated.B.Qi50.proj t h)
    (fun _ a => UpperTheory.Reformulated.B.Qi50.proj_self t _ a)
    (fun _ _ _ hij hjk a => UpperTheory.Reformulated.B.Qi50.proj_trans t hij hjk a)
    (fun _ _ => Set.toFinite _)
  refine ⟨s, fun j => ?_⟩
  have h := hs (Nat.le_succ j)
  rwa [UpperTheory.Reformulated.B.Qi50.proj_succ t le_rfl, UpperTheory.Reformulated.B.Qi50.proj_self] at h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectionCompact
section
noncomputable def UpperTheory.Reformulated.B.ProjectionCompact.piK :
    {T κ : Type} →
      [inst : Fintype T] →
        [inst_1 : DecidableEq T] →
          [inst_2 : Fintype κ] → [inst_3 : DecidableEq κ] → (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ :=
  fun {T κ} _ _ _ _ =>
    { toFun := fun M => Matrix.of fun f g => ∏ t, M t (f t) (g t)
      map_one' := by
        ext f g
        simp only [Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
        by_cases h : f = g
        · subst h
          simp
        · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
          rw [if_neg h]
          exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
      map_mul' := fun M N => by
        ext f g
        simp only [Matrix.of_apply, Pi.mul_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun h _ => Finset.prod_mul_distrib }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
section
noncomputable def UpperTheory.Reformulated.B.ProjectiveLineOf.P1 :
    Prop :=
    ∀ (k : Type) [inst : NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
      (↑γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        ∀ (D : Set (GL (Fin n) k)),
          IsCompact D →
            ∃ (C : Set (GL (Fin n) k)),
              IsCompact C ∧ ∀ (x : GL (Fin n) k), x⁻¹ * γ * x ∈ D → ∃ (t : GL (Fin n) k), t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

section

open Polynomial Matrix

private theorem charpoly_dvd_of_aeval {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : A.charpoly.Separable) (p : k[X]) (hp : aeval A p = 0) : A.charpoly ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  let K := AlgebraicClosure k
  let f := algebraMap k K
  rw [← Polynomial.map_dvd_map' f]
  have hsep : (A.charpoly.map f).Separable := hA.map
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep)]
  intro r hr
  have hr' : (A.map f).charpoly.IsRoot r := by
    rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots hr
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
  have h1 := spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩
  have h2 : aeval (A.map f) (p.map f) = 0 := by
    have h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0 := by
      rw [aeval_algHom_apply, hp, map_zero]
    rw [aeval_map_algebraMap]
    exact h3
  rw [mem_roots (Polynomial.map_ne_zero hp0)]
  by_contra hne
  rw [h2, spectrum.mem_iff, sub_zero] at h1
  exact h1 ((IsUnit.mk0 _ hne).map _)

private def krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

private theorem krylov_mulVec {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (p : k[X]) (hp : p.degree < n) :
    krylov A v *ᵥ (fun j => p.coeff j) = aeval A p *ᵥ v := by
  have h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]
    simp [Algebra.smul_def]
  rw [h, Matrix.sum_mulVec]
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

private theorem exists_krylov_det_ne_zero {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : A.charpoly.Separable) :
    ∃ v, (krylov A v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator k[X]
    (Module.AEval' (Matrix.toLin' A))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of _).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : k[X] := (degreeLTEquiv k n).symm c
  have hpdeg : p.degree < n := mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2
  have hpc : (fun j : Fin n => p.coeff j) = c := (degreeLTEquiv k n).apply_symm_apply c
  have hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p
  have h1 : aeval A p *ᵥ v = 0 := by rw [← krylov_mulVec A v p hpdeg, hpc, hc]
  have h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]
  rw [Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective] at h2
  have h3 := charpoly_dvd_of_aeval A hA p h2
  have h4 : p = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h3 ?_
    simpa [Matrix.charpoly_degree_eq_dim] using hpdeg
  apply hc0
  rw [← hpc, h4]
  rfl

private theorem mul_krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    A * krylov A v = krylov A v *
      Matrix.of fun i j : Fin n => (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).coeff i := by
  ext i j
  have hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n := by
    simpa [Matrix.charpoly_degree_eq_dim] using
      degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic
  have h := congrFun (krylov_mulVec A v _ hdeg) i
  rw [← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec] at h
  exact h.symm

private theorem continuous_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun δ : GL (Fin n) k => krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)

private theorem exists_compact_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ}
    (v : Fin n → k) (S : Set (GL (Fin n) k)) (hS : IsCompact S)
    (h : ∀ δ ∈ S, (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0) :
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧
      ∀ δ ∈ S, ∃ u ∈ C, (u : Matrix (Fin n) (Fin n) k) = krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Φ : S → GL (Fin n) k := fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)
  have hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) =
      krylov (δ.1 : Matrix (Fin n) (Fin n) k) v := fun δ => rfl
  have hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v :=
    (continuous_krylov v).comp continuous_subtype_val
  have hΦ : Continuous Φ := by
    rw [Units.continuous_iff]
    refine ⟨hc, ?_⟩
    simp_rw [Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate
  exact ⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩

private theorem isClosed_charpoly_eq {k : Type} [NontriviallyNormedField k] [CharZero k] {n : ℕ}
    (χ : k[X]) :
    IsClosed {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} := by
  have h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} =
      ⋂ r : k, {δ : GL (Fin n) k |
        (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]
    exact ⟨fun h r => by rw [h], Polynomial.funext⟩
  rw [h]
  exact isClosed_iInter fun r =>
    isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const

end

theorem UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds :
    UpperTheory.Reformulated.B.ProjectiveLineOf.P1 := by
  intro k _ _ _ n γ hγ D hD
  classical
  set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ
  have hD' := hD.inter_right (isClosed_charpoly_eq (n := n) χ)
  let U : (Fin n → k) → Set (GL (Fin n) k) := fun v =>
    {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}
  have hU : ∀ v, IsOpen (U v) := fun v =>
    isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const
  obtain ⟨s, hs⟩ := hD'.elim_finite_subcover U hU (by
    rintro δ ⟨-, hδ⟩
    exact Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))
  obtain ⟨S, hSc, hSU, hS⟩ := hD'.finite_compact_cover s U (fun v _ => hU v) hs
  choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)
  obtain ⟨v₀, hv₀⟩ := exists_krylov_det_ne_zero _ hγ
  let u₀ : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀
  have hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀ := rfl
  refine ⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v,
    s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩
  have hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ := by
    rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  have hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v := hS ▸ ⟨hx, hch⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨u, huC, hu⟩ := hC v _ hxv
  have h1 := mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v
  have h2 := mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀
  rw [← hu, hch] at h1
  rw [← hu₀, ← hχ] at h2
  have h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀ := by
    apply Units.ext
    rw [mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul,
      Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]
  refine ⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩
  calc x * u * u₀⁻¹ * γ = x * u * (u₀⁻¹ * γ * u₀) * u₀⁻¹ := by group
    _ = γ * (x * u * u₀⁻¹) := by rw [← h3]; group
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PseudoDivision
section
universe u

theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuotientBasisFiniteDimensional
section
theorem UpperTheory.Reformulated.B.QuotientBasisFiniteDimensional.qb_fd :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {ι : Type} [Finite ι]
    (f : ι → PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] ↥K ∧ ∀ (i : ι), f i ∈ K := by
  intro l _ ι _ f
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range f), ?_, fun i =>
    IntermediateField.subset_adjoin ℚ_[l] (Set.range f) ⟨i, rfl⟩⟩
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RayPrimeSpan
section
theorem UpperTheory.Reformulated.B.Qi16.rayPrime_span :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ),
    Nat.Prime p →
      (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {(↑p : NumberField.RingOfIntegers ℚ)} := by
  intro v p hp hmem
  have hprime : Prime (p : NumberField.RingOfIntegers ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv]
    rw [map_natCast]
    exact Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hne : Ideal.span {(p : NumberField.RingOfIntegers ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hprime.ne_zero
  have hmax : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsMaximal :=
    hP.isMaximal hne
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
end

