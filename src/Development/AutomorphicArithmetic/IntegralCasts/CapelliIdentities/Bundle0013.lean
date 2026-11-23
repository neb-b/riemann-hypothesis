module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalConjugateMem
section
private lemma liftUnitri {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (I : Ideal R) {n : ℕ}
    (h : GL (Fin n) K) (a : Fin n → Fin n → R)
    (ha : ∀ i j, f (a i j) = (h : Matrix (Fin n) (Fin n) K) i j)
    (hlow : ∀ i j, j < i → a i j = 0) (hd : ∀ i, a i i = 1)
    (hI : ∀ i j, i < j → a i j ∈ I) :
    h ∈ Subgroup.map (Matrix.GeneralLinearGroup.map f)
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker := by
  have hdet : (Matrix.of a).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := Matrix.of a) (fun i j hij => hlow i j hij)]
    simp [hd]
  let H : GL (Fin n) R := Matrix.GeneralLinearGroup.mk'' (Matrix.of a) (by rw [hdet]; exact isUnit_one)
  refine ⟨H, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have : Ideal.Quotient.mk I (a i j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hI i j hij)
      simpa [H, Matrix.one_apply, hij.ne] using this
    · simp [H, hd]
    · simp [H, hlow i j hij, Matrix.one_apply, hij.ne']
  · ext i j
    simp [H, ha]

theorem UpperTheory.diagonal_conjugate_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) < 1 →
        ∀ (c : ℕ) (z g : GL (Fin n) k),
        (z : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i : Fin n => ((ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) : kˣ) : k)) →
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (↥(ValuativeRel.valuation k).integer) k)).range →
        (g : Matrix (Fin n) (Fin n) k).BlockTriangular id → (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) →
        z ^ c * g * (z ^ c)⁻¹ ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker := by
  intro k _ _ _ _ n ϖ hϖ c z g hz hg hb hd
  obtain ⟨g0, hg0⟩ := hg
  have hg0' : ∀ i j, algebraMap (↥(ValuativeRel.valuation k).integer) k ((g0 : Matrix (Fin n) (Fin n) _) i j)
      = (g : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [← hg0]
    simp
  let p : ↥(ValuativeRel.valuation k).integer := ⟨(ϖ : k), hϖ.le⟩
  have hp : p ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have h1 : ValuativeRel.valuation k ((p * q : ↥(ValuativeRel.valuation k).integer) : k) = 1 := by
      rw [hq]; simp
    have h2 : ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) ≤ 1 := q.2
    rw [Subring.coe_mul, map_mul] at h1
    have h3 : ValuativeRel.valuation k (ϖ : k) * ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hϖ
    exact absurd h1 h3.ne
  let t : Fin n → kˣ := fun i => ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ))
  have hz1 : ((z ^ c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (((t i) ^ c : kˣ) : k)) := by
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
    congr 1
  have hz2 : (((z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => ((((t i) ^ c)⁻¹ : kˣ) : k)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hz1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    rw [← Units.val_mul]
    simp
  have hent : ∀ i j, ((z ^ c * g * (z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (((t i) ^ c : kˣ) : k) * (g : Matrix (Fin n) (Fin n) k) i j * ((((t j) ^ c)⁻¹ : kˣ) : k) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hz2, hz1, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hpow : ∀ i j : Fin n, i < j →
      (((t i) ^ c : kˣ) : k) * ((((t j) ^ c)⁻¹ : kˣ) : k) = (ϖ : k) ^ (((j : ℕ) - (i : ℕ)) * c) := by
    intro i j hij
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val]
    congr 1
    have hle : (i : ℕ) ≤ (j : ℕ) := hij.le
    simp only [t]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub hle]
    ring
  refine liftUnitri _ _ _
    (fun i j => if i < j then p ^ (((j : ℕ) - (i : ℕ)) * c) * (g0 : Matrix (Fin n) (Fin n) _) i j
      else if i = j then 1 else 0) ?_ ?_ ?_ ?_
  · intro i j
    rw [hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij, map_mul, hg0', map_pow, mul_right_comm, hpow i j hij]
      rfl
    · rw [if_neg (lt_irrefl _), if_pos rfl, hd, map_one, mul_one, ← Units.val_mul]
      simp
    · rw [if_neg hij.not_gt, if_neg hij.ne', hb hij]
      simp
  · intro i j hij
    rw [if_neg hij.not_gt, if_neg hij.ne']
  · intro i
    simp
  · intro i j hij
    rw [if_pos hij]
    apply Ideal.mul_mem_right
    have hpos : (j : ℕ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    rw [pow_mul]
    exact Ideal.pow_mem_pow (Ideal.pow_mem_of_mem _ hp _ (Nat.pos_of_ne_zero hpos)) c
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalEntries
section
theorem UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE :
    ∀ {κ : Type} [inst : Field κ]
    (M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) (α : Fin (2 : ℕ) → κ),
    Function.Injective α →
      M.charpoly = ∏ i : Fin (2 : ℕ), (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (α i)) →
        ∃ (P : GL (Fin (2 : ℕ)) κ),
          M * (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) =
            (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) * Matrix.diagonal α := by
  intro κ _ M α hα h
  classical
  have hv : ∀ i : Fin 2, ∃ v : Fin 2 → κ, v ≠ 0 ∧ M.mulVec v = α i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin 2) (α i) - M).det = 0 := by
      rw [← Matrix.eval_charpoly, h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) α hα v fun i =>
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv i), hv0 i⟩
  have hu : IsUnit (Matrix.of v).transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.1 hli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext j i
  have := congrFun (hv i) j
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalMultiplication
section
theorem UpperTheory.Reformulated.B.UpperTriangularThreeDiagonalOfMul.diag_mul :
    ∀ {R : Type} [inst : CommRing R]
    (X Y : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
    (∀ (i j : Fin (3 : ℕ)), j < i → X i j = (0 : R)) →
      (∀ (i j : Fin (3 : ℕ)), j < i → Y i j = (0 : R)) → ∀ (a : Fin (3 : ℕ)), (X * Y) a a = X a a * Y a a := by
  intro R _ X Y hX hY a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalizationExistence
section
theorem UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag :
    ∀ {κ : Type} [inst : Field κ] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) κ) (a : Fin n → κ),
    Function.Injective a →
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (a i)) →
        ∃ (P : GL (Fin n) κ),
          M * (↑P : Matrix (Fin n) (Fin n) κ) = (↑P : Matrix (Fin n) (Fin n) κ) * Matrix.diagonal a := by
  intro κ _ n M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  have hU : IsUnit (Matrix.of fun r c => v c r : Matrix (Fin n) (Fin n) κ) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext r c
  have h := congrFun (hv c).apply_eq_smul r
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalizeThreeByThree
section
theorem UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (M : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K),
        M.charpoly = ∏ a : Fin (3 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (d a)) →
          ∃ (h : GL (Fin (3 : ℕ)) K),
            (↑h⁻¹ : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) * M * (↑h : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) =
              Matrix.diagonal d := by
  intro K _ d hd M hM
  have hev : ∀ a, Module.End.HasEigenvalue (Matrix.toLin' M) (d a) := by
    intro a
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using fun a => (hev a).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  let P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => v j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hMP : M * P = P * Matrix.diagonal d := by
    ext i j
    have h := congrFun (hv j).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  obtain ⟨u, hu⟩ := hP
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hMP, ← hu, ← Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Diagz
section
theorem UpperTheory.Reformulated.B.Qh2.diagz :
    ∀ {K : Type} [inst : Field K]
    (M : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (a : Fin (4 : ℕ) → K),
    Function.Injective a →
      M.charpoly = ∏ i : Fin (4 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (a i)) →
        ∃ (P : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (Q : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K),
          P * Q = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧
            Q * P = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧ Q * M * P = Matrix.diagonal a := by
  intro K _ M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  let P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun r c => v c r
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hMP : M * P = P * Matrix.diagonal a := by
    ext r c
    have h := congrFun (hv c).apply_eq_smul r
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  refine ⟨P, P⁻¹, Matrix.mul_nonsing_inv P hdet, Matrix.nonsing_inv_mul P hdet, ?_⟩
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DigitExpansionLattice
section
open IsLocalRing

theorem UpperTheory.digit_expansion_lattice :
    ∀ {O Ω : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NormedField Ω] [IsUltrametricDist Ω] [Algebra O Ω]
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (ϖ : O) (hϖ : Irreducible ϖ) (hlt : ‖algebraMap O Ω ϖ‖ < 1)
        (S : Submodule O Ω) (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (E : Finset Ω) (hE : ∀ e ∈ E, e ∈ S)
        (hdig : ∀ s ∈ S, ∃ e ∈ E, ∃ s' ∈ S, s = e + ϖ • s'),
        Module.Finite O S := by
  intro O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig
  classical
  have hI : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hhaus : IsHausdorff (maximalIdeal O) S := by
    refine ⟨fun x hx => ?_⟩
    have hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n := by
      intro n
      have h := hx n
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      obtain ⟨t, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      have : (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω) := by
        simp [Algebra.smul_def]
      rw [this, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hS _ t.2)
    have hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
    have h0 : ‖(x : Ω)‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hpre : IsPrecomplete (maximalIdeal O) (E → O) := by
    refine ⟨fun g hg => ?_⟩
    have hcoord : ∀ {m : ℕ} (x : E → O),
        x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m := by
      intro m x hx i
      have h := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx
      rw [Submodule.map_smul''] at h
      have h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O) :=
        Submodule.smul_mono le_rfl le_top h
      simpa using h2
    have hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_
      intro m n hmn
      have h := (SModEq.sub_mem.1 (hg hmn))
      refine SModEq.sub_mem.2 ?_
      have h2 := hcoord _ h i
      simpa using h2
    choose L hL using hc
    refine ⟨L, fun n => ?_⟩
    refine SModEq.sub_mem.2 ?_
    have hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h := SModEq.sub_mem.1 (hL i n)
    simpa using h
  let v : E → S := fun e => ⟨e, hE e e.2⟩
  let f : (E → O) →ₗ[O] S := Fintype.linearCombination O v
  have hsurj : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_
    intro y
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, he, s', hs', hs⟩ := hdig s s.2
    refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    have hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩ := by
      simp [f, v, Fintype.linearCombination_apply_single]
    simp only [LinearMap.comp_apply, hf]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
      Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩
    apply Subtype.ext
    simp [hs]
  exact Module.Finite.of_surjective f hsurj
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem
section
private theorem int_of_rat {K : Type} [Field K] [CharZero K] (r : ℚ)
    (h : IsIntegral ℤ (r : K)) : ∃ a : ℤ, (a : ℚ) = r := by
  have h1 : IsIntegral ℤ r := by
    have h2 : IsIntegral ℤ (algebraMap ℚ K r) := by simpa using h
    exact (isIntegral_algebraMap_iff ).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨a, by simpa using ha⟩

theorem UpperTheory.discriminant_mul_integral_mem :
    ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* K) (w y : K) (t n : ℤ), w + σ w = (t : K) → w * σ w = (n : K) → IsIntegral ℤ y → y ∈ IntermediateField.adjoin ℚ {w} → ∃ a b : ℤ, ((t ^ 2 - 4 * n : ℤ) : K) * y = (a : K) + (b : K) * w := by
  intro K _ _ σ w y t n ht hn hy hmem
  have hsq : w * w = (t : K) * w - (n : K) := by linear_combination w * ht - hn
  have hw : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X,
        eq_intCast, eq_intCast]
      linear_combination hsq
  have hwQ : IsIntegral ℚ w := hw.tower_top
  have hmem' : y ∈ Algebra.adjoin ℚ {w} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hwQ.isAlgebraic]
    exact hmem
  have hrep : ∀ z ∈ Algebra.adjoin ℚ {w}, ∃ p q : ℚ, z = (p : K) + (q : K) * w := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p + r, q + s, by push_cast; ring⟩
    | mul x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p * r - q * s * n, p * s + q * r + q * s * t, by
        push_cast; linear_combination (q : K) * (s : K) * hsq⟩
  obtain ⟨p, q, hpq⟩ := hrep y hmem'
  have hσ : ∀ z : K, IsIntegral ℤ z → IsIntegral ℤ (z + σ z) := fun z hz =>
    hz.add (hz.map σ.toIntAlgHom)
  have hσw : σ w = (t : K) - w := by linear_combination ht
  have hσy : σ y = (p : K) + (q : K) * ((t : K) - w) := by
    rw [hpq, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσw]
  have hA : y + σ y = ((2 * p + q * t : ℚ) : K) := by
    rw [hσy, hpq]; push_cast; ring
  have hB : w * y + σ (w * y) = ((p * t + q * (t ^ 2 - 2 * n) : ℚ) : K) := by
    rw [map_mul, hσy, hσw, hpq]; push_cast; linear_combination 2 * (q : K) * hsq
  obtain ⟨A, hA'⟩ := int_of_rat _ (hA ▸ hσ y hy)
  obtain ⟨B, hB'⟩ := int_of_rat _ (hB ▸ hσ _ (hw.mul hy))
  have hAK : (A : K) = 2 * p + q * t := by exact_mod_cast congrArg (Rat.cast : ℚ → K) hA'
  have hBK : (B : K) = p * t + q * (t ^ 2 - 2 * n) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → K) hB'
  refine ⟨(t ^ 2 - 2 * n) * A - t * B, 2 * B - t * A, ?_⟩
  push_cast
  rw [hAK, hBK, hpq]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualLatticeDenominator
section
theorem UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsFullLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by
  intro A _ _ F V _ _ _ _ _ _ _ Y hY z
  have hz : z ∈ Submodule.span F (Y : Set V) := by
    rw [hY.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨d, hd⟩, n, hn⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors A) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩
    have h : (a * d) • c • x = n • a • x := by
      rw [mul_smul, ← smul_assoc d c x]
      have h2 : d • c = algebraMap A F n := hn.symm
      rw [h2, algebraMap_smul, smul_comm]
    rw [h]
    exact Y.smul_mem n hax
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualMemSpanEvalOfFiniteDimensional
section
theorem UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by
  intro Y E _ φ
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro x hx
  have h0 : x = 0 := by
    apply Subtype.ext
    funext y
    exact (Submodule.mem_iInf _).1 hx y
  rw [h0]
  exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrime
section
theorem UpperTheory.Reformulated.B.Qk11.dz_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_right _, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_left _, hm⟩
end

