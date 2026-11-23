module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis
section
theorem UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ),
      (0 : ℝ) ≤ r →
        r < (1 : ℝ) →
          ∀ (A : Matrix (Fin n) (Fin n) L),
            (∀ (i j : Fin n), ‖(A - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) →
              ∃ (U : Matrix (Fin n) (Fin n) L) (W : Matrix (Fin n) (Fin n) L),
                (∀ (i j : Fin n), j < i → U i j = (0 : L)) ∧
                  (∀ (i j : Fin n), i < j → W i j = (0 : L)) ∧
                    (∀ (i j : Fin n), ‖(U - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧
                      (∀ (i j : Fin n), ‖(W - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧ A = U * W := by
  intro L _ _ n r h0 h1
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro A hA
    have hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
    have hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r := by
      simpa using hA (Fin.last n) (Fin.last n)
    have hd : ‖A (Fin.last n) (Fin.last n)‖ = 1 := by
      have hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖ := by
        rw [norm_one]; exact (hd1.trans_lt h1).ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, norm_one] at this
      rw [this]
      exact max_eq_right (hd1.trans h1.le)
    have hd0 : A (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    have hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hcl i)] using hA i.castSucc (Fin.last n)
    have hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hlc i)] using hA (Fin.last n) i.castSucc
    have hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r :=
      fun i => by rw [norm_div, hd, div_one]; exact hb i
    have hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc
        = (1 : Matrix (Fin n) (Fin n) L) i j := fun i j => by
      simp [Matrix.one_apply]
    obtain ⟨U, W, hU, hW, hU1, hW1, hUW⟩ := ih
      (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc)
      (fun i j => by
        have h2 := hA i.castSucc j.castSucc
        rw [Matrix.sub_apply, hone] at h2
        rw [Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
        rw [norm_neg, norm_mul]
        calc _ ≤ r * 1 := mul_le_mul (hu i) ((hc j).trans h1.le) (norm_nonneg _) h0
          _ = r := mul_one r)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => L)
          (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (A (Fin.last n) j)
        (fun i' => Fin.lastCases (motive := fun _ => L) 0 (fun j' => W i' j') j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (Fin.le_last _).not_gt
      · simpa using hU _ _ (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Fin.le_last _).not_gt
      · simp
      · simpa using hW _ _ (by simpa using hij)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using h0
      · simpa [Matrix.one_apply_ne (hlc _)] using h0
      · simpa [Matrix.one_apply_ne (hcl _), hd] using hb _
      · rw [Matrix.sub_apply, hone]
        simpa using hU1 _ _
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using hd1
      · simpa [Matrix.one_apply_ne (hlc _)] using hc _
      · simpa [Matrix.one_apply_ne (hcl _)] using h0
      · rw [Matrix.sub_apply, hone]
        simpa using hW1 _ _
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simp
      · simp
      · simp [hd0]
      · rename_i i j
        have := congrFun (congrFun hUW i) j
        rw [Matrix.of_apply, Matrix.mul_apply] at this
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [← this, sub_add_cancel]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiltrationExponentBound
section
theorem UpperTheory.filtration_exponent_bound :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module O D] [Module A D]
        [IsScalarTower O A D] (N : Submodule O D) (γ : D →ₗ[O] D) (ϖ : A) (l : O) (E e : ℕ → ℕ) (lam : ℕ → O),
        Monotone E → Monotone e → (∀ y, E y ≤ e y) →
        (∀ r : ℕ, ∃ u : Oˣ, lam (r + 1) = (u : O) * l ^ (E (r + 1) - E r)) →
        lam 0 = 0 → (∀ x ∈ N, ϖ • x ∈ N) →
        (∀ (r : ℕ), ∀ x ∈ N, ∃ x' ∈ N,
          γ (ϖ ^ r • x) - ϖ ^ r • x = lam r • (ϖ ^ r • x) + ϖ ^ (r + 1) • x') →
        ∀ w ∈ N, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ N) ∧ ∀ K : ℕ, ∃ t ∈ N,
          l ^ e K • (γ w - w) - ∑ y ∈ Finset.range K, l ^ (e K - e y) •
            (γ (ϖ ^ y • (l ^ (e y - E y) • c y)) - ϖ ^ y • (l ^ (e y - E y) • c y)) = ϖ ^ K • t := by
  intro O A D _ _ _ _ _ _ _ N γ ϖ l E e lam hE he hEe hlam hlam0 hϖ hγ w hw
  choose u hu using hlam
  have hγ' : ∀ (r : ℕ) (x : N), ∃ x' : N,
      γ (ϖ ^ r • (x : D)) - ϖ ^ r • (x : D) = lam r • (ϖ ^ r • (x : D)) + ϖ ^ (r + 1) • (x' : D) := by
    intro r x
    obtain ⟨x', h1, h2⟩ := hγ r x x.2
    exact ⟨⟨x', h1⟩, h2⟩
  choose f hf using hγ'
  have h0 : γ w - w = ϖ • (f 0 ⟨w, hw⟩ : D) := by
    have := hf 0 ⟨w, hw⟩
    simpa [hlam0] using this
  let s : ℕ → N := fun K => Nat.rec (l ^ E 0 • f 0 ⟨w, hw⟩)
    (fun k sk => - f (k + 1) (((u k)⁻¹ : Oˣ).val • sk)) K
  have hs0 : s 0 = l ^ E 0 • f 0 ⟨w, hw⟩ := rfl
  have hsS : ∀ k, s (k + 1) = - f (k + 1) (((u k)⁻¹ : Oˣ).val • s k) := fun _ => rfl
  let c : ℕ → N := fun K => Nat.casesOn K 0 (fun k => ((u k)⁻¹ : Oˣ).val • s k)
  have hc0 : c 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = ((u k)⁻¹ : Oˣ).val • s k := fun _ => rfl
  clear_value c s
  have key : ∀ K, l ^ E K • (γ w - w) - ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
      (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = ϖ ^ (K + 1) • (s K : D) := by
    intro K
    induction K with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, hc0, hs0, h0, ZeroMemClass.coe_zero, smul_zero,
        map_zero, sub_zero, pow_one, Submodule.coe_smul]
      rw [smul_comm]
    | succ K ih =>
      have hK : E K ≤ E (K + 1) := hE (Nat.le_succ K)
      have hsum : ∑ y ∈ Finset.range (K + 1), l ^ (E (K + 1) - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) =
          l ^ (E (K + 1) - E K) • ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' : E y ≤ E K := hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      have hp : l ^ E (K + 1) = l ^ (E (K + 1) - E K) * l ^ E K := by
        rw [← pow_add]
        congr 1
        omega
      have hl : lam (K + 1) • (ϖ ^ (K + 1) • (c (K + 1) : D)) =
          l ^ (E (K + 1) - E K) • (ϖ ^ (K + 1) • (s K : D)) := by
        rw [hcS, Submodule.coe_smul, smul_comm (ϖ ^ (K + 1)), smul_smul, hu]
        congr 1
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [Finset.sum_range_succ _ (K + 1), hsum, hp, mul_smul, ← sub_sub, ← smul_sub, ih, hf, hl,
        hsS, ← hcS]
      simp
  refine ⟨fun y => (c y : D), by simp [hc0], fun y => (c y).2, fun K => ?_⟩
  cases K with
  | zero =>
    refine ⟨l ^ e 0 • (ϖ • (f 0 ⟨w, hw⟩ : D)), N.smul_mem _ (hϖ _ (f 0 ⟨w, hw⟩).2), ?_⟩
    simp [h0]
  | succ K =>
    have hK : E K ≤ e (K + 1) := (hEe K).trans (he (Nat.le_succ K))
    refine ⟨l ^ (e (K + 1) - E K) • (s K : D), N.smul_mem _ (s K).2, ?_⟩
    have hp : l ^ e (K + 1) = l ^ (e (K + 1) - E K) * l ^ E K := by
      rw [← pow_add]
      congr 1
      omega
    rw [smul_comm (ϖ ^ (K + 1)), ← key, smul_sub (l ^ (e (K + 1) - E K)), ← mul_smul, ← hp,
      Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyK : y ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    have h1 : E y ≤ E K := hE hyK
    have h2 : e y ≤ e (K + 1) := he (hyK.trans (Nat.le_succ K))
    have h3 := hEe y
    rw [smul_comm (ϖ ^ y), map_smul, ← smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteAndNcardBound
section
open NumberField in
theorem UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le :
    ∀ (E : Type) [inst : Field E] [NumberField E],
    ∃ (C : ℝ) (N : ℕ),
      ∀ (R : ℝ),
        (1 : ℝ) ≤ R →
          {r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.Finite ∧
            (↑{r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.ncard :
                ℝ) ≤
              C * R ^ N := by
  intro E _ _
  classical
  let L := LinearMap.toContinuousLinearMap (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap
  let c : ℝ := ‖L‖
  have hc : 0 ≤ c := norm_nonneg _
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E))
  refine ⟨(2 * c + 3) ^ n, n, fun R hR => ?_⟩
  let M : ℕ := ⌈c * R⌉₊
  have hM : c * R ≤ M := Nat.le_ceil _
  have hM' : (M : ℝ) ≤ c * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  let f : RingOfIntegers E → (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    (RingOfIntegers.basis E).equivFun
  have hf : Function.Injective f := (RingOfIntegers.basis E).equivFun.injective
  let T : Finset (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  have hT : T.card = (2 * M + 1) ^ n := by
    have h1 : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]; omega
    simp only [T, n, Fintype.card_piFinset, h1, Finset.prod_const, Finset.card_univ]
  have hmaps : ∀ r ∈ {r : RingOfIntegers E | ∀ (w : InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R},
      f r ∈ (T : Set _) := by
    intro r hr
    have h1 : ‖canonicalEmbedding E (r : E)‖ ≤ R := by
      rw [canonicalEmbedding.norm_le_iff]
      intro φ
      have := hr (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h2 : ‖L (canonicalEmbedding E (r : E))‖ ≤ M :=
      (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left h1 hc).trans hM)
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h3 := (norm_le_pi_norm _ i).trans h2
    have h4 : L (canonicalEmbedding E (r : E)) i = ((f r i : ℤ) : ℂ) := by
      change (canonicalEmbedding.latticeBasis E).repr (canonicalEmbedding E (r : E)) i = _
      rw [canonicalEmbedding.integralBasis_repr_apply]
      have := integralBasis_repr_apply E r i
      rw [RingOfIntegers.coe_eq_algebraMap, this]
      simp [f]
    rw [h4, Complex.norm_intCast] at h3
    have h5 : |f r i| ≤ (M : ℤ) := by exact_mod_cast h3
    exact abs_le.mp h5
  refine ⟨Set.Finite.of_finite_image (T.finite_toSet.subset ?_) hf.injOn, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hmaps r hr
  · have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn T.finite_toSet
    rw [Set.ncard_coe_finset, hT] at h
    calc _ ≤ (((2 * M + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 * (M : ℝ) + 1) ^ n := by push_cast; rfl
      _ ≤ ((2 * c + 3) * R) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith
      _ = _ := mul_pow _ _ _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteModuleMaximalIdealAnnihilation
section
theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfFiniteOverNormal
section
namespace UpperTheory

open nonZeroDivisors

private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)

theorem integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfIsFiniteLength
section
open IsLocalRing in
private lemma finite_of_isFiniteLength {S : Type} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] {M : Type} [AddCommGroup M] [Module S M]
    (h : IsFiniteLength S M) : Finite M := by
  induction h with
  | of_subsingleton => exact Finite.of_subsingleton
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal S := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    haveI : Finite (S ⧸ maximalIdeal S) := ‹Finite (ResidueField S)›
    haveI : Finite (M ⧸ N) := Finite.of_equiv _ e.symm.toEquiv
    haveI : Finite (M ⧸ N.toAddSubgroup) := ‹Finite (M ⧸ N)›
    haveI : Finite N.toAddSubgroup := ih
    exact Finite.of_addSubgroup_quotient N.toAddSubgroup

open IsLocalRing in
theorem UpperTheory.monic_ideal_completion :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
        [IsLocalHom (algebraMap O R)]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (J : Ideal R) (hJ : ∀ x : R, ∃ P : Polynomial O, P.Monic ∧ Polynomial.aeval x P ∈ J)
        (ϖ : O) (hϖ : Irreducible ϖ),
        Finite (R ⧸ (J ⊔ Ideal.span {algebraMap O R ϖ})) := by
  intro O R _ _ _ _ _ _ _ _ _ hres J hJ ϖ hϖ
  obtain ⟨I, hIdef⟩ : ∃ I, I = J ⊔ Ideal.span {algebraMap O R ϖ} := ⟨_, rfl⟩
  rw [← hIdef]
  have hJI : J ≤ I := hIdef ▸ le_sup_left
  have hϖI : algebraMap O R ϖ ∈ I :=
    hIdef ▸ (le_sup_right : _ ≤ J ⊔ Ideal.span {algebraMap O R ϖ}) (Ideal.subset_span rfl)
  by_cases hI : I = ⊤
  · subst hI
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Finite.of_subsingleton
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral O (R ⧸ I) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hx⟩ := hJ x
    refine ⟨P, hP, ?_⟩
    rw [← Polynomial.aeval_def]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O I) x P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJI hx)⟩
  have hm : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun Q hQ =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) Q (by
      have hle : Ideal.span {ϖ} ≤ Q.comap (algebraMap O (R ⧸ I)) := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        have : algebraMap O (R ⧸ I) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hϖI
        rw [this]
        exact Q.zero_mem
      have hne : Q.comap (algebraMap O (R ⧸ I)) ≠ ⊤ := (Ideal.comap_isPrime _ Q).ne_top
      change (Q.comap (algebraMap O (R ⧸ I))).IsMaximal
      rw [← hm.eq_of_le hne hle]
      exact hm)
  haveI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hmk : ∀ x ∈ maximalIdeal R, Ideal.Quotient.mk I x ∈ maximalIdeal (R ⧸ I) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hz
    have h1 := hImax hz
    have h2 : x * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hx
    have h3 : (1 : R) ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem h2 h1
      simpa using this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
  let φ : O →+* ResidueField (R ⧸ I) := (residue (R ⧸ I)).comp (algebraMap O (R ⧸ I))
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres x
    refine ⟨a, ?_⟩
    have h := hmk _ ha
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hφk : ∀ a ∈ maximalIdeal O, φ a = 0 := by
    intro a ha
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (isUnit_of_map_unit (algebraMap O R) a hu)
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmk _ h1)
  haveI : Finite (O ⧸ maximalIdeal O) := ‹Finite (ResidueField O)›
  haveI : Finite (ResidueField (R ⧸ I)) :=
    Finite.of_surjective (Ideal.Quotient.lift (maximalIdeal O) φ hφk)
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφs)
  exact finite_of_isFiniteLength (S := R ⧸ I) (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitePlaceSumLe
section
theorem UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le.{u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberField.FinitePlace K) {α : Type u_2} (s : Finset α)
      (f : α → K) {B : ℝ}, (0 : ℝ) ≤ B → (∀ a ∈ s, (v : K → ℝ) (f a) ≤ B) → (v : K → ℝ) (∑ a ∈ s, f a) ≤ B := by
  intro K _ _ v α s f B hB h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.FinitePlace.add_le v _ _).trans
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteSpanAddSmul
section
theorem UpperTheory.finite_span_add_smul :
    ∀ {ι V : Type} [AddCommGroup V] [Module ℂ V] (T : ι → V →ₗ[ℂ] V) (S : Set ι) (a b : V) (z : ℂ),
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i a) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i b) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i (a + z • b)) '' S)) := by
  intro ι V _ _ T S a b z ha hb
  have hle : Submodule.span ℂ ((fun i => T i (a + z • b)) '' S) ≤
      Submodule.span ℂ ((fun i => T i a) '' S) ⊔ Submodule.span ℂ ((fun i => T i b) '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [map_add (f := _), map_smul, SetLike.mem_coe]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.smul_mem _ z (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle
end

