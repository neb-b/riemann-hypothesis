module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CompleteFin
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [Module.Finite R M], IsAdicComplete I M := by
  intro R _ M _ _ _ I _ _
  have hH : IsHausdorff I M := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
  have hP : IsPrecomplete I M := by
    rw [← AdicCompletion.of_surjective_iff]
    have hR : Function.Surjective (AdicCompletion.of I R) := AdicCompletion.of_surjective_iff.mpr inferInstance
    intro x
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a m =>
      obtain ⟨r, rfl⟩ := hR a
      refine ⟨r • m, ?_⟩
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
      ext n
      rw [AdicCompletion.val_smul_apply]
      simp
      try rfl
    | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add (f := _), map_add (f := _), hu, hv]⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigNilInt
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (T : Module.End O M), LinearMap.range T ≤ IsLocalRing.maximalIdeal O • ⊤ → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → T.baseChange K y = μ • y → μ ≠ 0 → ¬ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint
  obtain ⟨p, hmon, -, hcoef, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)
  have hK : Polynomial.aeval (T.baseChange K) p = 0 := by
    have e : T.baseChange K = Module.End.baseChangeHom O K M T := rfl
    rw [e, Polynomial.aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvector (T.baseChange K) μ y :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩
  have hq : Polynomial.aeval μ p = 0 := by
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy
  set n := p.natDegree with hn
  set ν := μ⁻¹ with hνdef
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hq
    have h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0 := by
      rw [hq, mul_zero]
    rw [mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hp' : ν ^ n = ν ^ (n - i) * ν ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
    have e : ν ^ i * μ ^ i = 1 := by rw [← mul_pow, hνμ, one_pow]
    rw [Algebra.smul_def, hp']
    calc algebraMap O K (p.coeff i) * ν ^ (n - i)
        = algebraMap O K (p.coeff i) * ν ^ (n - i) * (ν ^ i * μ ^ i) := by rw [e, mul_one]
      _ = ν ^ (n - i) * ν ^ i * (algebraMap O K (p.coeff i) * μ ^ i) := by ring
  let C := integralClosure O K
  let ν' : C := ⟨ν, hint⟩
  have hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0 := by
    apply Subtype.ext
    simpa [C, ν'] using key
  have hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈
      (IsLocalRing.maximalIdeal O).map (algebraMap O C) := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have hin : i < n := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hcoef i)
  have htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]
    exact (Ideal.neg_mem_iff _).mpr hmem
  have hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hint' : (algebraMap O C).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOfQuot
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent
    {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (U : Submodule K Y) :
    U ≠ ⊥ → (∀ i, ∀ y ∈ U, T i y ∈ U) → (∀ i, ∀ y ∈ U, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → V ≠ ⊥ →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → (∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv hnil
  by_cases hall : ∀ i, ∀ y ∈ V, T i y = 0
  · obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    exact ⟨y, hy0, fun i => hall i y hyV⟩
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  have hpowmem : ∀ k : ℕ, (T i ^ k) z ∈ V := by
    intro k
    induction k with
    | zero => simpa using hzV
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hinv i _ ihk
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i)
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWne : W ≠ ⊥ := by
    classical
    have hex : ∃ n : ℕ, (T i ^ n) z = 0 := hnil i z hzV
    have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hz0 this
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hspec := Nat.find_spec hex
    rw [hm] at hspec
    have hmin : (T i ^ m) z ≠ 0 := Nat.find_min hex (by omega)
    rw [Submodule.ne_bot_iff]
    refine ⟨(T i ^ m) z, Submodule.mem_inf.mpr ⟨hpowmem m, ?_⟩, hmin⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
    exact hspec
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, hyk, map_zero]
  have hWnil : ∀ j, ∀ y ∈ W, ∃ n : ℕ, (T j ^ n) y = 0 :=
    fun j y hy => hnil j y (hWle hy)
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWne hWinv hWnil

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot
    {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (φ : Y →ₗ[K] Z)
    (hφ : ∀ i y, φ (T i y) = 0) (U : Submodule K Y) :
    (∃ u ∈ U, φ u ≠ 0) → (∀ i, ∀ y ∈ U, T i y ∈ U) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  intro hu hinv
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → (∃ u ∈ V, φ u ≠ 0) →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl hu hinv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv
  obtain ⟨u, huV, hu⟩ := hV
  have hVne : V ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨u, huV, fun h0 => hu (by rw [h0, map_zero])⟩
  by_cases hall : ∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0
  · exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent T hc V hVne hinv hall
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  let f : Module.End K V := (T i).restrict (hinv i)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_codisjoint_ker_pow_range_pow f)
  have hcod := hn (n + 1) (by omega)
  have hfpow : ∀ (k : ℕ) (w : V), ((f ^ k) w : Y) = (T i ^ k) (w : Y) := by
    intro k w
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
      rfl
  have hmem : (⟨u, huV⟩ : V) ∈ LinearMap.ker (f ^ (n + 1)) ⊔ LinearMap.range (f ^ (n + 1)) := by
    rw [codisjoint_iff.mp hcod]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hb
  have hφb : φ (((f ^ (n + 1)) c : V) : Y) = 0 := by
    rw [hfpow, pow_succ', Module.End.mul_apply, hφ]
  have hab' : (a : Y) + (((f ^ (n + 1)) c : V) : Y) = u := by
    have := congrArg Subtype.val hab
    simpa using this
  have hφa : φ (a : Y) ≠ 0 := by
    have h2 := congrArg φ hab'
    rw [map_add (f := _), hφb, add_zero] at h2
    rw [h2]
    exact hu
  have haker : (T i ^ (n + 1)) (a : Y) = 0 := by
    rw [← hfpow]
    rw [LinearMap.mem_ker.mp ha]
    rfl
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i ^ (n + 1))
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (n + 1) (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, ((hc i j).pow_left (n + 1)).eq, Module.End.mul_apply, hyk,
      map_zero]
  have hWu : ∃ w ∈ W, φ w ≠ 0 :=
    ⟨(a : Y), Submodule.mem_inf.mpr ⟨a.2, LinearMap.mem_ker.mpr haker⟩, hφa⟩
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWu hWinv

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot :
    ∀ {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] [AddCommGroup Z] [Module K Z] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (φ : Y →ₗ[K] Z), φ ≠ 0 → (∀ i y, φ (A i y) = x i • φ y) → ∃ y : Y, y ≠ 0 ∧ ∀ i, A i y = x i • y := by
  intro K Y Z ι _ _ _ _ _ _ A hA x φ hφ0 hφ
  let T : ι → Module.End K Y := fun i => A i - x i • (1 : Module.End K Y)
  have hT : ∀ i y, T i y = A i y - x i • y := by
    intro i y
    simp [T]
  have hc : ∀ i j, Commute (T i) (T j) := by
    intro i j
    exact ((hA i j).sub_right ((Commute.one_right (A i)).smul_right (x j))).sub_left
      (((Commute.one_left (A j)).smul_left (x i)).sub_right
        (((Commute.one_left 1).smul_left (x i)).smul_right (x j)))
  have hφT : ∀ i y, φ (T i y) = 0 := by
    intro i y
    rw [hT, map_sub, map_smul, hφ, sub_self]
  have hu : ∃ u ∈ (⊤ : Submodule K Y), φ u ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hφ0 (LinearMap.ext fun y => by simpa using hno y Submodule.mem_top)
  obtain ⟨y, hy0, hy⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot T hc φ hφT ⊤ hu
    (fun _ _ _ => Submodule.mem_top)
  refine ⟨y, hy0, fun i => ?_⟩
  have := hy i
  rw [hT, sub_eq_zero] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigSum
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.exists_eigenvector_fixed_idempotent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hc : Commute U f) (μ : K) :
    ∀ (k : ℕ) (y : V), y ≠ 0 → f y = y → ((U - μ • (1 : Module.End K V)) ^ k) y = 0 →
      ∃ z : V, z ≠ 0 ∧ f z = z ∧ U z = μ • z := by
  intro k
  induction k with
  | zero =>
    intro y hy _ h
    rw [pow_zero, Module.End.one_apply] at h
    exact absurd h hy
  | succ k ih =>
    intro y hy hfy hk
    by_cases hw : (U - μ • (1 : Module.End K V)) y = 0
    · refine ⟨y, hy, hfy, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hw
      exact hw
    · apply ih _ hw
      · have hc' : Commute (U - μ • (1 : Module.End K V)) f :=
          hc.sub_left (Commute.smul_left (Commute.one_left f) μ)
        have := LinearMap.congr_fun hc'.eq y
        rw [Module.End.mul_apply, Module.End.mul_apply, hfy] at this
        exact this.symm
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact hk

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idempotent_kills_generalized_eigenspace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U f : Module.End K V) (hf : IsIdempotentElem f) (hc : Commute U f) (μ : K)
    (h : ∀ z : V, z ≠ 0 → f z = z → U z = μ • z → False) (y : V)
    (hy : y ∈ U.maxGenEigenspace μ) : f y = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
  have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) f :=
    (hc.sub_left (Commute.smul_left (Commute.one_left f) μ)).pow_left k
  obtain ⟨z, hz, hfz, hUz⟩ := exists_eigenvector_fixed_idempotent U f hc μ k (f y) hne
    (by rw [← Module.End.mul_apply, hf.eq])
    (by rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero])
  exact h z hz hfz hUz

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum :
    ∀ {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (U e : Module.End K V) (S : Set K), IsIdempotentElem e → Commute U e → (∀ μ y, y ≠ 0 → e y = y → U y = μ • y → μ ∈ S) → (∀ μ y, y ≠ 0 → e y = 0 → U y = μ • y → μ ∉ S) → LinearMap.range e = ⨆ μ ∈ S, U.maxGenEigenspace μ := by
  intro K V _ _ _ _ _ U e S he hc h1 h2
  have hE : ∀ μ, Submodule.map e (U.maxGenEigenspace μ) ≤ U.maxGenEigenspace μ := by
    intro μ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace U μ y).mp hy
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    have hc' : Commute ((U - μ • (1 : Module.End K V)) ^ k) e :=
      (hc.sub_left (Commute.smul_left (Commute.one_left e) μ)).pow_left k
    rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply, hk, map_zero]
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← Module.End.iSup_maxGenEigenspace_eq_top U, Submodule.map_iSup]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ S
    · exact (hE μ).trans (le_iSup₂_of_le μ hμ le_rfl)
    · rintro _ ⟨y, hy, rfl⟩
      have h0 : e y = 0 :=
        idempotent_kills_generalized_eigenspace U e he hc μ (fun z hz hez hUz => hμ (h1 μ z hz hez hUz)) y hy
      rw [h0]
      exact Submodule.zero_mem _
  · refine iSup₂_le fun μ hμ => ?_
    intro y hy
    have hf : IsIdempotentElem (1 - e) := he.one_sub
    have hc1 : Commute U (1 - e) := (Commute.one_right U).sub_right hc
    have h0 := idempotent_kills_generalized_eigenspace U (1 - e) hf hc1 μ
      (fun z hz hez hUz => h2 μ z hz
        (by rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_self] at hez; exact hez) hUz hμ) y hy
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
    exact ⟨y, h0.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigUnitInt
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite
    {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (T : Module.End O M) (μ : K) (y : K ⊗[O] M) (hy : y ≠ 0)
    (h : T.baseChange K y = μ • y) : IsIntegral O μ := by
  obtain ⟨p, hp, hT⟩ := LinearMap.exists_monic_and_aeval_eq_zero O T
  have key : ∀ q : Polynomial O,
      (Polynomial.aeval T q).baseChange K y = (Polynomial.aeval μ q) • y := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.smul_apply,
        Module.End.one_apply, algebraMap_smul]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval T), map_mul (Polynomial.aeval μ),
        Polynomial.aeval_X, Polynomial.aeval_X, LinearMap.baseChange_mul, Module.End.mul_apply,
        h, map_smul, ih, smul_smul, mul_comm]
  have h0 := key p
  rw [hT, LinearMap.baseChange_zero, LinearMap.zero_apply] at h0
  have h1 : Polynomial.aeval μ p = 0 := (smul_eq_zero.mp h0.symm).resolve_right hy
  exact ⟨p, hp, by rwa [Polynomial.aeval_def] at h1⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (U V e : Module.End O M), V * U * e = e → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → e.baseChange K y = y → U.baseChange K y = μ • y → μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ M _ _ _ U V e hVU μ y hy he hU
  have h1 : μ • V.baseChange K y = y := by
    have h := congrArg (fun f : Module.End O M => f.baseChange K y) hVU
    simp only [LinearMap.baseChange_mul, Module.End.mul_apply] at h
    rwa [he, hU, map_smul] at h
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    exact hy h1.symm
  have h2 : V.baseChange K y = μ⁻¹ • y := by
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
  exact ⟨hμ, UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite U μ y hy hU,
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite V μ⁻¹ y hy h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FibreNe
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe :
    ∀ {T K M : Type*} [CommRing T] [Field K] [Algebra T K] [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M], Nontrivial (K ⊗[T] M) := by
  intro T K M _ _ _ _ _ _ _
  classical
  haveI hp : (RingHom.ker (algebraMap T K)).IsPrime := RingHom.ker_isPrime _
  set p : Ideal T := RingHom.ker (algebraMap T K) with hpdef
  let P : PrimeSpectrum T := ⟨p, hp⟩
  have hP : P ∈ Module.support T M := by
    rw [Module.support_eq_zeroLocus, (Module.annihilator_eq_bot).mpr inferInstance]
    simp
  have hV : Nontrivial (p.ResidueField ⊗[T] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct P).mp hP
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap T K) le_rfl (by
    intro x hx
    have hx' : algebraMap T K x ≠ 0 := fun h => hx ((RingHom.mem_ker).mpr h)
    exact (isUnit_iff_ne_zero.mpr hx'))
  letI : Algebra p.ResidueField K := f.toAlgebra
  haveI : IsScalarTower T p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap T K) le_rfl _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange T p.ResidueField K K M
  haveI : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[T] M)) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right p.ResidueField
      K (p.ResidueField ⊗[T] M) (Algebra.linearMap p.ResidueField K)
      (algebraMap p.ResidueField K).injective
  exact e.symm.nontrivial
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeModel
section
open IsLocalRing UpperTheory.V.Hi

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M) (op : ι → Module.End A M), CommOn Y op → ∃ (T : Type) (_ : CommRing T) (_ : Algebra A T) (j : T →ₐ[A] Module.End A Y) (t : ι → T), Function.Injective j ∧ j.range = heckeAlg Y op ∧ (∀ i, Restr (j (t i)) (op i)) ∧ Algebra.adjoin A (Set.range t) = ⊤ ∧ (IsNoetherianRing A → Module.Finite A Y → Module.Finite A T) := by
  intro A M ι _ _ _ Y op h
  have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
      ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, s * t = t * s := by
    rintro s ⟨i, hi⟩ t ⟨j, hj⟩
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (s (t y) : M) = t (s y)
    rw [hi, hj, hj, hi]
    exact h.2 i j y y.2
  have hc : ∀ a b : heckeAlg Y op, a * b = b * a := by
    exact isMulCommutative_iff.mp
      (Algebra.isMulCommutative_adjoin A (fun a ha b hb _ => key a ha b hb))
  let t : ι → heckeAlg Y op := fun i =>
    ⟨(op i).restrict (h.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩
  have htop : Algebra.adjoin A (Set.range t) = ⊤ := by
    have h1 : Set.range t = ((↑) : heckeAlg Y op → Module.End A Y) ⁻¹'
        {t : Module.End A Y | ∃ i, Restr t (op i)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, fun _ => rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext (LinearMap.ext fun y => Subtype.ext (hi y).symm)⟩
    rw [h1]
    exact Algebra.adjoin_adjoin_coe_preimage
  have hfin : IsNoetherianRing A → Module.Finite A Y → Module.Finite A (heckeAlg Y op) := by
    intro _ _
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := Y)
    let f : heckeAlg Y op →ₗ[A] (Fin n → Y) :=
      { toFun := fun t i => (t : Module.End A Y) (s i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun a b => by ext i; simp }
    have hf : Function.Injective f := by
      intro a b hab
      refine Subtype.ext (LinearMap.ext_on_range hs fun i => ?_)
      exact congrFun hab i
    exact Module.Finite.of_injective f hf
  exact ⟨heckeAlg Y op, { (inferInstance : Ring (heckeAlg Y op)) with mul_comm := hc },
    (inferInstance : Algebra A (heckeAlg Y op)), (heckeAlg Y op).val, t, Subtype.val_injective,
    Subalgebra.range_val _, fun i _ => rfl, htop, hfin⟩
end

