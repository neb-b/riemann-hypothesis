module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.FiniteStability

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped TensorProduct

private theorem ns_point (K R : Type) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (Q : Ideal R) (hQ : Q.IsPrime) (x : R) (hx : x ∉ Q) :
    ∃ ψ : R →ₐ[K] K, (∀ y ∈ Q, ψ y = 0) ∧ ψ x ≠ 0 := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hj : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hx
  push Not at hx
  obtain ⟨M, ⟨hQM, hM⟩, hxM⟩ := hx
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  haveI : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsAlgebraic.of_finite K _
  let e : (R ⧸ M) →ₐ[K] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨e.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩
  · have : Ideal.Quotient.mk M y = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hQM hy)
    simp [this]
  · have : Ideal.Quotient.mk M x ≠ 0 := fun h => hxM (Ideal.Quotient.eq_zero_iff_mem.1 h)
    simpa using this

private theorem ns_prime (B A K : Type) [CommRing B] [CommRing A] [Field K] [Algebra B A] [Algebra B K]
    (P : Ideal A) [P.IsPrime] (hP : ∀ b, algebraMap B A b ∈ P ↔ algebraMap B K b = 0) :
    ∃ Q : Ideal (K ⊗[B] A), Q.IsPrime ∧ ∀ a : A, (1 : K) ⊗ₜ[B] a ∈ Q ↔ a ∈ P := by
  let p : Ideal B := P.under B
  haveI : p.IsPrime := inferInstance
  have h1 : p ≤ RingHom.ker (algebraMap B K) := fun b hb => (hP b).1 hb
  have h2 : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap B K) := fun b hb =>
    (isUnit_iff_ne_zero.2 (fun h => hb ((hP b).2 h)) : IsUnit (algebraMap B K b))
  have h1' : p ≤ RingHom.ker (algebraMap B P.ResidueField) := fun b hb => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]
    exact hb
  have h2' : p.primeCompl ≤ (IsUnit.submonoid P.ResidueField).comap (algebraMap B P.ResidueField) :=
    fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb (by
      rw [IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero] at h
      exact h)) : IsUnit (algebraMap B P.ResidueField b))
  letI aK : Algebra p.ResidueField K := (Ideal.ResidueField.lift p _ h1 h2).toAlgebra
  letI aL : Algebra p.ResidueField P.ResidueField := (Ideal.ResidueField.lift p _ h1' h2').toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1 h2 b).symm
  haveI : IsScalarTower B p.ResidueField P.ResidueField := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1' h2' b).symm
  let T := K ⊗[p.ResidueField] P.ResidueField
  haveI : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    p.ResidueField K P.ResidueField (RingHom.injective _) (RingHom.injective _)
  obtain ⟨N, hN⟩ := Ideal.exists_maximal T
  let i1 : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft (S := B))
  let j : P.ResidueField →ₐ[p.ResidueField] T := Algebra.TensorProduct.includeRight
  let i2 : A →ₐ[B] T := (j.restrictScalars B).comp (IsScalarTower.toAlgHom B A P.ResidueField)
  let φ : K ⊗[B] A →ₐ[B] T := Algebra.TensorProduct.lift i1 i2 (fun _ _ => Commute.all _ _)
  refine ⟨N.comap φ, Ideal.comap_isPrime _ _, fun a => ?_⟩
  have hφ : φ ((1 : K) ⊗ₜ[B] a) = j (algebraMap A P.ResidueField a) := by
    simp [φ, i2]
  rw [Ideal.mem_comap, hφ]
  constructor
  · intro h
    by_contra ha
    have hu : IsUnit (algebraMap A P.ResidueField a) :=
      isUnit_iff_ne_zero.2 (fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h))
    exact hN.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map j))
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
    exact N.zero_mem

theorem UpperTheory.V.Alg.M.ns_holds :
    ∀ (O B A K : Type) [CommRing O] [CommRing B] [CommRing A] [Field K] [IsAlgClosed K] [Algebra O B] [Algebra B A]
      [Algebra O A] [IsScalarTower O B A] [Algebra O K] [Algebra.FiniteType B A] (σ : B →ₐ[O] K) (J : Ideal A) (f : A),
      (∀ b, σ b = 0 → algebraMap B A b ∈ J) → (∀ (b : B) (n : ℕ), σ b ≠ 0 → algebraMap B A b * f ^ n ∉ J) →
      ∃ ξ : A →ₐ[O] K, (∀ b, ξ (algebraMap B A b) = σ b) ∧ (∀ g ∈ J, ξ g = 0) ∧ ξ f ≠ 0 := by
  intro O B A K _ _ _ _ _ _ _ _ _ _ _ σ J f h0 h1
  let S : Submonoid A :=
    { carrier := {a | ∃ (b : B) (n : ℕ), σ b ≠ 0 ∧ a = algebraMap B A b * f ^ n}
      one_mem' := ⟨1, 0, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, n, hb, rfl⟩ ⟨c, m, hc, rfl⟩
        exact ⟨b * c, n + m, by simp [hb, hc], by rw [map_mul]; ring⟩ }
  have hd : Disjoint (J : Set A) (S : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, n, hb, rfl⟩
    exact h1 b n hb ha
  obtain ⟨P, hP, hJP, hPS⟩ := Ideal.exists_le_prime_disjoint J S hd
  rw [Set.disjoint_left] at hPS
  letI : Algebra B K := σ.toRingHom.toAlgebra
  have hσ : ∀ b, algebraMap B K b = σ b := fun _ => rfl
  haveI : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun o => by
    rw [hσ, AlgHom.commutes]
  obtain ⟨Q, hQ, hQP⟩ := ns_prime B A K P (fun b => by
    rw [hσ]
    constructor
    · intro hb
      by_contra hne
      exact hPS hb ⟨b, 0, hne, by simp⟩
    · intro hb
      exact hJP (h0 b hb))
  have hf : f ∉ P := fun h => hPS h ⟨1, 1, by simp, by simp⟩
  obtain ⟨ψ, hψ0, hψ1⟩ := ns_point K (K ⊗[B] A) Q hQ ((1 : K) ⊗ₜ[B] f) (fun h => hf ((hQP f).1 h))
  let ξ : A →ₐ[B] K := (ψ.restrictScalars B).comp Algebra.TensorProduct.includeRight
  refine ⟨ξ.restrictScalars O, fun b => ?_, fun g hg => ?_, hψ1⟩
  · exact (ξ.commutes b).trans (hσ b)
  · exact hψ0 _ ((hQP g).2 (hJP hg))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NzCoeffMul
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem nz_coeff_mul {τ E : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd := congrArg Finsupp.degree h
  rw [map_add (f := _), Finsupp.degree_single] at hd
  by_cases h1 : Finsupp.degree p.1 = 0
  · rw [(Finsupp.degree_eq_zero_iff _).1 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem nz_comp {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 := by
  classical
  obtain ⟨f, hf, -⟩ := h.onto i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum, map_sum] at hf
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hm := (DirectSum.decompose 𝒜 f j).2
  have hw : wt i = j := by
    by_contra hne
    exact hj (h.graded j _ hm _ (by simpa [Finsupp.weight_single] using hne))
  exact ⟨_, hw ▸ hm, hj⟩

theorem UpperTheory.V.Alg.M.nz_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ Nat.card {i // wt i = -1} → 1 ≤ Nat.card {i // wt i = 1} → SpansCot x 𝒜 (-1) Q.F →
    ∀ a ∈ 𝒜 0, ∃ a' ∈ 𝒜 0, a' - a ∈ Q.ideal ∧ x a' = x a ∧ φ a' ≠ 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hn hp hS a ha
  by_cases h0 : φ a = 0
  swap
  · exact ⟨a, ha, by simp, rfl, h0⟩
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hn).1
  obtain ⟨⟨i', hi'⟩⟩ := (Nat.card_pos_iff.1 hp).1
  obtain ⟨f, hf, hf0⟩ := nz_comp 𝒜 x wt φ hφ i
  obtain ⟨g, hg, hg0⟩ := nz_comp 𝒜 x wt φ hφ i'
  rw [hi] at hf
  rw [hi'] at hg
  have hg1 : φ g ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hinj : ∀ c : O, c ≠ 0 → ∀ y : FractionRing O, c • y = 0 → y = 0 := fun c hc y hy => by
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left fun h => hc (IsFractionRing.injective O _ (h.trans (map_zero _).symm))
  have hF : ∃ k, φ (Q.F k) ≠ 0 := by
    by_contra hall
    push Not at hall
    let L : A →ₗ[O] FractionRing O :=
      ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap
    have hL : ∀ y, L y = MvPowerSeries.coeff (Finsupp.single i 1) (φ y) := fun _ => rfl
    have hsq : ∀ y ∈ RingHom.ker x ^ 2, L y = 0 := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => by rw [map_add (f := _), hu, hv, add_zero])
      have hu' : x u = 0 := hu
      have hv' : x v = 0 := hv
      rw [hL, map_mul]
      exact nz_coeff_mul _ _ _ (by rw [hφ.const, hu', map_zero]) (by rw [hφ.const, hv', map_zero])
    have hk : satSq x ≤ LinearMap.ker L := by
      rintro y ⟨c, hc, hy⟩
      have := hsq _ hy
      rw [map_smul] at this
      exact hinj c hc _ this
    have hsp : cotSpan x Q.F ≤ LinearMap.ker ((satSq x).liftQ L hk) := by
      rw [cotSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show L (Q.F k) = 0
      rw [hL, hall k, map_zero]
    obtain ⟨c, hc, hcf⟩ := hS ((satSq x).mkQ f) ⟨f, ⟨hf, hW.fixed (-1) (by norm_num) f hf⟩, rfl⟩
    have := hsp hcf
    rw [LinearMap.mem_ker, map_smul] at this
    exact hf0 (hinj c hc _ this)
  obtain ⟨k, hk⟩ := hF
  have hm : g * Q.F k ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hg (Q.hF k)
  refine ⟨a + g * Q.F k, add_mem ha hm, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [map_add (f := _), map_mul, hW.fixed 1 one_ne_zero g hg, zero_mul, add_zero]
  · rw [map_add (f := _), h0, zero_add, map_mul]
    exact mul_ne_zero hg1 hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private theorem absR {w a b c : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + b) :
    z * f ∈ 𝒜 a * 𝒜 c := by
  subst hc
  refine Submodule.mul_induction_on hf (fun p hp q hq => ?_) (fun p q hp hq => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul hp (SetLike.GradedMul.mul_mem hz hq)
  · rw [mul_add]; exact add_mem hp hq

private theorem absL {w a b c d : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + a) (hd : d = b) :
    z * f ∈ 𝒜 c * 𝒜 d := by
  subst hd
  rw [mul_comm (𝒜 a)] at hf
  rw [mul_comm (𝒜 c)]
  exact absR 𝒜 hz hf hc

private def dec (ε j : ℤ) : Submodule O A where
  carrier := {f | f ∈ 𝒜 j ∧ (1 ≤ ε * j → f ∈ 𝒜 ε * 𝒜 (j - ε) ⊔ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε)) ∧
    (2 ≤ ε * j → f ∈ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε))}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun h => add_mem (ha.2.1 h) (hb.2.1 h), fun h => add_mem (ha.2.2 h) (hb.2.2 h)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ ha := ⟨Submodule.smul_mem _ c ha.1, fun h => Submodule.smul_mem _ c (ha.2.1 h),
    fun h => Submodule.smul_mem _ c (ha.2.2 h)⟩

private theorem dec_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w j : ℤ} (hw : -2 ≤ w ∧ w ≤ 2) {z f : A} (hz : z ∈ 𝒜 w)
    (hf : f ∈ dec 𝒜 ε j) : z * f ∈ dec 𝒜 ε (w + j) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨SetLike.GradedMul.mul_mem hz h0, ?_⟩
  by_cases c2 : w = 2 * ε
  · subst c2
    have : z * f ∈ 𝒜 (2 * ε) * 𝒜 (2 * ε + j - 2 * ε) := by
      rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    exact ⟨fun _ => Submodule.mem_sup_right this, fun _ => this⟩
  by_cases c1 : w = ε
  · subst c1
    refine ⟨fun _ => Submodule.mem_sup_left ?_, fun h => ?_⟩
    · rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    · obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
      rw [mul_add]
      exact add_mem (absL 𝒜 hz hp (by ring) (by ring)) (absR 𝒜 hz hq (by ring))
  refine ⟨fun h => ?_, fun h => absR 𝒜 hz (h2 (by rcases hε with rfl | rfl <;> omega)) (by ring)⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
  rw [mul_add]
  exact add_mem (Submodule.mem_sup_left (absR 𝒜 hz hp (by ring))) (Submodule.mem_sup_right (absR 𝒜 hz hq (by ring)))

private theorem dec_all [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : f ∈ dec 𝒜 ε j := by
  obtain ⟨s, hs, htop⟩ := hx.gen
  have gen : ∀ (w : ℤ), (-2 ≤ w ∧ w ≤ 2) → ∀ z ∈ 𝒜 w, ∀ g ∈ ⨆ i, dec 𝒜 ε i, z * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro w hw z hz g hg
    refine Submodule.iSup_induction (motive := fun g => z * g ∈ ⨆ i, dec 𝒜 ε i) _ hg (fun i g hg => ?_) (by simp)
      (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb)
    exact Submodule.mem_iSup_of_mem _ (dec_mul 𝒜 hε hw hz hg)
  have key : ∀ a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ s), ∀ g ∈ ⨆ i, dec 𝒜 ε i, a * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact gen 0 (by omega) a ha
      · rcases hs a ha with h | h | h | h <;> exact gen _ (by omega) a h
    | algebraMap c =>
      intro g hg
      rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c hg
    | add a b _ _ ha hb =>
      intro g hg
      rw [add_mul]; exact add_mem (ha g hg) (hb g hg)
    | mul a b _ _ ha hb =>
      intro g hg
      rw [mul_assoc]; exact ha _ (hb g hg)
  have h1 : (1 : A) ∈ dec 𝒜 ε 0 := ⟨SetLike.GradedOne.one_mem, fun h => by omega, fun h => by omega⟩
  have h2 := key f (htop ▸ Algebra.mem_top) 1 (Submodule.mem_iSup_of_mem _ h1)
  rw [mul_one] at h2
  have h3 : ∀ g ∈ ⨆ i, dec 𝒜 ε i, (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j := by
    intro g hg
    refine Submodule.iSup_induction (motive := fun g => (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j) _ hg
      (fun i g hg => ?_) (by simp) (fun a b ha hb => ?_)
    · by_cases hi : i = j
      · subst hi
        rwa [DirectSum.decompose_of_mem_same 𝒜 hg.1]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hg.1 hi]; exact zero_mem _
    · simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem ha hb
  have h4 := h3 f h2
  rwa [DirectSum.decompose_of_mem_same 𝒜 hf] at h4

private theorem pow_eps [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (n : ℕ) : oz 𝒜 (2 * ε * n) = oz 𝒜 (2 * ε) ^ n := by
  induction n with
  | zero =>
    ext f
    simp only [Nat.cast_zero, mul_zero, pow_zero, mem_oz, Submodule.mem_one]
    exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  | succ n ih =>
    rw [pow_succ, mul_comm (_ ^ n), ← ih]
    apply le_antisymm
    · intro f hf
      have h := (dec_all 𝒜 hx hε hf).2.2 (by rcases hε with rfl | rfl <;> push_cast <;> omega)
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) - 2 * ε = 2 * ε * n := by push_cast; ring
      rw [e] at h
      clear hf
      refine Submodule.mul_induction_on h (fun p hp q hq => ?_) (fun p q hp hq => add_mem hp hq)
      exact Submodule.mul_mem_mul hp hq
    · refine Submodule.mul_le.2 fun p hp q hq => ?_
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) = 2 * ε + 2 * ε * n := by push_cast; ring
      rw [mem_oz, e]
      exact SetLike.GradedMul.mul_mem (A := 𝒜) hp hq

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.oz_two_mul_eq_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx n
  have h1 := pow_eps 𝒜 hx (Or.inr rfl) n
  have h2 := pow_eps 𝒜 hx (Or.inl rfl) n
  have e : (2 * -1 * n : ℤ) = -(2 * n) := by ring
  rw [e] at h1
  rw [mul_one] at h2
  exact ⟨h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.isPrime_bot
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) (⊥ : Ideal (B ⧸ P)) (by
      change ((⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P))).IsMaximal
      rw [hbot]
      exact hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
end

