module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfHomogeneousAevalMemMaximalIdealPowSucc
section
open IsLocalRing UpperTheory.V.Alg

private def Cg {A : Type} [CommRing A] (I : Ideal A) (k : ℕ) (a b : A) : Prop :=
  b ∈ I ^ k ∧ a - b ∈ I ^ (k + 1)

private theorem Cg.mul {A : Type} [CommRing A] {I : Ideal A} {k l : ℕ} {a b c d : A}
    (h1 : Cg I k a b) (h2 : Cg I l c d) : Cg I (k + l) (a * c) (b * d) := by
  have hc : c ∈ I ^ l := by
    have := (I ^ l).add_mem (Ideal.pow_le_pow_right (Nat.le_succ l) h2.2) h2.1
    simpa using this
  refine ⟨by rw [pow_add]; exact Ideal.mul_mem_mul h1.1 h2.1, ?_⟩
  have e : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · rw [show k + l + 1 = (k + 1) + l by ring, pow_add]
    exact Ideal.mul_mem_mul h1.2 hc
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul h1.1 h2.2

private theorem Cg.refl {A : Type} [CommRing A] (I : Ideal A) (a : A) : Cg I 0 a a :=
  ⟨by simp, by simp⟩

private theorem Cg.pow {A : Type} [CommRing A] {I : Ideal A} {a b : A}
    (h : Cg I 1 a b) (k : ℕ) : Cg I k (a ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using Cg.refl I 1
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem Cg.prod {A ι : Type} [CommRing A] {I : Ideal A} {a b : ι → A}
    (h : ∀ i, Cg I 1 (a i) (b i)) (d : ι → ℕ) (s : Finset ι) :
    Cg I (∑ i ∈ s, d i) (∏ i ∈ s, a i ^ d i) (∏ i ∈ s, b i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cg.refl I 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

private theorem order_of_mem_pow {σ E : Type} [Field E] (k : ℕ) :
    ∀ f : MvPowerSeries σ E, f ∈ maximalIdeal (MvPowerSeries σ E) ^ k → (k : ℕ∞) ≤ f.order := by
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      have h1 : ((1 : ℕ) : ℕ∞) ≤ b.order := by
        refine MvPowerSeries.nat_le_order ?_
        intro d hd
        have hd0 : d = 0 := by
          have : Finsupp.degree d = 0 := by omega
          exact (Finsupp.degree_eq_zero_iff d).1 this
        subst hd0
        rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
          isUnit_iff_ne_zero, not_not] at hb
        simpa using hb
      refine le_trans ?_ MvPowerSeries.le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih a ha) h1
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

theorem UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) E) (c : O), c ≠ 0 → (∀ i, u i - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (h : MvPolynomial (Fin n) O), h.IsHomogeneous N → MvPolynomial.aeval u h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) → h = 0 := by
  intro O E _ _ _ _ _ n u c hc hu N h hh hm
  classical
  set I := maximalIdeal (MvPowerSeries (Fin n) E) with hI
  let v : Fin n → MvPowerSeries (Fin n) E := fun i => c • MvPowerSeries.X i
  have hv : ∀ i, Cg I 1 (u i) (v i) := by
    intro i
    refine ⟨?_, hu i⟩
    rw [pow_one]
    have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ I := by
      rw [hI, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    show c • MvPowerSeries.X i ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hX
  have hdeg : ∀ d ∈ h.support, ∑ i, d i = N := by
    intro d hd
    have := hh (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rfl
  have hdiff : MvPolynomial.aeval u h - MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d hd => ?_
    rw [← mul_sub]
    refine Ideal.mul_mem_left _ _ ?_
    have := (Cg.prod hv d Finset.univ).2
    rwa [hdeg d hd] at this
  have hvm : MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    have := (I ^ (N + 1)).sub_mem hm hdiff
    simpa using this
  have hval : MvPolynomial.aeval v h =
      ∑ d ∈ h.support, MvPowerSeries.monomial d (algebraMap O E (h.coeff d * c ^ N)) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd => ?_
    have hX : (∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ^ d i)
        = MvPowerSeries.monomial d 1 := by
      have h1 : ((MvPolynomial.monomial d (1 : E) : MvPolynomial (Fin n) E) :
          MvPowerSeries (Fin n) E) = MvPowerSeries.monomial d 1 := MvPolynomial.coe_monomial _ _
      rw [← h1, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp [map_prod]
    simp only [v, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hdeg d hd, hX, ← mul_assoc, ← map_pow, ← map_mul, MvPowerSeries.algebraMap_apply,
      ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]
    simp
  by_contra hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.2 hne
  have h0 : MvPowerSeries.coeff d (MvPolynomial.aeval v h) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ _ hvm))
    rw [Finsupp.degree_eq_sum, hdeg d hd]
    exact_mod_cast Nat.lt_succ_self N
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hval, map_sum, Finset.sum_eq_single d] at h0
  · rw [MvPowerSeries.coeff_monomial_same,
      map_eq_zero_iff _ (IsFractionRing.injective O E)] at h0
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd) (pow_ne_zero _ hc) h0
  · intro e _ he
    exact MvPowerSeries.coeff_monomial_ne he.symm _
  · intro h'; exact absurd hd h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDerivationsDualToCotangentParameters
section
open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.exists_derivations_dual_to_cotangent_parameters :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → ∃ (n : ℕ) (D : Fin n → (R →ₗ[O] E)) (t : Fin n → R) (c : O), c ≠ 0 ∧ (∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) ∧ (∀ i, ∀ a ∈ I, D i a = 0) ∧ (∀ i, x (t i) = 0) ∧ (∀ i j, D j (t i) = if j = i then algebraMap O E c else 0) ∧ ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I := by
  intro O E _ _ _ _ _ R _ _ _ I x hI
  classical
  set p : Ideal R := RingHom.ker x with hp
  have hmem : ∀ a, a ∈ p ↔ x a = 0 := fun a => RingHom.mem_ker
  let J : Ideal R := p ^ 2 ⊔ I
  have hJp : J ≤ p := sup_le (Ideal.pow_le_self two_ne_zero) hI
  let N : Submodule O R := Submodule.span O {(1 : R)} ⊔ J.restrictScalars O
  let f : (R ⧸ N) →ₗ[O] TensorProduct O E (R ⧸ N) := TensorProduct.mk O E (R ⧸ N) 1
  let π : R →ₗ[O] TensorProduct O E (R ⧸ N) := f ∘ₗ N.mkQ
  have hπN : ∀ a ∈ N, π a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero N).2 ha
    simp only [π, LinearMap.comp_apply, this, map_zero]
  have hJN : ∀ a ∈ J, a ∈ N := fun a ha => Submodule.mem_sup_right (by simpa using ha)
  have h1N : (1 : R) ∈ N := Submodule.mem_sup_left (Submodule.subset_span rfl)
  have hsub : ∀ a : R, a - x a • (1 : R) ∈ p := by
    intro a
    rw [hmem]
    simp
  have hder : ∀ a b, π (a * b) = x a • π b + x b • π a := by
    intro a b
    have h1 : (a - x a • (1 : R)) * (b - x b • (1 : R)) ∈ N := by
      apply hJN
      apply Submodule.mem_sup_left
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    have h2 : a * b = (a - x a • (1 : R)) * (b - x b • (1 : R)) - (x a * x b) • (1 : R)
        + (x a • b + x b • a) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [h2, map_add (f := _), hπN _ (N.sub_mem h1 (N.smul_mem _ h1N))]
    simp
  have hker : ∀ a, x a = 0 → π a = 0 → ∃ e : O, e ≠ 0 ∧ e • a ∈ J := by
    intro a ha h
    have h' : f (N.mkQ a) = 0 := h
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) f).1 h'
    refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    have h3 : (s : O) • a ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N]
      simpa [Submonoid.smul_def] using hs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hv' : v ∈ J := by simpa using hv
    have hxv : x v = 0 := (hmem v).1 (hJp hv')
    have := congrArg x huv
    simp [hxv, ha] at this
    rw [← huv, this]
    simpa using hv'
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian p)
  have hgp : ∀ i, x (g i) = 0 := fun i => (hmem _).1 (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range (π ∘ g)) = ⊤ := by
    have key : ∀ a ∈ p, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a ha
      rw [← hg] at ha
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_mul, hder, hgp, zero_smul, add_zero, ← IsScalarTower.algebraMap_smul E]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have key2 : ∀ a, π a ∈ Submodule.span E (Set.range (π ∘ g)) := by
      intro a
      have := key _ (hsub a)
      rwa [map_sub, hπN _ (N.smul_mem _ h1N), sub_zero] at this
    rw [eq_top_iff]
    rintro v -
    induction v with
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | tmul e q =>
      obtain ⟨a, rfl⟩ := N.mkQ_surjective q
      have : e ⊗ₜ[O] N.mkQ a = e • π a := by
        simp [π, f, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key2 a)
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' E (π ∘ g)
  haveI : Finite κ := Finite.of_injective a hainj
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ E (TensorProduct O E (R ⧸ N)) :=
    Module.Basis.mk hli (by rw [hsp, hspan])
  let b := b0.reindex ε
  let t : Fin n → R := fun i => g (a (ε.symm i))
  have hbt : ∀ i, π (t i) = b i := by
    intro i
    simp [b, b0, t]
  refine ⟨n, fun i => ((b.coord i).restrictScalars O) ∘ₗ π, t, 1, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro i u v
    rw [LinearMap.comp_apply, hder, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    rfl
  · intro i u hu
    simp [hπN u (hJN u (Submodule.mem_sup_right hu))]
  · intro i
    exact hgp _
  · intro i j
    simp [hbt, Finsupp.single_apply, eq_comm]
  · intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun i => b.repr (π u) i)
    choose o ho using hd
    have h0 : π ((d : O) • u - ∑ i, o i • t i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_smul, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (π u), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbt, ← IsScalarTower.algebraMap_smul E (o i), ho, smul_assoc]
    obtain ⟨e, he, hJ⟩ := hker _ (by simp [hu, t, hgp]) h0
    refine ⟨e * d, fun i => e * o i, mul_ne_zero he (nonZeroDivisors.coe_ne_zero d), ?_⟩
    simpa [smul_sub, Finset.smul_sum, mul_smul] using hJ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsHomogeneousLiftModKerPowSuccSup
section
open IsLocalRing UpperTheory.V.Alg

private theorem mul_mem_pow_sup {R : Type} [CommRing R] (P I : Ideal R) (m k : ℕ) (u v : R)
    (hu : u ∈ P ^ m) (hv : v ∈ P ^ k ⊔ I) : u * v ∈ P ^ (m + k) ⊔ I := by
  obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.mp hv
  rw [mul_add]
  refine Submodule.add_mem_sup ?_ (I.mul_mem_left u hi)
  rw [pow_add]
  exact Ideal.mul_mem_mul hu hp

theorem UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (t : Fin n → R), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) → ∀ (N : ℕ), ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O), e ≠ 0 ∧ h.IsHomogeneous N ∧ e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
  intro O R _ _ _ _ I x n t ht hyp
  have htK : ∀ i, t i ∈ RingHom.ker x := fun i => RingHom.mem_ker.mpr (ht i)
  have key : ∀ N : ℕ, ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O),
      e ≠ 0 ∧ h.IsHomogeneous N ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ N ∧
      e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
    intro N
    induction N with
    | zero =>
      intro a _
      refine ⟨1, MvPolynomial.C (x a), one_ne_zero, MvPolynomial.isHomogeneous_C _ _, ?_, ?_⟩
      · rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · apply Ideal.mem_sup_left
        rw [zero_add, pow_one, RingHom.mem_ker]
        simp
    | succ N ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on (C := fun a => ∃ (e : O) (h : MvPolynomial (Fin n) O),
        e ≠ 0 ∧ h.IsHomogeneous (N + 1) ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ∧
        e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1 + 1) ⊔ I) ha ?_ ?_
      · intro b hb c hc
        obtain ⟨e1, h1, he1, hh1, hm1, hs1⟩ := ih b hb
        have hxc : x c = 0 := RingHom.mem_ker.mp hc
        obtain ⟨e2, o, he2, hs2⟩ := hyp c hxc
        have haL : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            = ∑ i, o i • t i := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum, Algebra.smul_def]
        have hLK : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            ∈ RingHom.ker x := by
          rw [haL]
          exact Ideal.sum_mem _ (fun i _ => by
            rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ (htK i))
        refine ⟨e1 * e2, h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i,
          mul_ne_zero he1 he2, ?_, ?_, ?_⟩
        · exact hh1.mul (MvPolynomial.IsHomogeneous.sum _ _ _
            (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _))
        · rw [map_mul, pow_succ]
          exact Ideal.mul_mem_mul hm1 hLK
        · have eq : (e1 * e2) • (b * c) - MvPolynomial.aeval t
                (h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
              = (e2 • c) * (e1 • b - MvPolynomial.aeval t h1)
                + MvPolynomial.aeval t h1 * (e2 • c - ∑ i, o i • t i) := by
            rw [map_mul, haL]
            simp only [Algebra.smul_def, map_mul]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · have hc' : e2 • c ∈ RingHom.ker x ^ 1 := by
              rw [pow_one, Algebra.smul_def]
              exact Ideal.mul_mem_left _ _ hc
            have := mul_mem_pow_sup (RingHom.ker x) I 1 (N + 1) _ _ hc' hs1
            rwa [show 1 + (N + 1) = N + 1 + 1 by omega] at this
          · have := mul_mem_pow_sup (RingHom.ker x) I N 2 _ _ hm1 hs2
            rwa [show N + 2 = N + 1 + 1 by omega] at this
      · rintro a1 a2 ⟨e1, h1, he1, hh1, hm1, hs1⟩ ⟨e2, h2, he2, hh2, hm2, hs2⟩
        refine ⟨e1 * e2, MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2, mul_ne_zero he1 he2,
          (hh1.C_mul _).add (hh2.C_mul _), ?_, ?_⟩
        · rw [map_add (f := _), map_mul, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm1) (Ideal.mul_mem_left _ _ hm2)
        · have eq : (e1 * e2) • (a1 + a2) - MvPolynomial.aeval t
                (MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2)
              = e2 • (e1 • a1 - MvPolynomial.aeval t h1)
                + e1 • (e2 • a2 - MvPolynomial.aeval t h2) := by
            simp only [map_add (f := _), map_mul, MvPolynomial.aeval_C, Algebra.smul_def]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs1
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs2
  intro N a ha
  obtain ⟨e, h, he, hh, _, hs⟩ := key N a ha
  exact ⟨e, h, he, hh, hs⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNotMemMulMemIdealOfForallPrimePowSup
section
open IsLocalRing UpperTheory.V.Alg

private theorem a3one_of_factSplit_of_countCont (R : Type) [CommRing R] [IsNoetherianRing R] (I p : Ideal R) [hp : p.IsPrime]
    (a : R) (h : ∀ N : ℕ, ∃ s, s ∉ p ∧ s * a ∈ p ^ N ⊔ I) : ∃ y, y ∉ p ∧ y * a ∈ I := by
  by_cases hIp : I ≤ p
  swap
  · obtain ⟨y, hyI, hyp⟩ := Set.not_subset.mp hIp
    exact ⟨y, hyp, I.mul_mem_right a hyI⟩
  haveI hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI : IsNoetherianRing (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) :=
    IsLocalization.isNoetherianRing (p.map (Ideal.Quotient.mk I)).primeCompl _ inferInstance
  have hKrull := Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))))
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hmem : algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
      (Ideal.Quotient.mk I a) ∈ ⨅ i : ℕ,
        IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) ^ i := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨s, hs, hsa⟩ := h N
    have h1 : Ideal.Quotient.mk I (s * a) ∈ (p.map (Ideal.Quotient.mk I)) ^ N := by
      rw [← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup]
      exact hsa
    have h2 : algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (Ideal.Quotient.mk I (s * a)) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) ^ N := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ h1
    have hs' : Ideal.Quotient.mk I s ∉ p.map (Ideal.Quotient.mk I) := by
      rwa [Ideal.mem_quotient_iff_mem hIp]
    have hsu : IsUnit (algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (Ideal.Quotient.mk I s)) :=
      IsLocalization.map_units (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (⟨Ideal.Quotient.mk I s, hs'⟩ : (p.map (Ideal.Quotient.mk I)).primeCompl)
    rw [map_mul, map_mul] at h2
    obtain ⟨u, hu⟩ := hsu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.AtPrime (p.map (Ideal.Quotient.mk I))) h2
    rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at this
  rw [hKrull, Submodule.mem_bot] at hmem
  obtain ⟨⟨c, hc⟩, hca⟩ := (IsLocalization.map_eq_zero_iff (p.map (Ideal.Quotient.mk I)).primeCompl
    (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) _).mp hmem
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hc' : Ideal.Quotient.mk I y ∉ p.map (Ideal.Quotient.mk I) := hc
  refine ⟨y, fun hy => hc' (Ideal.mem_map_of_mem _ hy), ?_⟩
  have hca' : Ideal.Quotient.mk I y * Ideal.Quotient.mk I a = 0 := hca
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hca'
  exact hca'

theorem UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I p P : Ideal R), p.IsPrime → I ≤ p → (∀ a ∈ P, ∀ N : ℕ, ∃ s, s ∉ p ∧ s * a ∈ p ^ N ⊔ I) → ∃ y, y ∉ p ∧ ∀ a ∈ P, y * a ∈ I := by
  classical
  intro R _ _ I p P hp hIp hP
  haveI := hp
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian P : P.FG)
  have h1p : (1 : R) ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  have hgen : ∀ T : Finset R, (T : Set R) ⊆ P → ∃ y, y ∉ p ∧ ∀ a ∈ T, y * a ∈ I := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1p, by simp⟩
    | insert b T hb ih =>
      intro hT
      obtain ⟨y1, hy1, hy1'⟩ := ih (fun z hz => hT (Finset.mem_insert_of_mem hz))
      obtain ⟨y2, hy2, hy2'⟩ := a3one_of_factSplit_of_countCont R I p b (hP b (hT (Finset.mem_insert_self b T)))
      refine ⟨y1 * y2, fun h => (hp.mem_or_mem h).elim hy1 hy2, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [mul_assoc]
        exact I.mul_mem_left _ hy2'
      · rw [mul_comm y1, mul_assoc]
        exact I.mul_mem_left _ (hy1' z hz)
  obtain ⟨y, hy, hyS⟩ := hgen S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨y, hy, fun a ha => ?_⟩
  rw [← hS] at ha
  induction ha using Submodule.span_induction with
  | mem z hz => exact hyS z hz
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add]
    exact I.add_mem hu hv
  | smul r u _ hu =>
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left r hu
end

