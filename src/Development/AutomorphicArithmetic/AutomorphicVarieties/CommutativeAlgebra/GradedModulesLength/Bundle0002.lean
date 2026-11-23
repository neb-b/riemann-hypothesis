module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.Integral
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0002
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.ft_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    Algebra.FiniteType (𝒜 0) A ∧ ∀ I : Ideal A, M2 𝒜 I → Algebra.FiniteType O (A ⧸ I) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx
  classical
  obtain ⟨s, -, hs⟩ := hx.gen
  have htop : ∀ a : A, a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) := by
    intro a
    rw [hs]
    trivial
  refine ⟨?_, ?_⟩
  · refine ⟨⟨s, top_unique ?_⟩⟩
    intro a _
    have key : Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · exact (Subalgebra.mem_restrictScalars O).mpr
          (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (s : Set A)) (⟨z, hz⟩ : 𝒜 0))
      · exact (Subalgebra.mem_restrictScalars O).mpr (Algebra.subset_adjoin hz)
    exact (Subalgebra.mem_restrictScalars O).mp (key (htop a))
  · intro I hI
    obtain ⟨t, ht⟩ := hI
    refine ⟨⟨t ∪ s.image (Ideal.Quotient.mkₐ O I), top_unique ?_⟩⟩
    rintro y -
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I y
    have hm : Ideal.Quotient.mkₐ O I a ∈
        (Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A))).map (Ideal.Quotient.mkₐ O I) :=
      Subalgebra.mem_map.mpr ⟨a, htop a, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_union] at hm
    refine (Algebra.adjoin_le ?_) hm
    rintro z (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · have hz : Ideal.Quotient.mkₐ O I b ∈ Submodule.span O (t : Set (A ⧸ I)) := by
        rw [ht]
        exact Submodule.mem_map_of_mem hb
      have h2 := Algebra.span_le_adjoin O (t : Set (A ⧸ I)) hz
      refine Algebra.adjoin_mono ?_ h2
      push_cast
      exact Set.subset_union_left
    · apply Algebra.subset_adjoin
      push_cast
      exact Set.mem_union_right _ (Set.mem_image_of_mem _ hb)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private noncomputable def monoL (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add (f := _)])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem eq_mono {m : Fin k →₀ ℕ} {p : rees N} (hp : p ∈ reesGr N (toDeg m)) :
    p = mono N m (AddMonoidAlgebra.coeff p.1 m) (p.2 m) := by
  classical
  apply Subtype.ext
  ext n
  show _ = AddMonoidAlgebra.coeff (MvPolynomial.monomial m _) n
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hp n fun h' => h (toDeg_injective h').symm

private theorem gr_eq_range (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  apply le_antisymm
  · intro p hp
    exact ⟨⟨_, p.2 m⟩, (eq_mono N hp).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem e_eq (i : Fin k) : e i = toDeg (Finsupp.single i 1) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [e, toDeg]
  · simp [e, toDeg, Pi.single_apply, h, Finsupp.single_apply, Ne.symm h]

private theorem gr_add (m m' : Fin k →₀ ℕ) :
    reesGr N (toDeg (m + m')) = reesGr N (toDeg m) * reesGr N (toDeg m') := by
  apply le_antisymm
  · intro p hp
    have hf : AddMonoidAlgebra.coeff p.1 (m + m') ∈ lat N m * lat N m' := by
      rw [← lat_add]
      exact p.2 (m + m')
    obtain ⟨q, hq, hqv⟩ : ∃ q ∈ reesGr N (toDeg m) * reesGr N (toDeg m'),
        q.1 = MvPolynomial.monomial (m + m') (AddMonoidAlgebra.coeff p.1 (m + m')) := by
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        refine ⟨mono N m a ha * mono N m' b hb,
          Submodule.mul_mem_mul (mono_mem N m a ha) (mono_mem N m' b hb), ?_⟩
        show MvPolynomial.monomial m a * MvPolynomial.monomial m' b = _
        rw [MvPolynomial.monomial_mul]
      · rintro x y ⟨q₁, h₁, e₁⟩ ⟨q₂, h₂, e₂⟩
        refine ⟨q₁ + q₂, add_mem h₁ h₂, ?_⟩
        rw [map_add (f := _), ← e₁, ← e₂]
        rfl
    have hpq : p = q := by
      apply Subtype.ext
      rw [hqv]
      exact congrArg Subtype.val (eq_mono N hp)
    rw [hpq]
    exact hq
  · rw [Submodule.mul_le]
    intro a ha b hb
    have hab : AddMonoidAlgebra.coeff a.1 m * AddMonoidAlgebra.coeff b.1 m' ∈ lat N (m + m') := by
      rw [lat_add]
      exact Submodule.mul_mem_mul (a.2 m) (b.2 m')
    have h : a * b = mono N (m + m') _ hab := by
      apply Subtype.ext
      show a.1 * b.1 = MvPolynomial.monomial (m + m') _
      rw [← MvPolynomial.monomial_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val (eq_mono N ha)) (congrArg Subtype.val (eq_mono N hb))
    rw [h]
    exact mono_mem N (m + m') _ hab

end

theorem UpperTheory.V.Alg.M.std_holds :
    ∀ (B A : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A] (k : ℕ)
      (N : Fin k → Submodule B A), (∀ i, (N i).FG) → Std (reesGr N) := by
  intro B A _ _ hB _ _ k N hN
  have hdeg : ∀ d : Deg k, 0 ≤ d → ∃ m : Fin k →₀ ℕ, toDeg m = d := by
    intro d hd
    refine ⟨Finsupp.equivFunOnFinite.symm (fun j => (d j).toNat), ?_⟩
    funext j
    simp [toDeg, Int.toNat_of_nonneg (hd j)]
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro d hd
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    apply Subtype.ext
    ext m
    have hnn : 0 ≤ toDeg m := fun j => by simp [toDeg]
    have hm : toDeg m ≠ d := fun h => hd (h ▸ hnn)
    simpa using hp m hm
  · have h0 : (0 : Deg k) = toDeg 0 := by
      funext j
      simp [toDeg]
    rw [h0, gr_eq_range]
    ext p
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      have hf' := hf
      rw [lat_zero, Submodule.mem_one] at hf'
      obtain ⟨b, hb⟩ := hf'
      refine ⟨b, Subtype.ext ?_⟩
      show algebraMap B (MvPolynomial (Fin k) A) b = MvPolynomial.monomial 0 f
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply, hb]
    · rintro ⟨b, rfl⟩
      have hb : algebraMap B A b ∈ lat N 0 := by
        rw [lat_zero]
        exact Submodule.algebraMap_mem b
      refine ⟨⟨algebraMap B A b, hb⟩, Subtype.ext ?_⟩
      show MvPolynomial.monomial 0 (algebraMap B A b) = algebraMap B (MvPolynomial (Fin k) A) b
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply]
  · intro i
    rw [e_eq, gr_eq_range, LinearMap.range_eq_map]
    refine Submodule.FG.map _ ((Submodule.fg_top _).2 ?_)
    rw [lat_single]
    exact hN i
  · intro d i hd
    obtain ⟨m, rfl⟩ := hdeg d hd
    rw [e_eq, ← toDeg_add, gr_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GradedQuotientIsomorphism
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.graded_quotient_isomorphism {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (F G : GMod B R k) (f : F.M →ₗ[R] G.M) (hf : Function.Surjective f)
    (hg : ∀ m, G.gr m = (F.gr m).map (f.restrictScalars B)) (N : Submodule R F.M)
    (hN : N = LinearMap.ker f) : Nonempty (GIso G (F.quo N)) := by
  subst hN
  refine ⟨⟨(f.quotKerEquivOfSurjective hf).symm, fun m => ?_⟩⟩
  rw [hg m, ← Submodule.map_comp]
  show _ = (F.gr m).map ((LinearMap.ker f).mkQ.restrictScalars B)
  congr 1
  ext x
  exact (f.quotKerEquivOfSurjective hf).symm_apply_eq.2 rfl

theorem UpperTheory.V.Alg.M.qi_holds :
    ∀ (k : ℕ) (B R : Type) [CommRing B] [CommRing R] [Algebra B R] (𝒜 : Deg k → Submodule B R) (J : Ideal R)
      (us : List (Deg k × R)), Nonempty (GIso (((GMod.self 𝒜).quo J).quots us) ((GMod.self 𝒜).quo (J ⊔ secs us))) := by
  intro k B R _ _ _ 𝒜 J us
  let q : (GMod.self 𝒜).M →ₗ[R] ((GMod.self 𝒜).quo J).M := Submodule.mkQ J
  refine UpperTheory.V.Alg.M.graded_quotient_isomorphism (GMod.self 𝒜) _ ((GMod.quotsMk us ((GMod.self 𝒜).quo J)).comp q)
    ((GMod.quotsMk_surjective us _).comp (Submodule.mkQ_surjective J)) (fun m => ?_) _ ?_
  · rw [GMod.quots_gr]
    exact (Submodule.map_comp (q.restrictScalars B)
      ((GMod.quotsMk us ((GMod.self 𝒜).quo J)).restrictScalars B) ((GMod.self 𝒜).gr m)).symm
  · rw [LinearMap.ker_comp, GMod.ker_quotsMk]
    have h2 : (secs us • (⊤ : Submodule R (R ⧸ J))) =
        (secs us • (⊤ : Submodule R R)).map (Submodule.mkQ J) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    have h3 : J ⊔ secs us = (secs us • (⊤ : Submodule R (R ⧸ J))).comap (Submodule.mkQ J) := by
      rw [h2, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.hom_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    Q.ideal.IsHomogeneous 𝒜 ∧ (ideal2 Q).IsHomogeneous 𝒜 ∧ ideal2 Q ≤ Q.ideal := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q
  refine ⟨?_, ?_, ?_⟩
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, sq_mem_neg 𝒜 (Q.hF i)⟩, ⟨_, Q.hG i⟩, ⟨_, sq_mem_pos 𝒜 (Q.hE i)⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.span_le.2 ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IntHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.KillHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_comp {B ι M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    {G H : ι → Submodule B M} (hle : ∀ i, G i ≤ H i) (hind : iSupIndep H) (i : ι) {x : M}
    (hx : x ∈ H i) (hx' : x ∈ ⨆ j, G j) : x ∈ G i := by
  classical
  have h2 : (⨆ j, G j) ≤ G i ⊔ ⨆ (j) (_ : j ≠ i), G j := iSup_le fun j => by
    by_cases h : j = i
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j h le_rfl)
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 (h2 hx')
  have h2 : y ∈ ⨆ (j) (_ : j ≠ i), H j := (iSup₂_mono fun j _ => hle j) hy
  have h3 : y ∈ H i := by
    have := (H i).sub_mem hx (hle i hg)
    simpa using this
  have h4 : y = 0 := by
    have := (hind i).le_bot ⟨h3, h2⟩
    simpa using this
  rw [h4, add_zero]
  exact hg

theorem UpperTheory.V.Alg.M.kill_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ (J J' : Ideal X.B) (n : ℕ),
      (J.map (algebraMap X.B X.R) * Irr X.𝒜) ^ n ≤ F.Ann ⊔ J'.map (algebraMap X.B X.R) →
      ∀ᶠ d in atTop, J ^ n • F.gr d ≤ J' • F.gr d := by
  intro k X F hF J J' n hn
  have key1 : ∀ a ∈ J'.map (algebraMap X.B X.R), ∀ z : F.M,
      a • z ∈ J' • (⊤ : Submodule X.B F.M) := by
    intro a ha
    refine Submodule.span_induction
      (p := fun a _ => ∀ z : F.M, a • z ∈ J' • (⊤ : Submodule X.B F.M)) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩ z
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hb trivial
    · intro z
      rw [zero_smul]; exact zero_mem _
    · intro a b _ _ ha hb z
      rw [add_smul]; exact add_mem (ha z) (hb z)
    · intro r a _ ha z
      rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _
  have key : ∀ a ∈ F.Ann ⊔ J'.map (algebraMap X.B X.R), ∀ z : F.M,
      a • z ∈ J' • (⊤ : Submodule X.B F.M) := by
    intro a ha z
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul, Module.mem_annihilator.1 hu z, zero_add]
    exact key1 w hw z
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top n] with m hm
  refine Submodule.smul_le.2 fun b hb y hy => ?_
  refine kill_comp (G := fun d => J' • F.gr d) (H := F.gr) (fun _ => Submodule.smul_le_right)
    hF.internal.submodule_iSupIndep m (Submodule.smul_mem _ _ hy) ?_
  rw [← Submodule.smul_iSup, hF.internal.submodule_iSup_eq_top]
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    have h1 : algebraMap X.B X.R b * a ∈ F.Ann ⊔ J'.map (algebraMap X.B X.R) := by
      apply hn
      rw [mul_pow, ← Ideal.map_pow]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hb) ha
    have h2 := key _ h1 z
    rwa [mul_smul, algebraMap_smul] at h2
  · intro x y hx hy
    rw [smul_add]; exact add_mem hx hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceSupSpanSqLeAdd
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem locLen_le_of_exact {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {M N P : Type} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (h : Function.Exact f g) :
    locLen σ N ≤ locLen σ M + locLen σ P := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  exact Formalism.MainNotions.V.Pf.V2.length_le_of_exact (LocalizedModule.map (RingHom.ker σ).primeCompl f)
    (LocalizedModule.map (RingHom.ker σ).primeCompl g) (LocalizedModule.map_exact _ f g h)

theorem UpperTheory.V.Alg.M.locLen_aPiece_sup_span_sq_le_add :
    ∀ (O K A : Type) [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
      (σ : 𝒜 0 →ₐ[O] K) (J : Ideal A), J.IsHomogeneous 𝒜 → ∀ (d : ℤ) (t : A), t ∈ 𝒜 d → ∀ w : ℤ,
      locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w) ≤
        locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d)) + locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) w) := by
  intro O K A _ _ _ _ _ 𝒜 _ σ J hJ d t ht w
  have h1 : J ⊔ Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft A t) (J ⊔ Ideal.span {t ^ 2}) := by
    intro a ha
    obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    show t * (j + c * t) ∈ J ⊔ Ideal.span {t ^ 2}
    rw [show t * (j + c * t) = t * j + c * t ^ 2 by ring]
    exact Submodule.add_mem_sup (J.mul_mem_left _ hj) (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)
  have h2 : J ⊔ Ideal.span {t ^ 2} ≤ Submodule.comap (LinearMap.id : A →ₗ[A] A) (J ⊔ Ideal.span {t}) :=
    sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t two_ne_zero)) J
  let F : (A ⧸ (J ⊔ Ideal.span {t})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t ^ 2}) :=
    (Submodule.mapQ _ _ (LinearMap.mulLeft A t) h1).restrictScalars (𝒜 0)
  let G : (A ⧸ (J ⊔ Ideal.span {t ^ 2})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t}) :=
    (Submodule.mapQ _ _ (LinearMap.id : A →ₗ[A] A) h2).restrictScalars (𝒜 0)
  have hF : ∀ a : A, F (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (t * a) := fun a => rfl
  have hG : ∀ a : A, G (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  have hF' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d), F x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨t * a, ?_, (hF a).symm⟩
    have := SetLike.GradedMul.mul_mem ht (show a ∈ 𝒜 (w - d) from ha)
    rwa [add_sub_cancel] at this
  have hG' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w, G x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) w := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hG a).symm⟩
  refine locLen_le_of_exact σ (F.restrict hF') (G.restrict hG') ?_
  rintro ⟨_, a, ha, rfl⟩
  constructor
  · intro h
    have h0 : Ideal.Quotient.mk (J ⊔ Ideal.span {t}) a = 0 := congrArg Subtype.val h
    obtain ⟨j, hj, b, hb, hab⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have ha' : a ∈ 𝒜 w := ha
    have e1 : ((DirectSum.decompose 𝒜 (t * c)) (d + (w - d)) : A) = t * DirectSum.decompose 𝒜 c (w - d) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ht
    rw [add_sub_cancel] at e1
    have e2 : a = (DirectSum.decompose 𝒜 j w : A) + t * DirectSum.decompose 𝒜 c (w - d) := by
      rw [← e1, ← DirectSum.decompose_of_mem_same 𝒜 ha', ← hab, DirectSum.decompose_add, mul_comm c t]
      rfl
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒜 c (w - d) : A),
      ⟨_, (DirectSum.decompose 𝒜 c (w - d)).2, rfl⟩⟩, Subtype.ext ?_⟩
    show Ideal.Quotient.mk _ (t * (DirectSum.decompose 𝒜 c (w - d) : A)) = Ideal.Quotient.mk _ a
    rw [eq_comm, Ideal.Quotient.eq, e2, add_sub_cancel_right]
    exact Submodule.mem_sup_left (hJ w hj)
  · rintro ⟨⟨_, c, hc, rfl⟩, h⟩
    rw [← h]
    apply Subtype.ext
    show Ideal.Quotient.mk (J ⊔ Ideal.span {t}) (t * c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Submodule.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
end

