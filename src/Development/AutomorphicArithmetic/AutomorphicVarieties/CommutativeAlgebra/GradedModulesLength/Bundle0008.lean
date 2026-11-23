module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocalizedLengthLeOfSurjective
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem localized_length_le_of_surjective {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {L M N : Type} [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (φ : L →ₗ[B] M) (ψ : L →ₗ[B] N) (hφ : Function.Surjective φ)
    (h : ∀ x, ψ x = 0 → ∃ t : B, σ t ≠ 0 ∧ t • φ x = 0) : locLen σ M ≤ locLen σ N := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  unfold locLen
  set S := (RingHom.ker σ).primeCompl
  have hs : Function.Surjective (LocalizedModule.map S φ) := LocalizedModule.map_surjective S φ hφ
  have hk : LinearMap.ker (LocalizedModule.map S ψ) ≤ LinearMap.ker (LocalizedModule.map S φ) := by
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h x s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hy ⊢
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy ⊢
      obtain ⟨u, hu⟩ := hy
      have h1 : ψ ((u : B) • x) = 0 := by simpa [Submonoid.smul_def] using hu
      obtain ⟨t, ht, h2⟩ := h _ h1
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      simpa [Submonoid.smul_def, mul_smul] using h2
  have hs2 : Function.Surjective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S φ) hk) := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hs2).trans ?_
  exact Module.length_le_of_injective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S ψ) le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private def u4w (μ : Fin 3 →₀ ℕ) : ℤ := 2 * ((μ 1 : ℤ) - μ 0 - μ 2)

private theorem weight_submodule_mul_le (i j : ℤ) : oz 𝒜 i * oz 𝒜 j ≤ oz 𝒜 (i + j) :=
  Submodule.mul_le.2 fun _ ha _ hb => (mem_oz 𝒜).2 (SetLike.GradedMul.mul_mem ((mem_oz 𝒜).1 ha) ((mem_oz 𝒜).1 hb))

private theorem weight_submodule_pow_le {P : Submodule (𝒜 0) A} {i : ℤ} (h : P ≤ oz 𝒜 i) (n : ℕ) : P ^ n ≤ oz 𝒜 (n * i) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0)
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih h).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
    congr 1; push_cast; ring

private theorem lattice_le_weight_submodule {F : A} (hF : F ∈ 𝒜 (-1)) (μ : Fin 3 →₀ ℕ) : lat (mN 𝒜 F) μ ≤ oz 𝒜 (u4w μ) := by
  have h2 : mN 𝒜 F 2 ≤ oz 𝒜 (-2) := by
    show Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ _
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (sq_mem_neg 𝒜 hF)) ?_
    exact (mul_le_mul' (weight_submodule_mul_le 𝒜 _ _) le_rfl).trans (weight_submodule_mul_le 𝒜 _ _)
  have h0 : mN 𝒜 F 0 ≤ oz 𝒜 (-2) := le_rfl
  have h1 : mN 𝒜 F 1 ≤ oz 𝒜 2 := le_rfl
  rw [lat, Fin.prod_univ_three]
  refine (mul_le_mul' ((mul_le_mul' (weight_submodule_pow_le 𝒜 h0 _) (weight_submodule_pow_le 𝒜 h1 _)).trans (weight_submodule_mul_le 𝒜 _ _))
    (weight_submodule_pow_le 𝒜 h2 _)).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
  congr 1; unfold u4w; ring

private theorem power_mul_mem_lattice (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (μ : Fin 3 →₀ ℕ) {a : A} (ha : a ∈ 𝒜 (u4w μ)) :
    ∃ n : ℕ, (f * g) ^ n * a ∈ lat (mN 𝒜 F) μ := by
  have hl : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) ≤ lat (mN 𝒜 F) μ := by
    have h2 : oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ mN 𝒜 F 2 := le_sup_right
    rw [lat, Fin.prod_univ_three]
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl (pow_le_pow_left' h2 (μ 2)))
    show _ = oz 𝒜 (-2) ^ μ 0 * oz 𝒜 2 ^ μ 1 * _
    ring
  have hfg : ∀ n : ℕ, (f * g) ^ n ∈ oz 𝒜 (-2) ^ n * oz 𝒜 2 ^ n := fun n => by
    rw [mul_pow]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow (oz 𝒜 (-2)) hf n) (Submodule.pow_mem_pow (oz 𝒜 2) hg n)
  rcases le_total (μ 0 + 2 * μ 2) (μ 1 + μ 2) with h | h
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 0 + 2 * μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 2 ^ c := by
      rw [← (hp c).2, mem_oz]
      have : u4w μ = 2 * c := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 2) _ c, ← mul_assoc]
    exact Submodule.mul_mem_mul (hfg _) ha'
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 1 + μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 (-2) ^ c := by
      rw [← (hp c).1, mem_oz]
      have : u4w μ = -(2 * c) := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 (-2)) _ c, mul_right_comm]
    exact Submodule.mul_mem_mul (hfg _) ha'

private def u4K (F : A) (b : 𝒜 0) (J : Ideal (rees (mN 𝒜 F))) (μ : Fin 3 →₀ ℕ) : AddSubmonoid A where
  carrier := {a | ∃ n : ℕ, ∃ p ∈ J, p.1 = MvPolynomial.monomial μ ((b : A) ^ n * a)}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro a a' ⟨n, p, hp, e⟩ ⟨n', p', hp', e'⟩
    refine ⟨n + n', b ^ n' • p + b ^ n • p',
      J.add_mem (Submodule.smul_of_tower_mem _ _ hp) (Submodule.smul_of_tower_mem _ _ hp'), ?_⟩
    show b ^ n' • p.1 + b ^ n • p'.1 = _
    rw [e, e', MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, ← map_add (f := _)]
    congr 1
    show ((b ^ n' : 𝒜 0) : A) * _ + ((b ^ n : 𝒜 0) : A) * _ = _
    simp only [SetLike.GradeZero.coe_pow]
    ring

private theorem generated_component_mem (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (b : 𝒜 0) (hb : (b : A) = f * g)
    (J : Ideal (rees (mN 𝒜 F))) (μ ν : Fin 3 →₀ ℕ) (hν : ν ≤ μ) {y : A} (hy : y ∈ 𝒜 (u4w ν))
    (q : rees (mN 𝒜 F)) (hq : q ∈ J) (e : q.1 = MvPolynomial.monomial ν y) (c : A) :
    (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 F b J μ := by
  obtain ⟨ν', rfl⟩ := exists_add_of_le hν
  have hw : u4w (ν + ν') = u4w ν' + u4w ν := by
    simp only [u4w, Finsupp.add_apply]; push_cast; ring
  rw [hw, DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hy]
  obtain ⟨n, hn⟩ := power_mul_mem_lattice 𝒜 hp F hf hg ν' (DirectSum.decompose 𝒜 c (u4w ν')).2
  refine ⟨n, mono _ ν' _ hn * q, J.mul_mem_left _ hq, ?_⟩
  show MvPolynomial.monomial ν' _ * q.1 = _
  rw [e, MvPolynomial.monomial_mul, add_comm, hb, mul_assoc]

end

theorem UpperTheory.V.Alg.M.locLen_mQ_gr_le_locLen_aPiece :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ J : Ideal (mR Q), secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
    ∀ σ : 𝒜 0 →ₐ[O] K, ¬ idD 𝒜 ≤ RingHom.ker σ → ∀ d : Deg 3, 1 ≤ d →
      locLen σ ((mQ Q J).gr d) ≤ locLen σ (aPiece 𝒜 (ideal2 Q) (2 * (d 1 - d 0 - d 2))) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q J hJ hZ σ hσ d hd
  have hp := oz_two_mul_eq_pow O A 𝒜 x hW
  obtain ⟨b, ⟨f, hf, g, hg, hb⟩, hbσ⟩ : ∃ b : 𝒜 0, (∃ f ∈ 𝒜 (-2), ∃ g ∈ 𝒜 2, (b : A) = f * g) ∧ σ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hσ (Ideal.span_le.2 fun b ⟨f, hf, g, hg, hb⟩ => hcon b ⟨f, hf, g, hg, hb⟩)
  obtain ⟨μ, rfl⟩ : ∃ μ : Fin 3 →₀ ℕ, toDeg μ = d :=
    ⟨Finsupp.equivFunOnFinite.symm fun i => (d i).toNat, funext fun i => by
      have : (1 : ℤ) ≤ d i := hd i
      simp only [toDeg, Finsupp.equivFunOnFinite_symm_apply_apply]
      omega⟩
  have hμ : ∀ i, Finsupp.single i 1 ≤ μ := fun i => by
    have : (1 : ℤ) ≤ (μ i : ℤ) := hd i
    rw [Finsupp.single_le_iff]; omega
  have hsec : ∀ (i : Fin 3) (y : A) (hy : y ∈ mN 𝒜 (Q.F (Fin.last r)) i), (e i, sec _ i y hy) ∈ ts Q →
      ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := fun i y hy hm =>
    generated_component_mem 𝒜 hp _ hf hg b hb J μ _ (hμ i)
      (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) _ (by rw [lat_single]; exact hy)) _ (hJ (Ideal.subset_span ⟨_, hm⟩)) rfl
  have hI : ∀ y ∈ ideal2 Q, ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · induction i using Fin.lastCases with
        | last =>
          exact hsec 2 _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
        | cast i =>
          exact hsec 0 _ (sq_mem_neg 𝒜 (Q.hF _)) (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩))
      · exact hsec 0 _ (Q.hG i) (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (sq_mem_pos 𝒜 (Q.hE i)) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (Q.hE' i) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩))))
      · exact generated_component_mem 𝒜 hp _ hf hg b hb J μ 0 bot_le (Q.hZ i).1 _ (hZ i) rfl
    | zero => intro c; simp
    | add y z _ _ h1 h2 =>
      intro c
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem (h1 c) (h2 c)
    | smul a y _ h1 =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact h1 _
  let φ0 : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] mR Q :=
    { toFun := fun h => mono _ μ h.1 h.2
      map_add' := fun h h' => Subtype.ext (map_add (MvPolynomial.monomial μ) h.1 h'.1)
      map_smul' := fun c h => Subtype.ext (MvPolynomial.smul_monomial c).symm }
  let φ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] (mQ Q J).gr (toDeg μ) :=
    LinearMap.codRestrict _ ((J.mkQ.restrictScalars (𝒜 0)) ∘ₗ φ0) fun h => ⟨φ0 h, mono_mem _ μ h.1 h.2, rfl⟩
  let ψ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] aPiece 𝒜 (ideal2 Q) (u4w μ) :=
    LinearMap.codRestrict _ ((Ideal.Quotient.mkₐ (𝒜 0) (ideal2 Q)).toLinearMap ∘ₗ Submodule.subtype _) fun h =>
      ⟨h.1, lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2, rfl⟩
  refine localized_length_le_of_surjective σ φ ψ ?_ ?_
  · rintro ⟨_, p, hp', rfl⟩
    refine ⟨⟨AddMonoidAlgebra.coeff p.1 μ, p.2 μ⟩, Subtype.ext ?_⟩
    show J.mkQ (mono _ μ _ (p.2 μ)) = J.mkQ p
    congr 1
    apply Subtype.ext
    ext ν
    show AddMonoidAlgebra.coeff (MvPolynomial.monomial μ _) ν = _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact (hp' ν fun h' => h (toDeg_injective h').symm).symm
  · intro h h0
    have h1 : h.1 ∈ ideal2 Q := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val h0)
    have h2 := hI _ h1 1
    rw [one_mul, DirectSum.decompose_of_mem_same 𝒜 (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2)] at h2
    obtain ⟨n, p, hpJ, e⟩ := h2
    refine ⟨b ^ n, by rw [map_pow]; exact pow_ne_zero _ hbσ, ?_⟩
    rw [← map_smul]
    apply Subtype.ext
    show J.mkQ (φ0 (b ^ n • h)) = 0
    have : φ0 (b ^ n • h) = p := by
      apply Subtype.ext
      rw [e]
      show MvPolynomial.monomial μ (((b ^ n : 𝒜 0) : A) * h.1) = _
      rw [SetLike.GradeZero.coe_pow]
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero _).2 hpJ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SliceHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem exists_ptDer_eq_degree_smul_of_graded {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [Field K] [Algebra O K]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (ξ : A →ₐ[O] K) :
    ∃ E ∈ PtDer ξ K, ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a := by
  classical
  let L : (DirectSum ℤ fun i => 𝒜 i) →ₗ[O] K :=
    DirectSum.toModule O ℤ K (fun i => ((i : ℤ) : K) • (ξ.toLinearMap ∘ₗ (𝒜 i).subtype))
  let E : A →ₗ[O] K := L ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hE : ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a := by
    intro j a ha
    show L (DirectSum.decompose 𝒜 a) = _
    rw [DirectSum.decompose_of_mem 𝒜 ha, ← DirectSum.lof_eq_of O, DirectSum.toModule_lof]
    simp [smul_eq_mul]
  refine ⟨E, ?_, hE⟩
  intro a b
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous b =>
      rw [hE _ _ (SetLike.GradedMul.mul_mem a.2 b.2), hE _ _ a.2, hE _ _ b.2]
      simp only [map_mul, smul_eq_mul]
      push_cast
      ring
    | add b₁ b₂ h₁ h₂ =>
      simp only [mul_add, map_add (f := _), smul_add, h₁, h₂, smul_eq_mul]
      ring
  | add a₁ a₂ h₁ h₂ =>
    simp only [add_mul, map_add (f := _), smul_add, add_smul, h₁, h₂, smul_eq_mul]
    ring

private theorem degree_derivation_vanishes_on_homogeneous_ideal {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] [Field K] [Algebra O K]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (I : Ideal A) (hI : I.IsHomogeneous 𝒜) (ξ : A →ₐ[O] K)
    (hξ : OnS I ξ) (E : A →ₗ[O] K) (hE : ∀ (j : ℤ) (a : A), a ∈ 𝒜 j → E a = (j : K) * ξ a) :
    ∀ a ∈ I, E a = 0 := by
  classical
  intro a ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hE i _ (SetLike.coe_mem _), hξ _ (hI i ha), mul_zero]

theorem UpperTheory.V.Alg.M.slice_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∀ f ∈ 𝒜 (-2), ∀ g ∈ 𝒜 2,
      {ξ : A →ₐ[O] K | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0}.Finite ∧
      ∀ h : A, (∀ ξ : A →ₐ[O] K, OnS I ξ → ξ f = 1 → ξ g ≠ 0 → ξ h = 0) →
        ∃ (n : ℕ) (c : O), c ≠ 0 ∧ c • (g ^ n * h) ∈ I ⊔ Ideal.span {f - 1} := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4 f hf g hg
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective O K)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set J : Ideal A := I ⊔ Ideal.span {f - 1} with hJ
  let s : A ⧸ J := algebraMap O (A ⧸ J) π * Ideal.Quotient.mk J g
  let C := Localization.Away s
  let φ : A →ₐ[O] C := (IsScalarTower.toAlgHom O (A ⧸ J) C).comp (Ideal.Quotient.mkₐ O J)
  have hφ : ∀ a, φ a = algebraMap (A ⧸ J) C (Ideal.Quotient.mk J a) := fun a => rfl
  have hφJ : ∀ a ∈ J, φ a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hf1 : φ f = 1 := by
    have h0 : φ (f - 1) = 0 := hφJ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_sub, map_one, sub_eq_zero] at h0
  have hs_unit : IsUnit (algebraMap (A ⧸ J) C s) := IsLocalization.Away.algebraMap_isUnit s
  have hs_eq : algebraMap (A ⧸ J) C s = algebraMap O C π * φ g := by
    rw [hφ]
    simp only [s, map_mul]
    rw [← IsScalarTower.algebraMap_apply]
  rw [hs_eq] at hs_unit
  have hπu : IsUnit (algebraMap O C π) := isUnit_of_mul_isUnit_left hs_unit
  have hgu : IsUnit (φ g) := isUnit_of_mul_isUnit_right hs_unit
  have hunits : ∀ c : O, c ≠ 0 → IsUnit (algebraMap O C c) := by
    intro c hc
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hπu.pow n)
  haveI hft : Algebra.FiniteType O C := by
    have h1 : Algebra.FiniteType O (A ⧸ I) := (ft_holds O A 𝒜 x hx).2 I h2
    have h3 : Algebra.FiniteType O (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.factorₐ O (le_sup_left : I ≤ J))
        (Ideal.Quotient.factor_surjective (le_sup_left : I ≤ J))
    exact Algebra.FiniteType.trans h3 inferInstance
  have hslice : ∀ ψ : C →ₐ[O] K, OnS I (ψ.comp φ) ∧ (ψ.comp φ) f = 1 ∧ (ψ.comp φ) g ≠ 0 := by
    intro ψ
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · rw [AlgHom.comp_apply, hφJ a (Ideal.mem_sup_left ha), map_zero]
    · rw [AlgHom.comp_apply, hf1, map_one]
    · rw [AlgHom.comp_apply]
      exact (hgu.map ψ).ne_zero
  have hder : ∀ ψ : C →ₐ[O] K, PtDer ψ K = ⊥ := by
    intro ψ
    rw [eq_bot_iff]
    intro D hD
    rw [Submodule.mem_bot]
    obtain ⟨hOn, hξf, hξg⟩ := hslice ψ
    let D' : A →ₗ[O] K := D ∘ₗ φ.toLinearMap
    have hD' : D' ∈ PtDer (ψ.comp φ) K := by
      intro a b
      show D (φ (a * b)) = ψ (φ a) • D (φ b) + ψ (φ b) • D (φ a)
      rw [map_mul]
      exact hD _ _
    obtain ⟨E, hEm, hE⟩ := exists_ptDer_eq_degree_smul_of_graded 𝒜 (ψ.comp φ)
    have hEI := degree_derivation_vanishes_on_homogeneous_ideal 𝒜 I hI (ψ.comp φ) hOn E hE
    have hD'I : ∀ a ∈ I, D' a = 0 := by
      intro a ha
      show D (φ a) = 0
      rw [hφJ a (Ideal.mem_sup_left ha), map_zero]
    have htwo : TwoSigned 𝒜 (ψ.comp φ) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h0 := h (-2) (by norm_num) f hf
        rw [hξf] at h0
        exact one_ne_zero h0
      · exact hξg (h 2 (by norm_num) g hg)
    obtain ⟨c, c', hcc, hlin⟩ := h4 (ψ.comp φ) hOn htwo D' hD' E hEm hD'I hEI
    have hD1 : D 1 = 0 := by
      have h0 := hD 1 1
      have hψ1 : ψ 1 = 1 := map_one ψ
      rw [mul_one, hψ1, one_smul] at h0
      have h5 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h0.symm
      exact add_left_cancel h5
    have hD'f : D' f = 0 := by
      show D (φ f) = 0
      rw [hf1, hD1]
    have hEf : E f = -2 := by
      rw [hE (-2) f hf, hξf]
      norm_num
    have hc' : c' = 0 := by
      have h0 := LinearMap.congr_fun hlin f
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hD'f, hEf,
        LinearMap.zero_apply, smul_zero, zero_add, smul_eq_mul] at h0
      have h6 : (-2 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h0).resolve_right h6
    have hc : c ≠ 0 := hcc.resolve_right (fun h => h hc')
    have hD0 : ∀ a, D (φ a) = 0 := by
      intro a
      have h0 := LinearMap.congr_fun hlin a
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hc', zero_smul, add_zero,
        LinearMap.zero_apply, smul_eq_mul] at h0
      exact (mul_eq_zero.mp h0).resolve_left hc
    ext z
    obtain ⟨⟨b, t, ht⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
    obtain ⟨n, rfl⟩ := ht
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    set z := IsLocalization.mk' C (Ideal.Quotient.mk J a) (⟨s ^ n, n, rfl⟩ : Submonoid.powers s) with hz
    have hspec : z * algebraMap (A ⧸ J) C (s ^ n) = φ a := by
      rw [hz, IsLocalization.mk'_spec]
      rfl
    have ht : algebraMap (A ⧸ J) C (s ^ n) = φ ((algebraMap O A π * g) ^ n) := by
      rw [hφ]
      congr 1
    have htu : IsUnit (algebraMap (A ⧸ J) C (s ^ n)) := by
      rw [map_pow, hs_eq]
      exact hs_unit.pow n
    have h0 := hD z (algebraMap (A ⧸ J) C (s ^ n))
    rw [hspec, hD0, ht, hD0, smul_zero, zero_add, ← ht] at h0
    have hne : ψ (algebraMap (A ⧸ J) C (s ^ n)) ≠ 0 := (htu.map ψ).ne_zero
    rw [smul_eq_mul] at h0
    rw [LinearMap.zero_apply]
    exact ((mul_eq_zero.mp h0.symm).resolve_left hne)
  obtain ⟨hfin, hred⟩ := et_holds O K C hunits hder
  refine ⟨?_, ?_⟩
  · have hsub : {ξ : A →ₐ[O] K | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0} ⊆
        Set.range (fun ψ : C →ₐ[O] K => ψ.comp φ) := by
      rintro ξ ⟨hOn, hξf, hξg⟩
      have hJξ : ∀ a ∈ J, ξ a = 0 := by
        have hle : J ≤ RingHom.ker ξ := by
          refine sup_le (fun a ha => hOn a ha) ?_
          rw [Ideal.span_le, Set.singleton_subset_iff]
          show ξ (f - 1) = 0
          rw [map_sub, hξf, map_one, sub_self]
        exact fun a ha => hle ha
      let ξB : (A ⧸ J) →ₐ[O] K := Ideal.Quotient.liftₐ J ξ hJξ
      have hu : ∀ y : Submonoid.powers s, IsUnit (ξB y) := by
        rintro ⟨_, n, rfl⟩
        rw [map_pow]
        refine IsUnit.pow n (isUnit_iff_ne_zero.mpr ?_)
        simp only [s, map_mul, AlgHom.commutes]
        refine mul_ne_zero ?_ ?_
        · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr hπ0
        · exact hξg
      refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers s) (S := C) hu, ?_⟩
      ext a
      show IsLocalization.liftAlgHom (M := Submonoid.powers s) (S := C) hu
        (algebraMap (A ⧸ J) C (Ideal.Quotient.mk J a)) = ξ a
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      rfl
    exact (Set.finite_range _).subset hsub
  · intro h hh
    have hz : φ h = 0 := hred (φ h) (fun ψ => by
      obtain ⟨h1, h3, h5⟩ := hslice ψ
      exact hh _ h1 h3 h5)
    rw [hφ] at hz
    obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) C _).mp hz
    refine ⟨n, π ^ n, pow_ne_zero _ hπ0, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have heq : Ideal.Quotient.mk J (π ^ n • (g ^ n * h)) = s ^ n * Ideal.Quotient.mk J h := by
      simp only [s, Algebra.smul_def, map_mul, map_pow, mul_pow]
      rw [Ideal.Quotient.mk_algebraMap]
      ring
    rw [heq]
    exact hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ValuationNonnegApplyDegreeZeroOfOnS
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.valuation_nonneg_apply_degreeZero_of_onS :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I → ∀ ξ : A →ₐ[O] K, OnS I ξ → ∀ b ∈ 𝒜 0, ξ b ≠ 0 → 0 ≤ v (ξ b) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x I hI ξ hξ b hb hne
  classical
  set M : Submodule O K := Submodule.map ξ.toLinearMap (𝒜 0) with hMdef
  have hker : ∀ f ∈ I, ξ f = 0 := hξ
  let ξ' : (A ⧸ I) →ₐ[O] K := Ideal.Quotient.liftₐ I ξ hker
  have hcomp : ξ.toLinearMap = ξ'.toLinearMap.comp (Ideal.Quotient.mkₐ O I).toLinearMap := by
    apply LinearMap.ext
    intro a
    rfl
  have hMfg : M.FG := by
    rw [hMdef, hcomp, Submodule.map_comp]
    exact Submodule.FG.map _ hI
  haveI : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hMfg
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {ξ b}) ≤ M := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin O {ξ b} := hz
    clear hz
    rw [hMdef, Submodule.mem_map]
    induction hz' using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      exact ⟨b, hb, hw.symm⟩
    | algebraMap r =>
      exact ⟨algebraMap O A r, SetLike.algebraMap_mem_graded 𝒜 r, by simp⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, add_mem hc₁ hc₂, by simp [← e₁, ← e₂]⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      have hm : c₁ * c₂ ∈ 𝒜 (0 + 0) := SetLike.mul_mem_graded hc₁ hc₂
      rw [add_zero] at hm
      exact ⟨c₁ * c₂, hm, by simp [← e₁, ← e₂]⟩
  haveI : IsNoetherian O (Subalgebra.toSubmodule (Algebra.adjoin O {ξ b})) := isNoetherian_of_le hle
  have hint : IsIntegral O (ξ b) :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin O {ξ b}) inferInstance (ξ b)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  exact int_holds O K v hv (ξ b) hint hne
end

