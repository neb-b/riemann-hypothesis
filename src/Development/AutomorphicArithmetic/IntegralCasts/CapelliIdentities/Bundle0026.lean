module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericGradient
section
noncomputable def UpperTheory.Reformulated.B.Qf34.genericGradient :
    {n : ℕ} →
      (J : Ideal (MvPolynomial (Fin n) ℂ)) → MvPolynomial (Fin n) ℂ → Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
    fun {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (l : Fin n) ↦
      (Algebra.algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) :
          MvPolynomial (Fin n) ℂ ⧸ J → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        ((Ideal.Quotient.mk J : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ ⧸ J)
          ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) f))

noncomputable def UpperTheory.Reformulated.B.Qf34.Statement :
    Prop :=
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι] (f : ι → MvPolynomial (Fin n) ℂ),
      (∀ (i : ι), f i ∈ J) →
        Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) =
            Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
              (UpperTheory.Reformulated.B.Qf34.genericGradient J '' (↑J : Set (MvPolynomial (Fin n) ℂ))) →
          ∃ s ∉ J, ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.taylor {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    {n : ℕ} (φ ψ : MvPolynomial (Fin n) k →ₐ[k] B)
    (h : ∀ p q, (φ p - ψ p) * (φ q - ψ q) = 0) (p : MvPolynomial (Fin n) k) :
    φ p - ψ p = ∑ l, φ (pderiv l p) * (φ (X l) - ψ (X l)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    ring
  | mul_X p i hp =>
    have e : ∀ l, φ (pderiv l (p * X i)) * (φ (X l) - ψ (X l)) =
        φ (X i) * (φ (pderiv l p) * (φ (X l) - ψ (X l))) +
          (if l = i then φ p * (φ (X i) - ψ (X i)) else 0) := by
      intro l
      rw [pderiv_mul, map_add (f := _), map_mul, map_mul]
      split_ifs with hl
      · subst hl
        rw [pderiv_X_self, map_one]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hl), map_zero]
        ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    linear_combination - h p (X i)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.sq_zero_case {k B K ι : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [CommRing K] [Algebra k K] [Fintype ι] {n : ℕ}
    (π : B →ₐ[k] K) (σ : K →ₐ[k] B) (hσ : ∀ x, π (σ x) = x)
    (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0)
    (φ : MvPolynomial (Fin n) k →ₐ[k] B) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p = ∑ i, σ (c i) * φ (f i) := by
  have hd : ∀ q, π (φ q - (σ.comp (π.comp φ)) q) = 0 := by
    intro q
    simp [hσ]
  have ht := UpperTheory.Reformulated.B.Qf34.taylor φ (σ.comp (π.comp φ)) fun p q => hsq _ _ (hd p) (hd q)
  have ht' : ∀ q, π (φ q) = 0 →
      φ q = ∑ l, φ (pderiv l q) * (φ (X l) - (σ.comp (π.comp φ)) (X l)) := by
    intro q hq
    rw [← ht q]
    simp [hq]
  rw [ht' p hp, Finset.sum_congr rfl fun i _ => congrArg (σ (c i) * ·) (ht' _ (hf i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← sub_eq_zero, ← sub_mul]
  refine hsq _ _ ?_ (hd _)
  simp [hσ, hc]

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.mem_sup_sq {k A K ι : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing K] [Algebra k K] [Algebra.FormallySmooth k K] [Fintype ι] {n : ℕ}
    (π : A →ₐ[k] K) (hπ : Function.Surjective π)
    (φ : MvPolynomial (Fin n) k →ₐ[k] A) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p ∈ Ideal.span (Set.range fun i => φ (f i)) ⊔ RingHom.ker π * RingHom.ker π := by
  set m : Ideal A := RingHom.ker π with hm
  let π' : (A ⧸ m * m) →ₐ[k] K := Ideal.Quotient.liftₐ (m * m) π fun a ha => Ideal.mul_le_left ha
  have hπ' : ∀ a, π' (Ideal.Quotient.mk _ a) = π a := fun a => rfl
  have hs : Function.Surjective π' := fun x => by
    obtain ⟨a, rfl⟩ := hπ x
    exact ⟨_, hπ' a⟩
  have hsq : ∀ a b, π' a = 0 → π' b = 0 → a * b = 0 := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_mul ha hb
  have hn : IsNilpotent (RingHom.ker (π' : (A ⧸ m * m) →+* K)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    exact hsq a b ha hb
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k K) π' hs hn
  have hσ : ∀ x, π' (σ x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k K) π' hs hn
  have key := UpperTheory.Reformulated.B.Qf34.sq_zero_case π' σ hσ hsq ((Ideal.Quotient.mkₐ k (m * m)).comp φ)
    p f c hp hf hc
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := m * m) (σ (c i))
  have h2 : φ p - ∑ i, a i * φ (f i) ∈ m * m := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq, map_sum]
    simpa [← ha] using key
  rw [← add_sub_cancel (∑ i, a i * φ (f i)) (φ p)]
  refine Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ => ?_) h2
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem UpperTheory.Reformulated.B.Qf34.proof :
    UpperTheory.Reformulated.B.Qf34.Statement := by
  intro n J _ ι _ f hf hspan
  let R := MvPolynomial (Fin n) ℂ
  let K := FractionRing (R ⧸ J)
  let A := Localization.AtPrime J
  let g : R →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ (R ⧸ J) K).comp (Ideal.Quotient.mkₐ ℂ J)
  have hg : ∀ r, g r = algebraMap (R ⧸ J) K (Ideal.Quotient.mk J r) := fun r => rfl
  have hg0 : ∀ r, g r = 0 ↔ r ∈ J := fun r => by
    rw [hg, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ J) K), Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : J.primeCompl, IsUnit (g y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 ((hg0 _).mp h)
  let π : A →ₐ[ℂ] K := IsLocalization.liftAlgHom (M := J.primeCompl) hu
  let φ : R →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ R A
  have hπφ : ∀ r, π (φ r) = g r := fun r => IsLocalization.lift_eq hu r
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (R ⧸ J) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : b ∈ J.primeCompl := fun h =>
      nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    refine ⟨IsLocalization.mk' A a ⟨b, hb'⟩, ?_⟩
    rw [← hg, ← hg, eq_div_iff (hu ⟨b, hb'⟩).ne_zero, ← hπφ, ← hπφ, ← map_mul]
    exact congrArg π (IsLocalization.mk'_spec A a ⟨b, hb'⟩)
  haveI : Algebra.EssFiniteType (R ⧸ J) K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors (R ⧸ J))
  haveI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ (R ⧸ J) K
  haveI : Algebra.FormallySmooth ℂ K := Algebra.FormallySmooth.of_perfectField
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal (π : A →+* K) hπ
  have hN : IsLocalRing.maximalIdeal A ≤ (Ideal.span (Set.range f)).map (algebraMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    conv_lhs => rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hmem : UpperTheory.Reformulated.B.Qf34.genericGradient J p ∈
        Submodule.span K (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have := UpperTheory.Reformulated.B.Qf34.mem_sup_sq π hπ φ p f c (by rw [hπφ, hg0]; exact hp)
      (fun i => by rw [hπφ, hg0]; exact hf i) (fun l => by
        have h := congrFun hc l
        rw [Finset.sum_apply] at h
        simp only [hπφ]
        exact h.symm)
    rw [hker] at this
    rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, smul_eq_mul]
    exact this
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  have hs : ∀ p ∈ J, ∃ s ∈ J.primeCompl, s * p ∈ Ideal.span (Set.range f) := by
    intro p hp
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff J.primeCompl A]
    apply hN
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hp
  choose! s hs hs' using hs
  have htJ : ∀ p ∈ t, p ∈ J := fun p hp => ht ▸ Ideal.subset_span hp
  refine ⟨∏ p ∈ t, s p, Submonoid.prod_mem J.primeCompl fun p hp => hs p (htJ p hp), ?_⟩
  intro p hp
  rw [← ht] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem s hx
    rw [hu, mul_comm (s x), mul_assoc]
    exact Ideal.mul_mem_left _ _ (hs' x (htJ x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasStrictFDerivAtEval
section
noncomputable def UpperTheory.Reformulated.B.Qi29.polyDeriv :
    {n : ℕ} → MvPolynomial (Fin n) ℂ → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) ↦
      ∑ l : Fin n,
        (MvPolynomial.eval fun (i : Fin n) ↦ x.ofLp i : MvPolynomial (Fin n) ℂ → ℂ)
            ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) p) •
          EuclideanSpace.proj l

theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by
  intro n p x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0 := by
      simp [UpperTheory.Reformulated.B.Qi29.polyDeriv]
    rw [h]
    simp only [MvPolynomial.eval_C]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x
        = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add (f := _), add_smul, Finset.sum_add_distrib]
    rw [h]
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i)
        (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x
        = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) •
            (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul,
        MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [MvPolynomial.pderiv_X_of_ne hb.symm]
      · simp
    rw [h]
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hi
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HcAvg
section
theorem UpperTheory.Reformulated.B.Qe18.hc_avg :
    ∀ {k D M : Type} [inst : Field k] [inst_1 : Group D]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module k M] (ρ : Representation k D M) (N : Subgroup D),
    (↑N.index : k) ≠ (0 : k) →
      ∀ (z : D → M),
        (∀ (g h : D), z (g * h) = z g + ((ρ : D → M →ₗ[k] M) g : M → M) (z h)) →
          (∀ s ∈ N, z s = (0 : M)) → ∃ (m : M), ∀ (g : D), z g = ((ρ : D → M →ₗ[k] M) g : M → M) m - m := by
  intro k D M _ _ _ _ ρ N hN z hz h0
  have hidx : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : Fintype (D ⧸ N) := Subgroup.fintypeOfIndexNeZero hidx
  have hcos : ∀ a b : D, (a : D ⧸ N) = (b : D ⧸ N) → z a = z b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have h1 := hz a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  have hcard : Fintype.card (D ⧸ N) = N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have key : ∀ g : D, ∑ q : D ⧸ N, z q.out
      = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
    intro g
    have h1 : ∑ q : D ⧸ N, z (g • q).out = ∑ q : D ⧸ N, z q.out :=
      Equiv.sum_comp (MulAction.toPerm g) (fun q : D ⧸ N => z q.out)
    have h2 : ∀ q : D ⧸ N, z (g • q).out = z g + ρ g (z q.out) := by
      intro q
      rw [← hz]
      apply hcos
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.coe_smul_out]
    calc ∑ q : D ⧸ N, z q.out = ∑ q : D ⧸ N, z (g • q).out := h1.symm
      _ = ∑ q : D ⧸ N, (z g + ρ g (z q.out)) := Finset.sum_congr rfl fun q _ => h2 q
      _ = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  refine ⟨-((N.index : k)⁻¹ • ∑ q : D ⧸ N, z q.out), fun g => ?_⟩
  have h3 : (N.index : k) • z g
      = (∑ q : D ⧸ N, z q.out) - ρ g (∑ q : D ⧸ N, z q.out) :=
    eq_sub_of_add_eq (key g).symm
  calc z g = (N.index : k)⁻¹ • ((N.index : k) • z g) := (inv_smul_smul₀ hN _).symm
    _ = _ := by
      rw [h3, smul_sub, map_neg, map_smul]
      abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeGelfandPair
section
noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke :
    {G : Type} → [inst : Group G] → [TopologicalSpace G] → Subgroup G → (G → ℂ) → Prop :=
    fun {G : Type} [Group G] [TopologicalSpace G] (K' : Subgroup G) (f : G → ℂ) ↦
      HasCompactSupport f ∧ ∀ k ∈ K', ∀ (x : G), f (k * x) = f x ∧ f (x * k) = f x

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a b : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → b ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * (a * b)) = u x := by
  intro H _ u a b ha hb x
  rw [← mul_assoc, hb, ha]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) (a : H), u (a * (1 : H)) = u a := by
  intro H _ u a
  rw [mul_one]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * a⁻¹) = u x := by
  intro H _ u a ha x
  have h := ha (x * a⁻¹)
  rw [inv_mul_cancel_right] at h
  exact h.symm

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.rStab :
    {H : Type} → [inst : Group H] → (H → ℂ) → Subgroup H :=
    fun {H : Type} [inst : Group H] (u : H → ℂ) ↦
      { carrier := {k : H | ∀ (x : H), u (x * k) = u x}, mul_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 H inst u,
        one_mem' := UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 u, inv_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 H inst u : Subgroup H }

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.hint :
    {H : Type} → [inst : Group H] → Subgroup H → (H → ℂ) → ℂ :=
    fun {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) ↦
      (↑((UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K).relIndex K) : ℂ)⁻¹ * ∑ᶠ (q : H ⧸ UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K), u (Quotient.out q)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.cv :
    {G : Type} → [inst : Group G] → Subgroup G → (G → ℂ) → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) (y : G) ↦ UpperTheory.Reformulated.B.HeckeGelfandPair.hint K fun (z : G) ↦ f z * g (z⁻¹ * y)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand :
    Prop :=
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (τ : G → G),
            (∀ (x y : G), τ (x * y) = τ y * τ x) →
              (∀ (x : G), τ (τ x) = x) →
                (∀ k ∈ K, τ k ∈ K) →
                  (∀ (x : G), ∃ k ∈ K, ∃ k' ∈ K, τ x = k * x * k') →
                    ∀ (f g : G → ℂ),
                      UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K f →
                        UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K g → UpperTheory.Reformulated.B.HeckeGelfandPair.cv K f g = UpperTheory.Reformulated.B.HeckeGelfandPair.cv K g f

private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    UpperTheory.Reformulated.B.HeckeGelfandPair.hint K u = ∑ᶠ q : H ⧸ K, u (Quotient.out q) := by
  have h : UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K = K := inf_eq_right.mpr (fun k hk => hu k hk)
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.hint
  rw [h]
  simp

private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr {H : Type} [Group H] (K : Subgroup H) (u v : H → ℂ)
    (hv : ∀ k ∈ K, ∀ x, v (x * k) = v x) (e : H ≃ H)
    (he : ∀ a b, a⁻¹ * b ∈ K ↔ (e a)⁻¹ * e b ∈ K) (huv : ∀ z, v (e z) = u z) :
    ∑ᶠ q : H ⧸ K, u (Quotient.out q) = ∑ᶠ q : H ⧸ K, v (Quotient.out q) := by
  let E : H ⧸ K ≃ H ⧸ K := Quotient.congr e (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    exact he a b)
  rw [← finsum_comp_equiv E (f := fun q : H ⧸ K => v (Quotient.out q))]
  refine finsum_congr (fun q => ?_)
  have h1 : E q = (QuotientGroup.mk (e q.out) : H ⧸ K) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (e q.out)
  rw [h1, hk, hv _ k.2, huv]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand :
    UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand := by
  intro G _ _ _ K _ _ τ hmul hinv hK hdc f g hf hg
  have h1 : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hi : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_right
    rw [← hmul, inv_mul_cancel, h1]
  have hτ : ∀ φ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → ∀ x, φ (τ x) = φ x := by
    intro φ hφ x
    obtain ⟨k, hk, k', hk', h⟩ := hdc x
    rw [h, (hφ.2 k' hk' _).2, (hφ.2 k hk _).1]
  have hr : ∀ φ ψ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K ψ →
      ∀ y, ∀ k ∈ K, ∀ x, φ (x * k) * ψ ((x * k)⁻¹ * y) = φ x * ψ (x⁻¹ * y) := by
    intro φ ψ hφ hψ y k hk x
    rw [(hφ.2 k hk x).2, mul_inv_rev, mul_assoc, (hψ.2 k⁻¹ (K.inv_mem hk) _).1]
  funext y
  obtain ⟨k, hk, k', hk', hy⟩ := hdc y
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.cv
  rw [UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr f g hf hg y), UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr g f hg hf y)]
  let e : G ≃ G :=
    { toFun := fun z => y * k' * (τ z)⁻¹
      invFun := fun w => τ (w⁻¹ * (y * k'))
      left_inv := fun z => by
        have : (y * k' * (τ z)⁻¹)⁻¹ * (y * k') = τ z := by group
        simp only [this, hinv]
      right_inv := fun w => by
        simp only [hinv]
        group }
  refine UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr K (fun z => f z * g (z⁻¹ * y)) (fun z => g z * f (z⁻¹ * y))
    (hr g f hg hf y) e ?_ ?_
  · intro a b
    have h : (e a)⁻¹ * e b = τ (a⁻¹ * b)⁻¹ := by
      change (y * k' * (τ a)⁻¹)⁻¹ * (y * k' * (τ b)⁻¹) = _
      rw [hi, hmul, hi]
      group
    rw [h]
    constructor
    · exact fun hab => hK _ (K.inv_mem hab)
    · intro hab
      have h2 := hK _ hab
      rw [hinv] at h2
      exact K.inv_mem_iff.mp h2
  · intro z
    change g (y * k' * (τ z)⁻¹) * f ((y * k' * (τ z)⁻¹)⁻¹ * y) = f z * g (z⁻¹ * y)
    have h2 : (y * k' * (τ z)⁻¹)⁻¹ * y = τ z * k'⁻¹ := by group
    have h3 : τ (z⁻¹ * y) = k * (y * k' * (τ z)⁻¹) := by
      rw [hmul, hi, hy]
      group
    rw [h2, (hf.2 _ (K.inv_mem hk') _).2, hτ f hf, ← hτ g hg (z⁻¹ * y), h3, (hg.2 k hk _).1,
      mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckePolMap
section
noncomputable def UpperTheory.Reformulated.B.Qk6.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qk6.heckePol_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qk6.heckePol n q a) = UpperTheory.Reformulated.B.Qk6.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qk6.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HfsAevalRestrict
section
theorem UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict :
    ∀ {L W : Type} [inst : Field L] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module L W] (f : Module.End L W) {p : Submodule L W} (h : ∀ x ∈ p, (f : W → W) x ∈ p)
    (q : Polynomial L) (x : ↥p),
    (↑(((Polynomial.aeval (LinearMap.restrict f h) : Polynomial L → ↥p →ₗ[L] ↥p) q : ↥p → ↥p) x) : W) =
      ((Polynomial.aeval f : Polynomial L → Module.End L W) q : W → W) (↑x : W) := by
  intro L W _ _ _ f p h q x
  have hpow : ∀ (n : ℕ) (y : p), ((((LinearMap.restrict f h) ^ n) y : p) : W) = (f ^ n) (y : W) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
section
namespace UpperTheory.Reformulated.B.S8

theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single_of_mem a (Finset.mem_univ a) ?_
  intro b _ hb
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]

end UpperTheory.Reformulated.B.S8
end

