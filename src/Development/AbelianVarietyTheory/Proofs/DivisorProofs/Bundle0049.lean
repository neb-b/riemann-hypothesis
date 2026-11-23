module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensor
section
open TensorProduct

namespace GlobalTheory

theorem fibre_going_down_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  intro S A C _ _ _ _ _ u _ Q₁ _ hle h2
  let p := u.comap (algebraMap A (A ⊗[S] C))
  let p₁ := u.comap (algebraMap S (A ⊗[S] C))
  have hp : p₁ = p.comap (algebraMap S A) := by
    simp only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let K₁ := p₁.ResidueField
  let K := p.ResidueField
  letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra
  haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq
    (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)
  let F₁ := p₁.Fiber C
  let E := F₁ ⊗[K₁] K
  let e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S A K K C
  let e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S K₁ K K C
  let e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E := Algebra.TensorProduct.comm K₁ K F₁
  haveI : Module.Flat F₁ E := inferInstance
  haveI : Algebra.HasGoingDown F₁ E := inferInstance
  let Φ : p.Fiber (A ⊗[S] C) ≃+* E :=
    (e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv
  have hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C))
      = algebraMap F₁ E (Algebra.TensorProduct.includeRight c) := by
    intro c
    simp only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl

  haveI : u.LiesOver p := ⟨rfl⟩
  let isoA := PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p
  let ub := isoA ⟨u, inferInstance, inferInstance⟩
  have hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u := by
    have := congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)
    exact this
  have hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y
      ∈ ub.asIdeal ↔ y ∈ u := fun y => Iff.of_eq (congrArg (y ∈ ·) hub)

  haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩
  let iso₁ := PrimeSpectrum.primesOverOrderIsoFiber S C p₁
  let Qb := iso₁ ⟨Q₁, inferInstance, inferInstance⟩
  have hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁ := by
    have := congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)
    exact this

  let ue : Ideal E := ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))
  haveI : ue.IsPrime := Ideal.comap_isPrime _ _
  let w : Ideal F₁ := ue.comap (algebraMap F₁ E)
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : ue.LiesOver w := ⟨rfl⟩
  have hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) =
      u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C) := by
    ext c
    change Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _
    rw [← hΦ, RingEquiv.symm_apply_apply]
    exact hmem _
  have hwle : Qb.asIdeal ≤ w := by
    let u₁ := u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)
    haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : u₁.LiesOver p₁ := ⟨by
      show p₁ = u₁.comap (algebraMap S C)
      ext s
      simp [u₁, p₁]⟩
    let wP : PrimeSpectrum F₁ := ⟨w, inferInstance⟩
    have hsym : (iso₁.symm wP).1 = u₁ := hw
    have key : iso₁.symm Qb ≤ iso₁.symm wP := by
      show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1
      rw [hsym, iso₁.symm_apply_apply]
      exact hle
    exact (iso₁.symm.le_iff_le.mp key : Qb ≤ wP)
  obtain ⟨P, hPle, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle
  refine ⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap
    (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hmem]
    have := hPle hx
    simpa [ue] using this
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    erw [hΦ c]
    rw [← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]
  · ext a
    let J : Ideal K := (P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))
    haveI : J.IsPrime := Ideal.comap_isPrime _ _
    have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
    have hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C))
        (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a) := by
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.mem_comap, Ideal.mem_comap, hx]
    change algebraMap A K a ∈ J ↔ _
    rw [hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAwayOfIsAlgebraicOfFiniteType
section
namespace GlobalTheory

theorem finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by
  intro A B _ _ _ _ hft halg
  obtain ⟨s, hs⟩ := hft.out
  choose y hy hint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.mpr fun b _ => hy b, ?_⟩
  intro c A' B' _ _ _ _ _ _ _ _ hA' hB'
  set a := ∏ b ∈ s, y b with ha
  haveI hBB : Algebra.FiniteType B B' :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A B (a * c))) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans hft hBB
  haveI : Algebra.FiniteType A' B' := .of_restrictScalars_finiteType A A' B'
  have hu : IsUnit (algebraMap A A' (a * c)) := IsLocalization.Away.algebraMap_isUnit (a * c)
  have hunit : ∀ (r : A) (m : ℕ), r ∣ (a * c) ^ m → ∃ r' : A', algebraMap A' B' r' * algebraMap A B' r = 1 := by
    intro r m hr
    obtain ⟨u, hu'⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A A') hr) (by rw [map_pow]; exact hu.pow m)
    refine ⟨↑u⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply A A' B', ← hu', ← map_mul, Units.inv_mul, map_one]
  haveI : Algebra.IsIntegral A' B' := by
    let S : Subalgebra A B :=
      ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B')
    have hS : Algebra.adjoin A (s : Set B) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      intro b hb
      have h1 : IsIntegral A' (algebraMap B B' (y b • b)) :=
        ((hint b).map (IsScalarTower.toAlgHom A B B')).tower_top
      obtain ⟨r', hr'⟩ := hunit (y b) 1 (by rw [pow_one]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hb) c)
      show IsIntegral A' (algebraMap B B' b)
      have : algebraMap B B' b = algebraMap A' B' r' * algebraMap B B' (y b • b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, hr', one_mul]
      rw [this]
      exact isIntegral_algebraMap.mul h1
    rw [hs] at hS
    constructor
    intro x
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap A B (a * c))) x
    have hb : IsIntegral A' (algebraMap B B' b) := hS (Algebra.mem_top (x := b))
    obtain ⟨r', hr'⟩ := hunit ((a * c) ^ n) n dvd_rfl
    refine IsIntegral.of_mul_unit (y := algebraMap B B' (algebraMap A B (a * c) ^ n)) (r := r') ?_ ?_
    · rw [← map_pow, ← IsScalarTower.algebraMap_apply]; exact hr'
    · have hx' : x * algebraMap B B' (algebraMap A B (a * c) ^ n) = algebraMap B B' b := hx
      rw [hx']; exact hb
  exact Algebra.IsIntegral.finite

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCardTorsionQuotSmulTopLePowFinrank
section
open scoped TensorProduct

namespace GlobalTheory.TorsionCount

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem exists_colon_gen (I J : Ideal R) (hI : I.IsMaximal) (hJ : J ≠ ⊥) :
    ∃ c : R, (∀ a ∈ I, c * a ∈ J) ∧ ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J := by
  by_cases hle : J ≤ I
  · obtain ⟨J', rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ' : J' ≠ ⊥ := by rintro rfl; simp at hJ
    have hI0 : I ≠ ⊥ := by rintro rfl; simp at hJ
    have hne : ¬ J' ≤ I * J' := by
      intro h
      have h1 : I * J' ∣ 1 * J' := by rw [one_mul]; exact Ideal.dvd_iff_le.2 h
      rw [mul_dvd_mul_iff_right hJ', Ideal.one_eq_top] at h1
      exact hI.ne_top (eq_top_iff.2 (Ideal.dvd_iff_le.1 h1))
    obtain ⟨c, hc, hcn⟩ := Set.not_subset.1 hne
    refine ⟨c, fun a ha => ?_, fun x hx => ?_⟩
    · rw [mul_comm c a]; exact Ideal.mul_mem_mul ha hc
    · have hLJ' : Ideal.span {c} ⊔ I * J' ≤ J' :=
        sup_le (by rw [Ideal.span_le]; simpa using hc) (Ideal.mul_le_inf.trans inf_le_right)
      obtain ⟨L', hL'⟩ := Ideal.dvd_iff_le.2 hLJ'
      have hIL' : I ≤ L' := by
        have h2 : J' * L' ∣ J' * I := by
          rw [← hL', mul_comm J' I]; exact Ideal.dvd_iff_le.2 le_sup_right
        exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hJ').1 h2)
      by_cases htop : L' = ⊤
      · rw [htop, Ideal.mul_top] at hL'
        have hxJ' : x ∈ J' := by
          have h3 : Ideal.span {x} * I ≤ J' * I := by
            rw [Ideal.span_singleton_mul_le_iff]
            intro z hz
            rw [mul_comm x z, mul_comm J' I]; exact hx z hz
          have := (mul_dvd_mul_iff_right hI0).1 (Ideal.dvd_iff_le.2 h3)
          exact Ideal.dvd_iff_le.1 this (Ideal.mem_span_singleton_self x)
        rw [← hL', Ideal.mem_span_singleton_sup] at hxJ'
        obtain ⟨r, b, hb, hrb⟩ := hxJ'
        exact ⟨r, by rw [← hrb]; simpa using hb⟩
      · have hEq : L' = I := (hI.eq_of_le htop hIL').symm
        rw [hEq, mul_comm] at hL'
        exact (hcn (by rw [mul_comm I J', ← hL']; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))).elim
  · have hsup : I ⊔ J = ⊤ :=
      hI.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))
    refine ⟨0, fun a _ => by simp, fun x hx => ⟨0, ?_⟩⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
    have : x = u * x + x * v := by rw [mul_comm u, ← mul_add, huv, mul_one]
    rw [zero_mul, sub_zero, this]
    exact J.add_mem (hx u hu) (J.mul_mem_left x hv)

variable {M : Type} [AddCommGroup M] [Module R M]

omit [IsDedekindDomain R] in
theorem map_mem_of_mem_smul_top {S : Type} [CommRing S] {N : Type} [AddCommGroup N] [Module S N]
    (J : Ideal S) (φ : N →ₗ[S] S) {z : N} (hz : z ∈ J • (⊤ : Submodule S N)) : φ z ∈ J := by
  exact Submodule.smul_induction_on hz (fun a ha n _ => by
      rw [map_smul, smul_eq_mul]; exact J.mul_mem_right _ ha)
    (fun x y hx hy => by rw [map_add (f := _)]; exact J.add_mem hx hy)

omit [IsDedekindDomain R] in
theorem mem_range_of_torsion [Module.Finite R M] [Module.Projective R M] (I J : Ideal R) (c : R)
    (hc : ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J)
    (y : M ⧸ J • (⊤ : Submodule R M)) (hy : ∀ a ∈ I, a • y = 0) :
    ∃ m : M, Submodule.Quotient.mk (c • m) = y := by
  obtain ⟨m0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨n, g, f, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hcoord : ∀ j, ∃ r : R, f m0 j - r * c ∈ J := by
    intro j
    refine hc _ fun a ha => ?_
    have h1 : a • m0 ∈ J • (⊤ : Submodule R M) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hy a ha
    have h2 := map_mem_of_mem_smul_top J ((LinearMap.proj j) ∘ₗ f) h1
    simpa using h2
  choose r hr using hcoord
  refine ⟨g r, (Submodule.Quotient.eq _).2 ?_⟩
  have hm0 : m0 = g (f m0) := by
    have := congrArg (fun φ => φ m0) hfg; simpa using this.symm
  have hdec : f m0 - c • r = ∑ j, (f m0 j - r j * c) • Pi.single j (1 : R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have : c • g r - m0 = -(g (f m0 - c • r)) := by
    rw [map_sub, map_smul, ← hm0]; abel
  rw [this]
  refine Submodule.neg_mem _ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  exact Submodule.sum_mem _ fun j _ => by
    rw [map_smul]; exact Submodule.smul_mem_smul (hr j) trivial

theorem card_quot_smul_top [Module.Finite R M] [Module.Projective R M] (I : Ideal R) [I.IsMaximal]
    [Finite (R ⧸ I)] : Finite (M ⧸ I • (⊤ : Submodule R M)) ∧
      Nat.card (M ⧸ I • (⊤ : Submodule R M)) = Nat.card (R ⧸ I) ^ Module.finrank R M := by
  let ek : (R ⧸ I) ≃ₐ[R] I.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) I.ResidueField)
      I.bijective_algebraMap_quotient_residueField
  let e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] I.ResidueField ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ
      TensorProduct.congr ek.toLinearEquiv (LinearEquiv.refl R M)
  haveI : Finite I.ResidueField := Finite.of_equiv _ ek.toEquiv
  haveI : Finite (I.ResidueField ⊗[R] M) := Module.finite_of_finite I.ResidueField
  have hr : Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) = Module.finrank R M :=
    Ideal.finrank_fiber_eq_finrank I
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := I.ResidueField), hr,
    Nat.card_congr ek.toEquiv]

theorem torsion_card : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal →
    Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧
      Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤
        Nat.card (R ⧸ I) ^ Module.finrank R M := by
  intro R _ _ M _ _ _ _ I J hI hfin hJ
  obtain ⟨c, hcI, hc⟩ := exists_colon_gen I J hI hJ
  let f : M →ₗ[R] M ⧸ J • (⊤ : Submodule R M) :=
    (J • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.lsmul R M c)
  have hfI : I • (⊤ : Submodule R M) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha m _
    rw [LinearMap.mem_ker]
    simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_smul]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let g := (I • (⊤ : Submodule R M)).liftQ f hfI
  have hgT : ∀ z, ∀ a ∈ I, a • g z = 0 := by
    intro z a ha
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    simp only [g, Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_smul]
    rw [mul_comm]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let h : (M ⧸ I • (⊤ : Submodule R M)) →
      {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} := fun z => ⟨g z, hgT z⟩
  have hsurj : Function.Surjective h := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm⟩ := mem_range_of_torsion I J c hc y hy
    exact ⟨Submodule.Quotient.mk m, Subtype.ext (by simpa [h, g, f] using hm)⟩
  obtain ⟨hQ, hcard⟩ := card_quot_smul_top (M := M) I
  exact ⟨Finite.of_surjective h hsurj, (Nat.card_le_card_of_surjective h hsurj).trans hcard.le⟩

end GlobalTheory.TorsionCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParam
section
open MeasureTheory Topology

namespace GlobalTheory.KernelCovolume

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma c_zero {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) : c 0 = 1 :=
  mul_left_cancel (a := c 0) (by rw [mul_one, ← hca, add_zero])

lemma c_neg {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (r : ℝ) : (c r)⁻¹ = c (-r) :=
  inv_eq_of_mul_eq_one_right (by rw [← hca, add_neg_cancel, c_zero hca])

def cHom (c : ℝ → G) (hca : ∀ x y, c (x + y) = c x * c y) : Multiplicative ℝ →* G where
  toFun x := c (Multiplicative.toAdd x)
  map_one' := c_zero hca
  map_mul' x y := hca _ _

lemma c_int {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (n : ℤ) : c n = c 1 ^ n := by
  have h := map_zpow (cHom c hca) (Multiplicative.ofAdd (1:ℝ)) n
  rw [← ofAdd_zsmul, zsmul_one] at h
  exact h

lemma mem_of_split {H : Subgroup G} {s : G → ℝ} {c : ℝ → G}
    (hsa : ∀ g h, s (g * h) = s g + s h) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0)
    (g : G) : g * c (-s g) ∈ H := by
  rw [hH, hsa, hsc]; ring

def splitHomeo {H : Subgroup G} {s : G → ℝ} {c : ℝ → G} (hs : Continuous s)
    (hsa : ∀ g h, s (g * h) = s g + s h) (hc : Continuous c)
    (hca : ∀ x y, c (x + y) = c x * c y) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0) :
    H × ℝ ≃ₜ G where
  toFun p := (p.1 : G) * c p.2
  invFun g := (⟨g * c (-s g), mem_of_split hsa hsc hH g⟩, s g)
  left_inv p := by
    rcases p with ⟨⟨h, hh⟩, t⟩
    have h0 : s h = 0 := (hH h).1 hh
    have e : s (h * c t) = t := by rw [hsa, hsc, h0, zero_add]
    refine Prod.ext (Subtype.ext ?_) ?_
    · show h * c t * c (-s (h * c t)) = h
      rw [e, mul_assoc, ← hca, add_neg_cancel, c_zero hca, mul_one]
    · exact e
  right_inv g := by
    show g * c (-s g) * c (s g) = g
    rw [mul_assoc, ← hca, neg_add_cancel, c_zero hca, mul_one]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd)
  continuous_invFun := (Continuous.subtype_mk (continuous_id.mul (hc.comp hs.neg)) _).prodMk hs

end GlobalTheory.KernelCovolume

open scoped Pointwise

open GlobalTheory.KernelCovolume in
theorem GlobalTheory.finiteCovolume_kernel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H Γ Λ s c hs hsa hc hca hcc hsc hH hΓ hΛ _hdisc hfin π D hπ hD
  have hcl : IsClosed (H : Set G) := by
    have : (H : Set G) = s ⁻¹' {0} := by ext g; exact hH g
    rw [this]; exact isClosed_singleton.preimage hs
  haveI : LocallyCompactSpace H := hcl.locallyCompactSpace
  haveI : SigmaCompactSpace H := hcl.sigmaCompactSpace
  haveI : SigmaFinite π := inferInstance
  set φ : H × ℝ ≃ₜ G := GlobalTheory.KernelCovolume.splitHomeo hs hsa hc hca hsc hH with hφdef
  have hφ : ∀ p : H × ℝ, φ p = (p.1 : G) * c p.2 := fun p => rfl
  set μ0 : Measure (H × ℝ) := π.prod volume with hμ0
  set ν : Measure G := μ0.map φ with hνdef
  have hνapp : ∀ A, ν A = μ0 (φ ⁻¹' A) := fun A => φ.toMeasurableEquiv.map_apply A
  have hmulφ : ∀ (γ : H) (r : ℝ) (p : H × ℝ), (γ : G) * c r * φ p = φ (γ * p.1, r + p.2) := by
    intro γ r p
    simp only [hφ, Subgroup.coe_mul, hca, mul_assoc]
    rw [← mul_assoc (c r) (p.1 : G), hcc r, mul_assoc]

  haveI : (Subgroup.zpowers (c 1)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute ((c 1) ^ k) g := (Commute.zpow_left (hcc 1 g) k)
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers _ _⟩
  have hdec : ∀ l ∈ Λ, ∃ γ ∈ Γ, ∃ n : ℤ, l = γ * c n := by
    intro l hl
    rw [hΛ] at hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨y, hy, n, by rw [GlobalTheory.KernelCovolume.c_int hca]⟩
  have hmemΛ : ∀ γ ∈ Γ, ∀ n : ℤ, γ * c n ∈ Λ := by
    intro γ hγ n
    rw [hΛ, GlobalTheory.KernelCovolume.c_int hca]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

  have hνHaar : ν.IsHaarMeasure := by
    haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ0 φ
    haveI : ν.IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
    haveI : ν.IsMulLeftInvariant := ⟨fun g => by
      obtain ⟨p0, rfl⟩ := φ.surjective g
      ext A hA
      rw [Measure.map_apply (measurable_const_mul _) hA, hνapp, hνapp]
      have hpre : φ ⁻¹' ((fun x => φ p0 * x) ⁻¹' A) =
          (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) ⁻¹' (φ ⁻¹' A) := by
        ext p
        simp only [Set.mem_preimage, Prod.map]
        rw [show φ p0 = (p0.1 : G) * c p0.2 from rfl, hmulφ]
      have hT : μ0.map (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) = μ0 := by
        rw [hμ0, ← Measure.map_prod_map π volume (measurable_const_mul _) (measurable_const_add _),
          map_mul_left_eq_self, map_add_left_eq_self]
      rw [hpre, ← Measure.map_apply ((measurable_const_mul _).prodMap (measurable_const_add _))
        (φ.measurable hA), hT]⟩
    exact ⟨⟩

  set S : Set (H × ℝ) := D ×ˢ Set.Ico (0:ℝ) 1 with hS
  set D' : Set G := φ.symm ⁻¹' S with hD'
  have hφD' : φ ⁻¹' D' = S := by ext p; simp [hD']
  have hsub : ∀ (l : Λ) (γ : G) (hγ : γ ∈ Γ) (n : ℤ), (l : G) = γ * c n → ∀ p : H × ℝ,
      φ p ∈ l • D' → (⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1 ∈ D ∧ ((-n : ℤ) : ℝ) + p.2 ∈ Set.Ico (0:ℝ) 1 := by
    intro l γ hγ n e p hp
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hp
    have hx : l⁻¹ • φ p = φ ((⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1, ((-n : ℤ) : ℝ) + p.2) := by
      rw [← hmulφ, Subgroup.smul_def, smul_eq_mul]
      congr 1
      simp only [Subgroup.coe_inv, e, mul_inv_rev, GlobalTheory.KernelCovolume.c_neg hca, Int.cast_neg]
      exact hcc _ _
    rw [hx] at hp
    simpa [hD', hS] using hp
  have hFD : IsFundamentalDomain Λ D' ν := by
    refine { nullMeasurableSet := ?_, ae_covers := ?_, aedisjoint := ?_ }
    · exact (hD.nullMeasurableSet.prod measurableSet_Ico.nullMeasurableSet).preimage
        (φ.toMeasurableEquiv.quasiMeasurePreserving_symm μ0)
    · rw [hνdef, show (⇑φ : H × ℝ → G) = ⇑φ.toMeasurableEquiv from rfl,
        φ.toMeasurableEquiv.measurableEmbedding.ae_map_iff]
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp
      obtain ⟨γ, hγ⟩ := hp
      have hγΓ : ((γ : H) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      refine ⟨⟨((γ : H) : G) * c ((-⌊p.2⌋ : ℤ) : ℝ), hmemΛ _ hγΓ _⟩, ?_⟩
      rw [Subgroup.smul_def, smul_eq_mul]
      show _ ∈ φ.symm ⁻¹' S
      rw [Set.mem_preimage, show (φ.toMeasurableEquiv p) = φ p from rfl, hmulφ, φ.symm_apply_apply]
      have hfr : ((-⌊p.2⌋ : ℤ) : ℝ) + p.2 = Int.fract p.2 := by
        rw [Int.cast_neg, Int.fract]; ring
      rw [hfr]
      exact Set.mk_mem_prod hγ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro l1 l2 hne
      obtain ⟨γ1, hγ1, n1, e1⟩ := hdec l1 l1.2
      obtain ⟨γ2, hγ2, n2, e2⟩ := hdec l2 l2.2
      show ν ((l1 • D') ∩ (l2 • D')) = 0
      rw [hνapp]
      by_cases hn : n1 = n2
      · subst hn
        have hγne : γ1 ≠ γ2 := by
          rintro rfl; exact hne (Subtype.ext (e1.trans e2.symm))
        let g1 : Γ.subgroupOf H := ⟨⟨γ1, hΓ hγ1⟩, Subgroup.mem_subgroupOf.2 hγ1⟩
        let g2 : Γ.subgroupOf H := ⟨⟨γ2, hΓ hγ2⟩, Subgroup.mem_subgroupOf.2 hγ2⟩
        have hg : g1 ≠ g2 := fun h => hγne (congrArg (fun x : Γ.subgroupOf H => ((x : H) : G)) h)
        have h0 : π (g1 • D ∩ g2 • D) = 0 := hD.aedisjoint hg
        refine measure_mono_null (t := (g1 • D ∩ g2 • D) ×ˢ Set.univ) ?_ ?_
        · rintro p ⟨hp1, hp2⟩
          refine Set.mk_mem_prod ⟨?_, ?_⟩ (Set.mem_univ _)
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l1 γ1 hγ1 n1 e1 p hp1).1
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l2 γ2 hγ2 n1 e2 p hp2).1
        · rw [hμ0, Measure.prod_prod, h0, zero_mul]
      · refine measure_mono_null (t := ∅) ?_ measure_empty
        rintro p ⟨hp1, hp2⟩
        have a1 := (hsub l1 γ1 hγ1 n1 e1 p hp1).2
        have a2 := (hsub l2 γ2 hγ2 n2 e2 p hp2).2
        simp only [Set.mem_Ico, Int.cast_neg] at a1 a2
        have b1 : (n1 : ℝ) < n2 + 1 := by linarith
        have b2 : (n2 : ℝ) < n1 + 1 := by linarith
        have c1 : n1 < n2 + 1 := by exact_mod_cast b1
        have c2 : n2 < n1 + 1 := by exact_mod_cast b2
        exact absurd (by omega : n1 = n2) hn
  have hfinν := hfin ν D' hνHaar hFD
  have hνD' : ν D' = π D := by
    rw [hνapp, hφD', hS, hμ0, Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
      mul_one]
  rwa [hνD'] at hfinν
end

