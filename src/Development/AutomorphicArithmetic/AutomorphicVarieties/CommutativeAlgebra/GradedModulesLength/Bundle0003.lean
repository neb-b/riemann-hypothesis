module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0002
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0003
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0002
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.DedekindDomain.Instances
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LaDifPerm
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem la_dif_perm {k : ℕ} {l l' : List (Deg k)} (h : l.Perm l') (f : Deg k → ℤ) :
    ∀ m, dif l f m = dif l' f m := by
  induction h with
  | nil => intro m; rfl
  | cons a _ ih => intro m; simp only [dif, ih]
  | swap a b l =>
    intro m
    simp only [dif]
    rw [sub_right_comm m a b]
    ring
  | trans _ _ ih1 ih2 => intro m; rw [ih1, ih2]

private theorem la_hdiff {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (ts : List (Deg k × R)) (G : GMod B R k) :
    ∀ m, Sm.hdiff ts G m = dif (ts.map Prod.fst) (hilb G) m := by
  induction ts with
  | nil => intro m; rw [Sm.hdiff_nil]; rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro m
    rw [Sm.hdiff_cons, ih, ih]
    rfl

private theorem la_adm {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (d : Deg k) (a y : X.R)
    (ts : List (Deg k × X.R)) (h : admitted X.𝒜 ((d, a * y) :: ts) J) : admitted X.𝒜 ((d, y) :: ts) J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨e, he⟩
  rcases List.mem_cons.1 he with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, List.mem_cons_self⟩)
  · exact Ideal.subset_span ⟨e, List.mem_cons_of_mem _ h⟩

private theorem la_mem {k : ℕ} (X : HidaSetting k) (β : X.B) (c : ℕ) {d : Deg k} {y : X.R} (hy : y ∈ X.𝒜 d) :
    algebraMap X.B X.R β ^ c * y ∈ X.𝒜 d := by
  rw [← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hy

private theorem la_peel {k : ℕ} (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) (β : X.B)
    (hβ : ∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0)
    (hA : admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann) (d : Deg k) (hd : 0 ≤ d) (y : X.R)
    (hy : y ∈ X.𝒜 d) (ts : List (Deg k × X.R)) (hV : Valid X.𝒜 ts) (c : ℕ) :
    admitted X.𝒜 ((d, algebraMap X.B X.R β ^ c * y) :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, algebraMap X.B X.R β ^ c * y) :: ts) F m =
      (c : ℤ) * dif (ts.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m + chi ((d, y) :: ts) F m := by
  have hb : algebraMap X.B X.R β ∈ X.𝒜 0 := by
    rw [X.std.zero]; exact ⟨β, rfl⟩
  have hs := ruleSmall k X ts _ hV ((ruleGr k X F hF).2.2 0 _ hb).1 hA
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    rw [pow_succ', mul_assoc] at h ⊢
    have hV' : Valid X.𝒜 ((0, algebraMap X.B X.R β) :: (d, algebraMap X.B X.R β ^ c * y) :: ts) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hb⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, la_mem X β c hy⟩
      · exact hV p hp
    filter_upwards [euler_rule_product_zero k X ts F d _ _ hV' hF h, ih (la_adm X _ d _ _ ts h), hs] with m h1 h2 h3
    have h4 : chi ts (F.quot (algebraMap X.B X.R β)) m = _ := h3.trans (la_hdiff ts _ m)
    rw [h1, h2, ruleNzd k X ts F 0 _ hβ m, h4]
    push_cast
    ring

theorem UpperTheory.V.Alg.M.la_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ β : X.B, (∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0) →
      admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann → ∀ (d : Deg k), 0 ≤ d → ∀ (n : ℕ) (y : Fin n → X.R) (c : Fin n → ℕ),
      (∀ i, y i ∈ X.𝒜 d) → ∀ us : List (Deg k × X.R), Valid X.𝒜 us →
      admitted X.𝒜 ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F.Ann →
      ∀ᶠ m in atTop, ((∑ i, c i : ℕ) : ℤ) * dif (List.replicate (n - 1) d ++ us.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m ≤
        chi ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F m := by
  intro k X F hF β hβ hA d hd n
  induction n with
  | zero =>
    intro y c _ us hV h
    simpa using rulePos k X us F hV hF (by simpa using h)
  | succ n ih =>
    intro y c hy us hV h
    rw [List.ofFn_succ, List.cons_append] at h ⊢
    set L := (List.ofFn fun i : Fin n => (d, algebraMap X.B X.R β ^ c i.succ * y i.succ)) with hL
    have hVL : Valid X.𝒜 (L ++ us) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨hd, la_mem X β _ (hy _)⟩
      · exact hV p hp
    have hc : ∀ l, Valid X.𝒜 l → Valid X.𝒜 ((d, y 0) :: l) := by
      intro l hl p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, hy 0⟩
      · exact hl p hp
    have hP : ((d, y 0) :: (L ++ us)).Perm (L ++ (d, y 0) :: us) := List.perm_middle.symm
    have h' := la_adm X _ d _ _ _ h
    have h'' : admitted X.𝒜 (L ++ (d, y 0) :: us) F.Ann := by
      unfold admitted at h' ⊢
      rwa [← E2.secs_perm hP]
    have hfst : (L ++ us).map Prod.fst = List.replicate n d ++ us.map Prod.fst := by
      rw [List.map_append, hL, List.map_ofFn]
      congr 1
      exact List.ofFn_const n d
    filter_upwards [la_peel X F hF β hβ hA d hd (y 0) (hy 0) _ hVL (c 0) h,
      euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X _ _ F (hc _ hVL) hP hF h',
      ih (fun i => y i.succ) (fun i => c i.succ) (fun i => hy _) _ (hc _ hV) h''] with m h1 h2 h3
    rw [h1, h2, hfst, Fin.sum_univ_succ, Nat.add_sub_cancel, Nat.cast_add, add_mul]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) h3)
    cases n with
    | zero => simp
    | succ n =>
      congr 1
      refine la_dif_perm ?_ _ m
      rw [Nat.add_sub_cancel, List.replicate_succ, List.map_cons, List.cons_append]
      exact List.perm_middle.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LengthQuotientSpanEqFinsumValuation
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem der_satSq {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) (f : A) (hf : f ∈ satSq x) : D f = 0 := by
  obtain ⟨c, hc, hcf⟩ := hf
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
    intro g hg
    rw [sq] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      have ha' : x a = 0 := ha
      have hb' : x b = 0 := hb
      rw [hD', ha', hb']; simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have := key _ hcf
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

private theorem len_le_of_inj {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (hN : Module.length O N ≠ ⊤) (ψ : M → N) (hψ : Function.Injective ψ) :
    Module.length O M ≤ Module.length O N := by
  obtain ⟨hfN, n, hn, hcn⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)
  have hfM : Finite M := Finite.of_injective ψ hψ
  have hM : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨_, m, hm, hcm⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [hcm, hcn] at hle
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [hm, hn]
  exact_mod_cast (Nat.pow_le_pow_iff_right h1).1 hle

theorem UpperTheory.V.Alg.M.mprime_holds :
    LemmaM' := by
  intro O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift
  by_cases htop : cotLen x 𝒜 j F = ⊤
  · rw [htop]; exact le_top
  have hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ) := by
    intro μ f hf
    obtain ⟨D', hD', -, h⟩ := hlift μ
    rw [LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]
  have hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤
      LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype) := by
    intro μ
    rw [LinearMap.ker_comp]
    refine Submodule.comap_mono ?_
    rw [cotSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDF μ i
  let ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c}) :=
    fun μ => Submodule.liftQ _ _ (hspan μ)
  have hψ : Function.Injective ψ := by
    intro μ ν h
    apply hD
    have hj : ∀ f ∈ 𝒜 j, D μ f = D ν f := fun f hf =>
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)
    have hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0 := by
      intro μ i hi f hf
      obtain ⟨D', -, hw, h⟩ := hlift μ
      rw [h, hw i hi f hf, map_zero]
    refine LinearMap.ext fun f => ?_
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero]
    | @homogeneous i m =>
      by_cases hij : i = j
      · subst hij; exact hj _ m.2
      · rw [hi μ i hij _ m.2, hi ν i hij _ m.2]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hp
  have hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1 := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk]
    exact Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k
  have hle := Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)
  exact (len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.neg_weight_le {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    -Finsupp.weight wt ν ≤ ((Finsupp.weight (negW wt) ν : ℕ) : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : -wt i ≤ ((negW wt i : ℕ) : ℤ) := by
    simp only [negW]
    exact Int.self_le_toNat _
  have hc : (0 : ℤ) ≤ (ν i : ℤ) := Int.natCast_nonneg _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  nlinarith

theorem UpperTheory.V.Alg.M.fil_holds :
    ∀ (E τ : Type) [CommRing E] (wt : τ → ℤ) (a b : ℕ) (g h : MvPowerSeries τ E), g ∈ fil E wt a → h ∈ fil E wt b →
      g * h ∈ fil E wt (a + b) ∧ ∀ j : ℤ, g ∈ wtPart E wt j → g ∈ fil E wt (-j).toNat := by
  intro E τ _ wt a b g h hg hh
  classical
  refine ⟨?_, ?_⟩
  · intro ν hν
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν := by
      rw [← hp, map_add (f := _)]
    by_cases h1 : Finsupp.weight (negW wt) p.1 < a
    · rw [hg p.1 h1, zero_mul]
    · rw [hh p.2 (by omega), mul_zero]
  · intro j hj ν hν
    by_contra hne
    have hwj : Finsupp.weight wt ν = j := by
      by_contra h'
      exact hne (hj ν h')
    have key := neg_weight_le wt ν
    rw [hwj] at key
    omega
end

