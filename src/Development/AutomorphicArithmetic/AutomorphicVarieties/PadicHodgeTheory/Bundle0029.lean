module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryPadicSqrt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh9.isCM_of_conj K h

private theorem exists_root_lift {Ω M : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field M] [CharZero M]
    (j : Ω →+* M) (g : Polynomial ℚ) (hg : g ≠ 0) (β : M) (hβ : Polynomial.aeval β g = 0) :
    ∃ b : Ω, j b = β ∧ Polynomial.aeval b g = 0 := by
  have hs : (g.map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
  have hne : g.map (algebraMap ℚ Ω) ≠ 0 := Polynomial.map_ne_zero hg
  have hroot : ((g.map (algebraMap ℚ Ω)).map j).IsRoot β := by
    rw [Polynomial.map_map, Subsingleton.elim (j.comp (algebraMap ℚ Ω)) (algebraMap ℚ M)]
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hβ
  obtain ⟨b, hb⟩ := hs.mem_range_of_isRoot hne hroot
  refine ⟨b, hb, j.injective ?_⟩
  have := Polynomial.aeval_algHom_apply j.toRatAlgHom b g
  rw [map_zero]
  change Polynomial.aeval (j b) g = j _ at this
  rw [← this, hb, hβ]

private theorem exists_sqrt_padic (l : ℕ) [Fact l.Prime] : ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * l := by
  let P : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (l : ℤ_[l])
  have h : ‖Polynomial.aeval (0 : ℤ_[l]) P‖ < ‖Polynomial.aeval (0 : ℤ_[l]) (Polynomial.derivative P)‖ ^ 2 := by
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp [P]
    exact inv_lt_one_of_one_lt₀ hl
  obtain ⟨z, hz, -⟩ := hensels_lemma h
  have hz' : z ^ 2 - z + l = 0 := by simpa [P] using hz
  have hz2 : (z : ℚ_[l]) ^ 2 - z + l = 0 := by exact_mod_cast congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) hz'
  exact ⟨2 * z - 1, by linear_combination 4 * hz2⟩

theorem UpperTheory.exists_totally_imaginary_padic_sqrt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (j : Ω →+* Om l) (K : FinExt l), ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (_ : Algebra E Ω) (_ : IsAlgClosure E Ω), IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) = K.1 ∧ ∃ δ : E, δ ≠ 0 ∧ (∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) ∧ j (algebraMap E Ω δ) ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro F Ω _ _ _ _ _ l _ j K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have halg : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  obtain ⟨β, g, hg, hβ, hreal, hK⟩ := UpperTheory.exists_totally_real_primitive_element_padic_finite_ext l K
  obtain ⟨b, hb, hbg⟩ := exists_root_lift j g hg.ne_zero β hβ
  obtain ⟨d, hd⟩ := exists_sqrt_padic l
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * l : Ω) (n := 2) two_pos
  obtain ⟨δ, hδ, hjδ⟩ : ∃ δ : Ω, δ ^ 2 = 1 - 4 * l ∧ j δ = algebraMap ℚ_[l] (Om l) d := by
    have h1 : j e ^ 2 = (algebraMap ℚ_[l] (Om l) d) ^ 2 := by
      rw [← map_pow, ← map_pow, he, hd]; simp [map_ofNat]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact ⟨e, he, h⟩
    · exact ⟨-e, by rw [neg_sq, he], by rw [map_neg, h, neg_neg]⟩
  let E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {b, δ}
  have hfin : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hNF : NumberField E := ⟨⟩
  let b' : E := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ' : E := ⟨δ, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ' : δ' ^ 2 = 1 - 4 * l := (algebraMap E Ω).injective (by
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]; exact hδ)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hre : ∀ φ : E →+* ℂ, (φ δ').re = 0 ∧ (φ δ').im ≠ 0 := fun φ => by
    have h : φ δ' ^ 2 = 1 - 4 * l := by rw [← map_pow, hδ']; simp [map_ofNat]
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have h3 : (φ δ').im ≠ 0 := by
      intro h0
      rw [h0] at h1
      nlinarith [mul_self_nonneg (φ δ').re]
    refine ⟨?_, h3⟩
    have : (φ δ').re * (φ δ').im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right h3
  have hconj : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ') = -φ δ' := fun φ => by
    apply Complex.ext <;> simp [(hre φ).1]
  have hbb : ∀ φ : E →+* ℂ, (φ b').im = 0 := fun φ => by
    apply hreal
    have h0 : Polynomial.aeval b' g = 0 := by
      apply (algebraMap E Ω).injective
      rw [← Polynomial.aeval_algebraMap_apply, map_zero]
      exact hbg
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b' g
    rw [h0, map_zero] at this
    exact this
  have htc : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ') = w.embedding δ' := congrArg (fun f : E →+* ℂ => f δ') h
    exact (hre w.embedding).2 (Complex.conj_eq_iff_im.mp h1)⟩
  have hCM : IsCMField E := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b', fun φ => (Complex.conj_eq_iff_im.mpr (hbb φ)).symm⟩
      · exact ⟨-δ', fun φ => by rw [map_neg]; exact (hconj φ).symm⟩
    | algebraMap a =>
      refine ⟨(a : E), fun φ => ?_⟩
      change φ (a : E) = starRingEnd ℂ (φ (a : E))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add (f := _), ha, hb, ← map_add (f := _), ← map_add (f := _)]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  have hAC : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  refine ⟨E, inferInstance, hNF, hCM, inferInstance, hAC, ?_, δ', ?_, hconj, ⟨d, hjδ.symm⟩⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      change j x ∈ K.1
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · rw [hb, ← hK]; exact IntermediateField.mem_adjoin_simple_self _ _
        · rw [hjδ]; exact IntermediateField.algebraMap_mem _ _
      | algebraMap a => simp
      | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
      | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
      | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
    · rw [← hK]
      apply IntermediateField.adjoin.mono
      rintro _ rfl
      exact ⟨b', hb⟩
  · intro h
    have φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    exact (hre φ).2 (by rw [h]; simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsWeilInvariantInDpstOfWeilDeligneInvariant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_weil_group {Γ I K D W : Type} [Group Γ] [Group I] [Field K] [CharZero K]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (j : I →* Γ) (φ : Γ) (hn : ∀ s, ∃ t, j s * φ = φ * j t) (hg : ∀ σ, ∃ (n : ℤ) (t : I), σ = φ ^ n * j t)
    (a : Γ →* Module.End K D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (I ⧸ (a.comp j).ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hno
  let := Fintype.ofFinite (I ⧸ (a.comp j).ker)
  let a' : I ⧸ (a.comp j).ker →* Module.End K D := QuotientGroup.lift _ (a.comp j) le_rfl
  have ha : ∀ q : I ⧸ (a.comp j).ker, a (j q.out) = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let n : ℕ := Fintype.card (I ⧸ (a.comp j).ker)
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let E : Module.End K D := ∑ q : I ⧸ (a.comp j).ker, a (j q.out)
  let E' : Module.End ℂ W := ∑ q : I ⧸ (a.comp j).ker, b (j q.out)
  have hE : ∀ x s, a (j s) (E x) = E x := fun x s => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, LinearMap.sum_apply, map_sum, ha]
    refine Fintype.sum_equiv (Equiv.mulLeft (s : I ⧸ (a.comp j).ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have hE1 : ∀ z, (∀ s, a (j s) z = z) → E z = n • z := fun z hz => by
    simp only [E, LinearMap.sum_apply, hz, Finset.sum_const, Finset.card_univ, n]
  have hE2 : E' y = n • y := by
    simp only [E', LinearMap.sum_apply, hi, Finset.sum_const, Finset.card_univ, n]
  have hEE : ∀ x, E' (mk x) = mk (E x) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, E', LinearMap.sum_apply, hc, map_sum]
  have hcan : ∀ z : D, n • z = 0 → z = 0 := fun z hz => by
    rw [← Nat.cast_smul_eq_nsmul K] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn0
  let S : Module.End K D := a φ * E - E + n • 1 - E
  let S' : Module.End ℂ W := b φ * E' - E' + n • 1 - E'
  have hS : ∀ x, S x = a φ (E x) - E x + n • x - E x := fun x => rfl
  have hS' : ∀ x, S' x = b φ (E' x) - E' x + n • x - E' x := fun x => rfl
  have hinj : Function.Injective S := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ s, a (j s) (a φ (E x)) = a φ (E x) := fun s => by
      obtain ⟨t, ht⟩ := hn s
      rw [← Module.End.mul_apply, ← map_mul, ht, map_mul, Module.End.mul_apply, hE]
    have h2 := congrArg E hx
    rw [hS, map_sub, map_add (f := _), map_sub, map_nsmul, hE1 _ h1, hE1 _ (hE x), map_zero, add_sub_cancel_right,
      ← smul_sub] at h2
    have h3 : a φ (E x) = E x := sub_eq_zero.mp (hcan _ h2)
    have h4 : E x = 0 := by
      by_contra h0
      refine hno ⟨_, h0, fun g => ?_⟩
      obtain ⟨m, t, rfl⟩ := hg g
      rw [map_mul, Module.End.mul_apply, hE]
      exact (GlobalTheory.PstLaws.vecStab a (E x)).zpow_mem h3 m
    rw [hS, h4, map_zero, sub_zero, sub_zero, zero_add] at hx
    exact hcan _ hx
  have hsur := LinearMap.injective_iff_surjective.mp hinj
  have hsur' : Function.Surjective S' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsur x
    refine ⟨mk z, ?_⟩
    rw [hS, hS', hEE, hc, map_sub, map_add (f := _), map_sub, map_nsmul]
  refine hy (LinearMap.injective_iff_surjective.mpr hsur' ?_)
  rw [hS', hE2, map_nsmul, hi, map_zero, sub_self, zero_add, sub_self]

theorem UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1
  obtain ⟨y, hy, hi⟩ := h1
  let a : ↥(Weil h) →* Module.End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    { toFun := fun σ => urEnd P ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
      map_one' := LinearMap.ext fun x => LinearMap.congr_fun (map_one (weilD Bw h P ρ)) ((toUr P ρ).symm x)
      map_mul' := fun σ τ => LinearMap.ext fun x =>
        LinearMap.congr_fun (map_mul (weilD Bw h P ρ) σ τ) ((toUr P ρ).symm x) }
  have := compactSpace_Ine (E := F) A
  have hle : (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker ≤ (a.comp (ineIncl h)).ker := fun s hs =>
    LinearMap.ext fun x => LinearMap.congr_fun (MonoidHom.mem_ker.mp hs) ((toUr P ρ).symm x)
  have : Finite (Ine (F := F) A ⧸ (a.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle (isSmooth_weilD Bw h P ρ hj))
  have hn : ∀ s, ∃ t, ineIncl h s * frob h = frob h * ineIncl h t := fun s => by
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (ineIncl h s * frob h)
    refine ⟨t, ?_⟩
    rw [deg_mul, deg_ineIncl, deg_frob, zero_add, zpow_one] at ht
    exact ht
  obtain ⟨x, hx, hf⟩ := UpperTheory.fixed_vector_descends_weil_group (ineIncl h) (frob h) hn
    (fun σ => ⟨deg σ, exists_eq_zpow_mul (deg_frob (h := h)) σ⟩) a (wdRho P ι Bw h hj ρ)
    ((AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)).comp (toUr P ρ).symm.toAddMonoidHom) (span_wdMk P ι ρ)
    (fun g x => wdRho_mk P ι Bw h hj ρ g ((toUr P ρ).symm x)) y hy hi
  exact ⟨(toUr P ρ).symm x, hx, hf⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfMemSpectrumFrobeniusMatrixFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private noncomputable def filS {l : ℕ} [Fact l.Prime] (K : FinExt l) : Subring (Bcr l) where
  carrier := {x | ∀ k : ℕ, (PP l).ιB (((PP l).φB ^ k) x) ∈ ((PP l).PD K).Fil 0}
  mul_mem' := fun {a b} ha hb k => by
    rw [map_mul, map_mul]
    simpa using ((PP l).PD K).Fil_mul 0 0 _ _ (ha k) (hb k)
  one_mem' := fun k => by
    rw [map_one, map_one]; exact ((PP l).PD K).one_mem
  add_mem' := fun {a b} ha hb k => by
    rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ (ha k) (hb k)
  zero_mem' := fun k => by
    rw [map_zero, map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha k => by
    rw [map_neg, map_neg]; exact Submodule.neg_mem _ (ha k)

private theorem frobenius_iterate_unramified {l : ℕ} [Fact l.Prime] (K : FinExt l) (k : ℕ) (c : ↥(K0 K)) :
    ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K,
      ((PP l).PD K).φ_K₀]

private theorem K0_mem {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(K0 K)) :
    algebraMap ↥(K0 K) (Bcr l) c ∈ filS K := by
  intro k
  rw [AlgHom.coe_pow, frobenius_iterate_unramified, ← (PP l).PD_ι K, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul ↥K.1]
  exact Submodule.smul_mem _ _ ((PP l).PD K).one_mem

private theorem fil_iff {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (x : Bdr l) :
    x ∈ ((PP l).PD K).Fil 0 ↔ x ∈ ((PP l).PD K').Fil 0 := by
  obtain ⟨T⟩ := tiedP l
  rw [T.fil, T.fil]

theorem UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K)), M' * M = 1 → (∀ (k : ℕ) i j, (PP l).ιB (((PP l).φB)^[k] (M i j)) ∈ ((PP l).PD (botExt l)).Fil 0) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖a‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' F hM hFil hφ a ha
  obtain ⟨T⟩ := tiedP l
  haveI : IsDomain (Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hdet⟩ := UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum (K0 K) F a ha
  set j : ↥(K0 K) →+* Bcr l := algebraMap ↥(K0 K) (Bcr l) with hj
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin d) (Fin r) (Bcr l), X = M * Y.map j := ⟨_, rfl⟩
  have hZX : (Z.map j * M') * X = 1 := by
    rw [hXd]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M', hM, Matrix.one_mul, ← Matrix.map_mul, hZY,
      Matrix.map_one _ (map_zero j) (map_one j)]
  have hYψ : (Y.map j).map ψ = Y.map j := by
    ext i k
    simp only [Matrix.map_apply]
    rw [hψ, hj, frobenius_iterate_unramified, hσ]
  have hX : X.map ψ = X * F'.map j := by
    rw [hXd]
    rw [Matrix.map_mul, hYψ, hψ, hφ, Matrix.mul_assoc, ← Matrix.map_mul, hFY, Matrix.map_mul,
      Matrix.mul_assoc]
  obtain ⟨s, hs⟩ := UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse X _ hZX
  have hXS : ∀ i k, X i k ∈ filS K := by
    intro i k
    simp only [hXd, Matrix.mul_apply, Matrix.map_apply]
    refine Subring.sum_mem _ fun c _ => Subring.mul_mem _ (fun n => ?_) (K0_mem K _)
    rw [AlgHom.coe_pow]
    exact (fil_iff _ _ _).1 (hFil n i c)
  have hbS : (X.submatrix s id).det ∈ filS K := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hXS _ _)
  have hb : ((PP l).φB)^[f] (X.submatrix s id).det = j F'.det * (X.submatrix s id).det := by
    have h1 : (X.submatrix s id).map ψ = X.submatrix s id * F'.map j := by
      ext i k
      have := congrFun (congrFun hX (s i)) k
      simpa [Matrix.mul_apply] using this
    rw [← hψ, RingHom.map_det, RingHom.mapMatrix_apply, h1, Matrix.det_mul, mul_comm,
      RingHom.map_det, RingHom.mapMatrix_apply]
  have hle := UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero K f hf hσ _ F'.det hs hb fun i => by
    have := hbS i
    rw [AlgHom.coe_pow] at this
    exact (fil_iff _ _ _).1 this
  rw [hdet] at hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg a) hr.ne').1 hle
end

