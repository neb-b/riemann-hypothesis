module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpCS

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma norm_tsum_sq_le_card_mul_sum_sq {α ι : Type*} (s : Finset ι) (f : ι → α → ℂ)
    (g : α → ℂ) (hg : ∀ a, g a = ∑ i ∈ s, f i a) (hdom : ∀ i ∈ s, ∀ a, ‖f i a‖ ≤ ‖g a‖) :
    ‖∑' a, g a‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by
  by_cases hs : Summable g
  · have hfi : ∀ i ∈ s, Summable (f i) := fun i hi =>
      Summable.of_norm_bounded (summable_norm_iff.mpr hs) (hdom i hi)
    have hsum : ∑' a, g a = ∑ i ∈ s, ∑' a, f i a := by
      simp_rw [hg]
      exact Summable.tsum_finsetSum hfi
    rw [hsum]
    calc ‖∑ i ∈ s, ∑' a, f i a‖ ^ 2 ≤ (∑ i ∈ s, ‖∑' a, f i a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    have : (0 : ℝ) ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by positivity
    simpa using this


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.AmpCS.ampSq_le_card_mul_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 1 ≤ k → ∀ {ι : Type} (s : Finset ι) (P : ι → S.Datum → Submodule L.O S.V → Prop) (Q : S.Datum → Submodule L.O S.V → Prop), (∀ d Λ, S.IsTerm d Λ → (Q d Λ ↔ ∃ i ∈ s, P i d Λ)) → (∀ d Λ, S.IsTerm d Λ → ∀ i ∈ s, ∀ i' ∈ s, P i d Λ → P i' d Λ → i = i') → S.ampSq Q ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, S.ampSq (P i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ ι s P Q hQ hdisj
  unfold _root_.GlobalTheory.HL.Frames.ampSq _root_.GlobalTheory.HL.Frames.sumData
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (s.card : ℝ≥0∞), mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold _root_.GlobalTheory.HL.Frames.amp
  apply norm_tsum_sq_le_card_mul_sum_sq
  · intro a
    by_cases ht : S.IsTerm (Quotient.out o) (Quotient.out a)
    · by_cases hq : Q (Quotient.out o) (Quotient.out a)
      · obtain ⟨i, hi, hPi⟩ := (hQ _ _ ht).mp hq
        rw [if_pos ⟨ht, hq⟩, Finset.sum_eq_single_of_mem i hi, if_pos ⟨ht, hPi⟩]
        intro j hj hji
        rw [if_neg]
        rintro ⟨-, hPj⟩
        exact hji (hdisj _ _ ht j hj i hi hPj hPi)
      · rw [if_neg (fun h => hq h.2)]
        refine (Finset.sum_eq_zero fun i hi => ?_).symm
        rw [if_neg]
        rintro ⟨-, hPi⟩
        exact hq ((hQ _ _ ht).mpr ⟨i, hi, hPi⟩)
    · rw [if_neg (fun h => ht h.1)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg (fun h => ht h.1)]
  · intro i hi a
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, (hQ _ _ h1.1).mpr ⟨i, hi, h1.2⟩⟩ h2
    · rw [norm_zero]; exact norm_nonneg _
    · simp

end GlobalTheory.AmpCS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBase
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramOrder

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Ideal in
private lemma card_quotient_span_eq_card_residueField_pow_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a}) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {(u : R) * ϖ ^ n} = IsLocalRing.maximalIdeal R ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hm, Ideal.span_singleton_pow]
  have hv : IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u]
    simp
  have hne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [hm, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  rw [hv, hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]
  simp
  rfl


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : M →ₗ[R] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R (LinearMap.det f)).toNat := by
  classical
  let b := Module.Free.chooseBasis R M
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    apply hf
    rw [← LinearMap.det_toMatrix b]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨b.repr x, fun h => hx0 ?_, ?_⟩
    · have h' : b.repr x = 0 := by
        ext i
        exact congrFun h i
      simpa using h'
    · rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero]
      rfl
  have hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hinj
  let T := Submodule.smithNormalFormTopBasis b hrank
  let B := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  let e : M ≃ₗ[R] LinearMap.range f := T.equiv B (Equiv.refl _)
  let g : M →ₗ[R] M := (LinearMap.range f).subtype ∘ₗ e.toLinearMap
  have hgT : ∀ i, g (T i) = a i • T i := by
    intro i
    simp [g, e, Module.Basis.equiv_apply, B, T, a, Submodule.smithNormalFormBotBasis_def]
  have hdetg : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix T]
    have hmat : LinearMap.toMatrix T T g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hgT, map_smul, T.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [hmat, Matrix.det_diagonal]
  let h : M →ₗ[R] M := e.symm.toLinearMap ∘ₗ f.rangeRestrict
  have hfgh : f = g ∘ₗ h := by
    ext x
    simp [g, h]
  have hsurj : Function.Surjective h := e.symm.surjective.comp f.surjective_rangeRestrict
  have hbij : Function.Bijective h :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism h hsurj, hsurj⟩
  have hdeth : IsUnit (LinearMap.det h) := by
    have h1 := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective h hbij)
    have h2 : ((LinearEquiv.ofBijective h hbij : M ≃ₗ[R] M) : M →ₗ[R] M) = h :=
      LinearMap.ext fun _ => rfl
    rwa [h2] at h1
  have hdet : LinearMap.det f = (∏ i, a i) * LinearMap.det h := by
    rw [hfgh, LinearMap.det_comp, hdetg]
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  have key : ∀ s : Finset (Module.Free.ChooseBasisIndex R M),
      (IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i)).toNat =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal R (a i)).toNat := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul,
        ENat.toNat_add, ih]
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha i)
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
          (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range f) b hrank).toEquiv,
    Nat.card_pi]
  rw [Finset.prod_congr rfl fun i _ =>
    card_quotient_span_eq_card_residueField_pow_addVal (Submodule.smithNormalFormCoeffs_ne_zero b hrank i)]
  have hu : IsDiscreteValuationRing.addVal R (LinearMap.det h) = 0 := by
    have h3 := IsDiscreteValuationRing.addVal_eq_zero_of_unit hdeth.unit
    rwa [IsUnit.unit_spec] at h3
  rw [Finset.prod_pow_eq_pow_sum, hdet, IsDiscreteValuationRing.addVal_mul, hu, add_zero]
  exact congrArg _ (key Finset.univ).symm


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.UnramOrder.card_coker_of_det_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = _root_.GlobalTheory.HL.resQ ϖ ^ (2 * j) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ ι _ _ A j u hA
  obtain ⟨-, hO, -, -, hmem, -⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  let φ : 𝒪[F] →+* L.O :=
    { toFun := fun r => ⟨algebraMap F E r, (hmem r).mpr r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hφ : ∀ r : 𝒪[F], ((algebraMap 𝒪[F] L.O r : L.O) : E) = algebraMap F E r := fun r => rfl
  let c : L.O →+* L.O :=
    { toFun := fun x => ⟨L.cj x, (hO x.1 x.2).1⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hc : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun x => rfl
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let ω' : L.O := ⟨ω, hω⟩
  have hunit : IsUnit (ω' - c ω') :=
    isUnit_iff_exists_inv.mpr ⟨⟨e, he⟩, Subtype.ext (by simpa [ω', hc] using hωe)⟩
  have hdecomp := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := 𝒪[F]) c
    (fun x => Subtype.ext (by simp [hc, L.cj_cj]))
    (fun r => Subtype.ext (by simp [hc, hφ]))
    (fun x hx => by
      obtain ⟨r, hr⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext (by rw [hφ, ← hr])⟩) hunit
  have hinjO : Function.Injective (algebraMap 𝒪[F] L.O) := by
    intro r s h
    have h' := congrArg Subtype.val h
    rw [hφ, hφ] at h'
    exact Subtype.ext (_root_.GlobalTheory.UnramOrder.algebraMap_inj L h')
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ω'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hst' := congrArg c hst
    rw [map_add (f := _), map_mul, map_zero] at hst'
    have hfix : ∀ r : 𝒪[F], c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r :=
      fun r => Subtype.ext (by simp [hc, hφ])
    rw [hfix, hfix] at hst'
    have ht0 : algebraMap 𝒪[F] L.O t * (ω' - c ω') = 0 := by
      rw [mul_sub]
      linear_combination hst - hst'
    have ht : t = 0 := hinjO (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp ht0)
    refine ⟨hinjO ?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    rw [hst, map_zero]
  have hspan : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ω']) := by
    intro x _
    obtain ⟨a, b, hx⟩ := hdecomp x
    have hx' : x = a • ![(1 : L.O), ω'] 0 + b • ![(1 : L.O), ω'] 1 := by
      simp [hx, Algebra.smul_def]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bO := Module.Basis.mk hli hspan
  haveI : Module.Free 𝒪[F] L.O := Module.Free.of_basis bO
  haveI : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis bO
  have hrank : Module.finrank 𝒪[F] L.O = 2 := by
    rw [Module.finrank_eq_card_basis bO, Fintype.card_fin]
  have hdetA : A.det = algebraMap 𝒪[F] L.O (ϖ ^ j * (u : 𝒪[F])) := by
    apply Subtype.ext
    rw [hA, hφ]
    push_cast
    rfl
  have hdetf : LinearMap.det (A.mulVecLin.restrictScalars 𝒪[F]) =
      (ϖ ^ j * (u : 𝒪[F])) ^ 2 := by
    rw [LinearMap.det_restrictScalars]
    change Algebra.norm 𝒪[F] (LinearMap.det (Matrix.toLin' A)) = _
    rw [LinearMap.det_toLin', hdetA, Algebra.norm_algebraMap, hrank]
  have hne : (ϖ ^ j * (u : 𝒪[F])) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero)
  have h1 := _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det (A.mulVecLin.restrictScalars 𝒪[F])
    (by rw [hdetf]; exact hne)
  rw [LinearMap.range_restrictScalars,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv] at h1
  rw [h1, hdetf, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u, add_zero]
  have hres : Nat.card (IsLocalRing.ResidueField 𝒪[F]) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  rw [hres]
  congr 1
  simp [mul_comm]

end GlobalTheory.UnramOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FiniteModuleOrder

theorem exists_card_eq_pow (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ _ hn
    rcases subsingleton_or_nontrivial D with h | h
    · exact ⟨0, by simp⟩
    have hfin : Finite (Submodule R D) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top
    have hs : IsSimpleModule R (D ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    subst hI'
    have hc := Submodule.card_eq_card_quotient_mul_card M
    have hnt : Nontrivial (D ⧸ M) := IsSimpleModule.nontrivial R _
    have hf : Finite (D ⧸ M) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
    have h2 : 1 < Nat.card (D ⧸ M) := Finite.one_lt_card
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨i, hi⟩ := ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl
    exact ⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩

theorem card_eq_pow_and_index_ge : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], (∃ i : ℕ, Nat.card D = resQ ϖ ^ i) ∧ ∀ I : Submodule L.O D, I ≠ ⊤ → resQ ϖ * Nat.card I ≤ Nat.card D := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  have key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D],
      ∃ i : ℕ, Nat.card D = resQ ϖ ^ i := by
    intro D _ _ _
    let : Module 𝒪[F] D := Module.compHom D i
    rw [resQ, ← hϖ.maximalIdeal_eq]
    exact exists_card_eq_pow 𝒪[F] _ D rfl
  intro D _ _ _
  refine ⟨key D, fun I hI => ?_⟩
  have hnt : Nontrivial (D ⧸ I) := Submodule.Quotient.nontrivial_iff.2 hI
  have hf : Finite (D ⧸ I) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)
  have h2 : 1 < Nat.card (D ⧸ I) := Finite.one_lt_card
  obtain ⟨j, hj⟩ := key (D ⧸ I)
  have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
  rw [Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)

end GlobalTheory.FiniteModuleOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRingStatement
section
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (k n : ℕ), 2 * k + 1 ≤ 2 * n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.quad_count | exact GlobalTheory.GramCount.quad_count | (intros; apply GlobalTheory.GramCount.quad_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSubmoduleAndHomLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SubmoduleCount

section Abstract

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

end Abstract

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D] in
private theorem exists_finite_generators_of_isPrincipalIdealRing [IsPrincipalIdealRing R] :
    ∀ (g : ℕ) (M : Type) [AddCommGroup M] [Module R M] (x : Fin g → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∀ N : Submodule R M, ∃ v : Fin g → M, N = Submodule.span R (Set.range v) := by
  intro g
  induction g with
  | zero =>
    intro M _ _ x hx N
    refine ⟨Fin.elim0, ?_⟩
    have hbot : (⊤ : Submodule R M) = ⊥ := by
      rw [← hx, Set.range_eq_empty, Submodule.span_empty]
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]
    exact le_top
  | succ g ih =>
    intro M _ _ x hx N
    set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef
    let x' : Fin g → P := fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩
    have hx' : Submodule.span R (Set.range x') = ⊤ := by
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    obtain ⟨w, hw⟩ := ih P x' hx' (N.comap P.subtype)
    set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef
    set a := Submodule.IsPrincipal.generator I
    have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup] at ha
    obtain ⟨n, hn, p, hp, hnp⟩ := ha
    refine ⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩
    · intro m hm
      have hmtop : m ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmtop
      rw [Fin.sum_univ_succ] at hm ⊢
      set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef
      have hq : q ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc0 : c 0 ∈ I := by
        rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
        have := sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)
        simpa using this
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton] at hc0
      obtain ⟨t, ht⟩ := hc0
      have hdiff : c 0 • x 0 + q - t • n = q + t • p := by
        rw [← ht, smul_assoc, ← hnp, smul_add]; abel
      have hdP : c 0 • x 0 + q - t • n ∈ P := by
        rw [hdiff]; exact add_mem hq (Submodule.smul_mem _ _ hp)
      have hdN : c 0 • x 0 + q - t • n ∈ N := sub_mem hm (Submodule.smul_mem _ _ hn)
      have hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w) := hw ▸ hdN
      have hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.succ, by simp⟩
      have h1 := hle hmem
      rw [Submodule.mem_comap, Submodule.coe_subtype] at h1
      have h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M)) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      simpa using add_mem h1 h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hn
      · have : w i ∈ N.comap P.subtype := hw ▸ Submodule.subset_span ⟨i, rfl⟩
        simpa using this


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.SubmoduleCount.card_submodule_and_hom_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by
  intro F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  refine ⟨?_, fun D' _ _ _ => ?_⟩
  · have hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v)) := by
      intro N
      obtain ⟨v, hv⟩ := exists_finite_generators_of_isPrincipalIdealRing g D x hx N
      exact ⟨v, hv.symm⟩
    calc Nat.card (Submodule L.O D) ≤ Nat.card (Fin g → D) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card D ^ g := by simp [Nat.card_fun]
  · have hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i)) := by
      intro f f' h
      exact LinearMap.ext_on_range hx (fun i => congrFun h i)
    calc Nat.card (D →ₗ[L.O] D') ≤ Nat.card (Fin g → D') := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card D' ^ g := by simp [Nat.card_fun]

end GlobalTheory.SubmoduleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubiniStatement
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_prod_fubini : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  first | exact @GlobalTheory.IdxInt.Fubini.cint_prod | exact GlobalTheory.IdxInt.Fubini.cint_prod | (intros; apply GlobalTheory.IdxInt.Fubini.cint_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChangeStatement
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_transport_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (Nice (A.map e.toAddMonoidHom) φ ↔ Nice A (fun w => φ (e w))) ∧ cint (A.map e.toAddMonoidHom) φ = cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (Nice A φ ↔ Nice A' φ) ∧ cint A' φ * (A.relIndex A' : ℂ) = cint A φ * (A'.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.Transport.cint_map_and_change | exact GlobalTheory.IdxInt.Transport.cint_map_and_change | (intros; apply GlobalTheory.IdxInt.Transport.cint_map_and_change <;> assumption)
end

