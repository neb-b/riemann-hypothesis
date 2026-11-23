module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.ExtendNormal

theorem isDominant_fst {P Y₀ Y : Scheme.{0}} (p : P ⟶ Y) (i : Y₀ ⟶ Y) [IsOpenImmersion p] [IsDominant i] :
    IsDominant (pullback.fst p i) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst]
  exact i.denseRange.preimage p.isOpenEmbedding.isOpenMap

theorem glue {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (t₀ : Y₀ ⟶ X) [IsDominant i] [IsReduced Y] [X.IsSeparated]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀) :
    ∃ t : Y ⟶ X, i ≫ t = t₀ := by
  choose U hy t ht using h
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover U hU
  have hc : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ t x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ t y := by
    intro x y
    change pullback.fst (U x).ι (U y).ι ≫ t x = pullback.snd (U x).ι (U y).ι ≫ t y
    let p := pullback.fst (U x).ι (U y).ι ≫ (U x).ι
    have : IsReduced (pullback (U x).ι (U y).ι) := isReduced_of_isOpenImmersion p
    have := isDominant_fst p i
    refine ext_of_isDominant (pullback.fst p i) ?_
    rw [← Category.assoc, ← Category.assoc, ht x _ _ (pullback.snd p i), ht y _ _ (pullback.snd p i)]
    · rw [Category.assoc, ← pullback.condition]
      exact pullback.condition
    · rw [Category.assoc]
      exact pullback.condition
  refine ⟨𝒰.glueMorphisms t hc, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ i) _ _ fun y => ?_
  have e := 𝒰.ι_glueMorphisms t hc y
  change pullback.fst i (𝒰.f y) ≫ _ = pullback.fst i (𝒰.f y) ≫ _
  rw [pullback.condition_assoc, e]
  exact ht y _ _ _ pullback.condition.symm

theorem exists_eq_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (A : CommRingCat.{0})
    (z : Spec A ⟶ X) (hz : ∀ p, z p ∈ W) : ∃ ψ : Γ(X, W) ⟶ A, Spec.map ψ ≫ hW.fromSpec = z := by
  have hr : Set.range z ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact hz p
  exact ⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec z hr), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

theorem exists_extension_local {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (O K : Type) [CommRing O]
    [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K]
    [IsFractionRing O K] (x : Sp K ⟶ X)
    (h : ∀ (V : ValuationSubring K) [IsDiscreteValuationRing V] (hV : ∀ r, algebraMap O K r ∈ V),
      IsLocalHom ((algebraMap O K).codRestrict V hV) →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ g : Sp O ⟶ X, spMap (algebraMap O K) ≫ g = x := by
  have h' : ∀ (V : ValuationSubring K), IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap O K) ≤ V.toLocalSubring →
      ∃ ψ : Γ(X, W) ⟶ CommRingCat.of V, Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap V K)) ≫ hW.fromSpec = x := by
    intro V hV hle
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp hle
    obtain ⟨z, hz, hzW⟩ := h V h1 h2
    obtain ⟨ψ, rfl⟩ := exists_eq_fromSpec hW _ z fun p =>
      ((IsLocalRing.specializes_closedPoint p).map z.continuous).mem_open W.isOpen hzW
    exact ⟨ψ, by rw [Spec.map_comp, Category.assoc, ← hz]⟩
  by_cases hO : IsField O
  · have hb : Function.Bijective (algebraMap O K) :=
      ⟨IsFractionRing.injective O K, IsFractionRing.surjective_iff_isField.mpr hO⟩
    have : IsIso (CommRingCat.ofHom (algebraMap O K)) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
    exact ⟨inv (spMap (algebraMap O K)) ≫ x, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨V₀, hV₀, hle₀⟩ := exists_discreteValuationSubring_dominating O K K hO
  obtain ⟨ψ₀, hψ₀⟩ := h' V₀ hV₀ hle₀
  set φ := ψ₀ ≫ CommRingCat.ofHom (algebraMap V₀ K) with hφ
  have hmem : ∀ b, φ.hom b ∈ (algebraMap O K).range := by
    intro b
    rw [range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]
    rintro ⟨V, h1, h2⟩
    obtain ⟨ψ, hψ⟩ := h' V h1 h2
    rw [← hψ₀, cancel_mono] at hψ
    rw [← Spec.map_injective hψ]
    exact (ψ.hom b).2
  let e : O ≃+* (algebraMap O K).range :=
    RingEquiv.ofBijective (algebraMap O K).rangeRestrict
      ⟨fun a b hab => IsFractionRing.injective O K (congrArg Subtype.val hab),
        (algebraMap O K).rangeRestrict_surjective⟩
  let φ' : Γ(X, W) →+* O := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  refine ⟨Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec, ?_⟩
  rw [← hψ₀, ← Spec.map_comp_assoc]
  congr 2
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom b, hmem b⟩)

theorem isDominant_spMap (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] :
    IsDominant (spMap (algebraMap O K)) := by
  refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
  exact ((RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O K)).le.trans bot_le

theorem exists_nhds_specializes {Y : Scheme.{0}} [IsLocallyNoetherian Y] (y : Y) [IsDomain (Y.presheaf.stalk y)]
    (V : Y.Opens) (hy : y ∈ V) :
    ∃ U : Y.Opens, y ∈ U ∧ U ≤ V ∧
      ∀ u ∈ U, Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y)) ⤳ u := by
  obtain ⟨U, hyU, hU, hUV, hinj⟩ := Y.exists_le_and_germ_injective y V hy
  have : IsDomain Γ(Y, U) := hinj.isDomain _
  refine ⟨U, hyU, hUV, fun u hu => ?_⟩
  have key : ∀ v ∈ U, hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ⤳ v := by
    intro v hv
    obtain ⟨q, rfl⟩ : v ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hv
    exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map hU.fromSpec.continuous
  obtain ⟨q, hq⟩ : hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact key y hyU
  refine Specializes.trans ?_ (key u hu)
  rw [← hq]
  exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map (Y.fromSpecStalk y).continuous

theorem spMap_apply_eq_bot (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (p : Sp K) : spMap (algebraMap O K) p = (⊥ : PrimeSpectrum O) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (algebraMap O K) p.asIdeal = ⊥
  have hp : Ideal.IsPrime (α := K) p.asIdeal := p.isPrime
  rw [Ideal.eq_bot_of_prime (K := K) p.asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)

theorem exists_extension_nhds {R : Type} [CommRing R] {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R)
    (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X) [IsOpenImmersion i] [IsDominant i] [IsLocallyNoetherian Y] [IsReduced Y]
    [X.IsSeparated] [LocallyOfFiniteType τ] (hc : i ≫ σ = t₀ ≫ τ) (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsIntegrallyClosed (Y.presheaf.stalk y)] {W : X.Opens} (hW : IsAffineOpen W)
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y' : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i →
      y' (IsLocalRing.closedPoint V) = y →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀ ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀ := by
  let O : Type := Y.presheaf.stalk y
  let K : Type := FractionRing O
  let j : Sp K ⟶ Spec (Y.presheaf.stalk y) := spMap (algebraMap O K)
  have hjd : IsDominant j := isDominant_spMap O K
  let ξ : Y := Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y))
  have hgen : ∀ p, (j ≫ Y.fromSpecStalk y) p = ξ := fun p =>
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.fromSpecStalk y) (spMap_apply_eq_bot O K p))
  have hgi : ξ ∈ Set.range i := by
    obtain ⟨U, hyU, -, hU⟩ := exists_nhds_specializes y ⊤ trivial
    obtain ⟨u, hu⟩ := i.denseRange.exists_mem_open U.isOpen ⟨y, hyU⟩
    exact (hU _ hu).mem_open i.isOpenEmbedding.isOpen_range ⟨u, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Sp K ⟶ Y₀, x ≫ i = j ≫ Y.fromSpecStalk y :=
    ⟨_, IsOpenImmersion.lift_fac i (j ≫ Y.fromSpecStalk y) (by rintro _ ⟨p, rfl⟩; rw [hgen]; exact hgi)⟩
  obtain ⟨g, hg⟩ : ∃ g : Spec (Y.presheaf.stalk y) ⟶ X, j ≫ g = x ≫ t₀ := by
    refine exists_extension_local hW O K (x ≫ t₀) fun V _ hV hloc => ?_
    let k : Sp V ⟶ Spec (Y.presheaf.stalk y) := spMap ((algebraMap O K).codRestrict V hV)
    refine h V K (k ≫ Y.fromSpecStalk y) x ?_ ?_
    · rw [hx, ← Category.assoc]
      congr 1
      exact (Spec.map_comp _ _).symm
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (Y.fromSpecStalk y) ?_) (Scheme.fromSpecStalk_closedPoint (x := y)))
      exact IsLocalRing.comap_closedPoint ((algebraMap O K).codRestrict V hV)
  have hgτ : g ≫ τ = Y.fromSpecStalk y ≫ σ := by
    refine ext_of_isDominant j ?_
    rw [reassoc_of% hg, ← reassoc_of% hx, hc]
  obtain ⟨U₁, hy₁, t₁, ht₁, -⟩ := spread_out_of_isGermInjective' σ τ g hgτ
  obtain ⟨U, hyU, hle, hU⟩ := exists_nhds_specializes y U₁ hy₁
  refine ⟨U, hyU, Y.homOfLE hle ≫ t₁, fun T a b hab => ?_⟩
  have hw : (j ≫ U.fromSpecStalkOfMem y hyU) ≫ U.ι = x ≫ i := by simp [hx]
  let w : Sp K ⟶ pullback U.ι i := pullback.lift _ _ hw
  let p : pullback U.ι i ⟶ Y := pullback.fst U.ι i ≫ U.ι
  have hwp : w ≫ p = j ≫ Y.fromSpecStalk y := by
    rw [← hx, ← hw]
    exact pullback.lift_fst_assoc _ _ hw _
  have : IsReduced (pullback U.ι i) := isReduced_of_isOpenImmersion p
  have : IsDominant w := by
    refine ⟨fun q => ?_⟩
    have h1 : w (IsLocalRing.closedPoint K) ⤳ q := by
      have h0 : p (w (IsLocalRing.closedPoint K)) = ξ :=
        (Scheme.Hom.comp_apply w p _).symm.trans (by rw [hwp]; exact hgen _)
      rw [← p.isOpenEmbedding.isInducing.specializes_iff, h0]
      exact hU _ (pullback.fst U.ι i q).2
    exact h1.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  have e : pullback.fst U.ι i ≫ Y.homOfLE hle ≫ t₁ = pullback.snd U.ι i ≫ t₀ := by
    refine ext_of_isDominant w ?_
    have h2 : U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hle = U₁.fromSpecStalkOfMem y hy₁ := by
      rw [← cancel_mono U₁.ι]; simp
    simp only [w, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% h2, ← ht₁, hg]
  rw [← pullback.lift_fst a b hab, Category.assoc, e, pullback.lift_snd_assoc]

theorem exists_extension : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  intro R _ _ Y₀ Y X i σ τ t₀ hi hd hY hred hint hq hc hval hqf
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  have hfin := GlobalTheory.FiniteSubsetsInAffineOpens.of_isQProjOver hq
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from τ]; infer_instance⟩
  obtain ⟨t, ht⟩ := glue i t₀ fun y => by
    have := hint y
    have : IsDomain (Y.presheaf.stalk y) := GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced _ (hint y)
    obtain ⟨W, hW, hSW⟩ := hfin.exists_isAffineOpen _ (hqf y)
    exact exists_extension_nhds i σ τ t₀ hc y hW fun V K _ _ _ _ _ _ y' x hx hy => by
      obtain ⟨z, hz⟩ := hval V K y' x hx
      exact ⟨z, hz, hSW ⟨V, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, y', z, x, hx, hz, hy, rfl⟩⟩
  refine ⟨t, ht, ext_of_isDominant i ?_⟩
  rw [reassoc_of% ht, hc]

end GlobalTheory.ExtendNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def lowerWedge :
    (I →₀ R) →ₗ[R] (I →₀ R) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  Finsupp.linearCombination R (fun i => Finsupp.linearCombination R (fun j =>
    if i < j then exteriorPower.ιMulti R 2 ![Finsupp.single i 1, Finsupp.single j 1] else 0))

noncomputable def wedgeBil {M : Type} [AddCommGroup M] [Module R M] :
    M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun x y => exteriorPower.ιMulti R 2 ![x, y])
    (fun x x' y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![y] x x')
    (fun c x y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![y] c x)
    (fun x y y' => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![y + y', x] = exteriorPower.ιMulti R 2 ![y, x] + exteriorPower.ιMulti R 2 ![y', x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![x] y y'
      rw [h (y + y') x, h y x, h y' x, h1, neg_add])
    (fun c x y => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![c • y, x] = c • exteriorPower.ιMulti R 2 ![y, x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![x] c y
      rw [h (c • y) x, h y x, h1, smul_neg])

theorem wedgeBil_apply {M : Type} [AddCommGroup M] [Module R M] (x y : M) :
    wedgeBil x y = exteriorPower.ιMulti R 2 ![x, y] := rfl

theorem lowerWedge_sub_flip :
    lowerWedge (R := R) (I := I) - lowerWedge.flip = wedgeBil (M := I →₀ R) := by
  ext i j
  simp only [lowerWedge, LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.smul_apply, wedgeBil_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp only [lt_irrefl, if_false, sub_zero]
    exact congrArg _ ((exteriorPower.ιMulti R 2 (M := I →₀ R)).map_eq_zero_of_eq ![Finsupp.single i 1, Finsupp.single i 1] (i := 0) (j := 1) rfl (by decide)).symm
  · have hs := (exteriorPower.ιMulti R 2).map_swap ![Finsupp.single j (1:R), Finsupp.single i 1] (i := 0) (j := 1) (by decide)
    have e : ![Finsupp.single j (1:R), Finsupp.single i 1] ∘ Equiv.swap 0 1 = ![Finsupp.single i 1, Finsupp.single j 1] := by
      ext k; fin_cases k <;> rfl
    rw [e] at hs
    simp [h, h.not_gt, hs]

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def crossWedge :
    ((I →₀ R) × (I →₀ R)) [⋀^Fin 2]→ₗ[R] ⋀[R]^2 (I →₀ R) where
  toFun v := lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update_of_ne, map_add (f := _), LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update_of_ne, map_smul, LinearMap.smul_apply, smul_sub]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem crossWedge_apply (v : Fin 2 → (I →₀ R) × (I →₀ R)) :
    crossWedge v = lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2 := rfl

noncomputable def crossWedgeLin : ⋀[R]^2 ((I →₀ R) × (I →₀ R)) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  exteriorPower.alternatingMapLinearEquiv crossWedge

theorem crossWedgeLin_inl :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_inr :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_diag :
    crossWedgeLin ∘ₗ exteriorPower.map 2
      (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) = LinearMap.id := by
  ext v
  have h := LinearMap.congr_fun₂ (lowerWedge_sub_flip (R := R) (I := I)) (v 0) (v 1)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, wedgeBil_apply] at h
  have hv : ![v 0, v 1] = v := by ext k; fin_cases k <;> rfl
  rw [hv] at h
  simp [crossWedgeLin, crossWedge_apply, h]

theorem free_case (t : ⋀[R]^2 (I →₀ R))
    (H : exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) t =
      exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) t +
        exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) t) : t = 0 := by
  have h := congrArg crossWedgeLin H
  rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply crossWedgeLin, ← LinearMap.comp_apply crossWedgeLin,
    crossWedgeLin_diag, crossWedgeLin_inl, crossWedgeLin_inr] at h
  simpa using h

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

theorem eq_zero_of_diag_additive : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  intro R M _ _ _ _ t H
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  letI : LinearOrder M := IsWellOrder.linearOrder WellOrderingRel
  set p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have e0 : (LinearMap.inl R (M →₀ R) (M →₀ R) + LinearMap.inr R (M →₀ R) (M →₀ R)) ∘ₗ s =
      (s.prodMap s) ∘ₗ (LinearMap.inl R M M + LinearMap.inr R M M) := by
    ext x <;> simp
  have e1 : (s.prodMap s) ∘ₗ LinearMap.inl R M M = LinearMap.inl R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have e2 : (s.prodMap s) ∘ₗ LinearMap.inr R M M = LinearMap.inr R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have hu : exteriorPower.map 2 s t = 0 := by
    apply free_case
    have h := congrArg (exteriorPower.map 2 (s.prodMap s)) H
    rw [map_add (f := _)] at h
    simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp] at h ⊢
    rw [e0, ← e1, ← e2]
    exact h
  have := congrArg (exteriorPower.map 2 p) hu
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hs, exteriorPower.map_id, map_zero] at this
  exact this

end GlobalTheory.WedgeDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSnd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem finite_dvr_limits_of_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X)
    (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt →
    ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro X Y₀ S q U s₀ t₀ gt hq hS _ hgt hfin z hz
  refine ((gt.finite_preimage_singleton ⟨z, hz⟩).image s₀).subset ?_
  rintro u ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, rfl, rfl⟩

  have hr : Set.range z' ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map z'.continuous).mem_open U.isOpen hz
  set z'' := IsOpenImmersion.lift U.ι z' hr with hz''
  have hfac : z'' ≫ U.ι = z' := IsOpenImmersion.lift_fac _ _ _

  have hsq : x ≫ gt = spMap (algebraMap V K) ≫ z'' := by
    rw [← cancel_mono U.ι, Category.assoc, hgt, Category.assoc, hfac, h2]
  have hE : ValuativeCriterion.Existence gt :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gt) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gt).1
  obtain ⟨l, hl1, hl2⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z'', commSq := ⟨hsq⟩ }).exists_lift
  dsimp only at hl1 hl2

  have hU := IsSeparated.valuativeCriterion (q ≫ terminal.from S)
  have hsq' : (x ≫ s₀) ≫ (q ≫ terminal.from S) = spMap (algebraMap V K) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have hy : y' = l ≫ s₀ := by
    have := hU { R := V, K := K, i₁ := x ≫ s₀, i₂ := terminal.from _, commSq := ⟨hsq'⟩ }
    have e := this.elim ⟨y', h1, terminal.hom_ext _ _⟩
      ⟨l ≫ s₀, by change spMap (algebraMap V K) ≫ l ≫ s₀ = x ≫ s₀; rw [← Category.assoc, hl1], terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l e
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · show gt (l _) = _
    apply Subtype.ext
    change (l ≫ gt ≫ U.ι) _ = z' _
    rw [← Category.assoc, hl2, hfac]
  · rw [hy]; rfl

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFaithfullyFlatAlgebraOverAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory

theorem finiteFlatSurj_affine_algebra : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (V₀ : Y.Opens), IsAffineOpen V₀ →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    IsNoetherianRing Γ(Y, V₀) ∧ Module.Finite Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) ∧ Module.FaithfullyFlat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := by
  intro X Y f _ _ _ _ V₀ hV₀
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  refine ⟨IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩, ?_, ?_⟩
  · exact IsFinite.finite_app f V₀ hV₀
  · have hflat : (f.app V₀).hom.Flat := by
      have := Flat.flat_appLE f hV₀ hV le_rfl
      rwa [Scheme.Hom.appLE_eq_app] at this
    haveI : Module.Flat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := hflat
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV₀ hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hsq
    have hy : hV₀.fromSpec p ∈ (V₀ : Set Y) := by
      rw [← hV₀.range_fromSpec]; exact ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := f.surjective (hV₀.fromSpec p)
    have hxV : x ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      show f x ∈ (V₀ : Set Y)
      rw [hx]; exact hy
    obtain ⟨q, rfl⟩ := hxV
    refine ⟨q, ?_⟩
    apply hV₀.fromSpec.isOpenEmbedding.injective
    have := congrArg (fun g => g q) (congrArg (fun h => h.base) hsq)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [← hx]
    convert this using 2
    rw [Spec.map_base]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.AbTorsionGeomDescent

theorem finite_torsion_and_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  intro k _ _ A _ _ hA n hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h, Nat.cast_zero]) hn
    · exact h
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.TorusExtTorsion.finite_torsion_abelian_geomPoint A hA k (𝟙 _) n hn1
  · intro κ _ _ x g hg
    letI : Algebra k κ := (Spec.preimage x).hom.toAlgebra
    have hx : x = spMap (algebraMap k κ) := by
      show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨g₀, hg₀, hgl⟩ := GlobalTheory.AlgClosedDescent.torsion_descent (K := κ) A hA n hn hx g hg
    refine ⟨g₀, hg₀, ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hgl]
    congr 1

end GlobalTheory.AbTorsionGeomDescent
end

