module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_opens_preimage_le_of_isClosedMap {F Y : Scheme.{0}} (φ : F ⟶ Y) (hφ : IsClosedMap φ) (y : Y)
    (T : F.Opens) (hT : ∀ p, φ p = y → p ∈ T) : ∃ N : Y.Opens, y ∈ N ∧ φ ⁻¹ᵁ N ≤ T := by
  refine ⟨⟨(φ '' (T : Set F)ᶜ)ᶜ, (hφ _ T.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, e⟩
    exact hp (hT p e)
  · intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩

theorem exists_basicOpen_le_of_finite {A : Type} [CommRing A] (s : Set (PrimeSpectrum A)) (hs : s.Finite)
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ b : A, s ⊆ PrimeSpectrum.basicOpen b ∧ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  by_cases hne : s = ∅
  · subst hne
    exact ⟨0, by simp, by simp⟩
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  have key : ¬ ((I : Set A) ⊆ ⋃ i ∈ s, (i.asIdeal : Set A)) := by
    rw [Ideal.subset_union_prime_finite hs a a (fun i _ _ _ => i.2)]
    rintro ⟨i, hi, hle⟩
    have : i ∈ Uᶜ := by rw [hI]; exact hle
    exact this (hsU hi)
  obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 key
  refine ⟨b, fun i hi h => hb' (Set.mem_iUnion₂.2 ⟨i, hi, h⟩), fun i hi => ?_⟩
  by_contra h
  have : i ∈ PrimeSpectrum.zeroLocus (I : Set A) := hI ▸ h
  exact hi (this hb)

theorem exists_basicOpen_le_of_finite' {G : Scheme.{0}} {W : G.Opens} (hW : IsAffineOpen W) (s : Set G) (hs : s.Finite)
    (hsW : s ⊆ W) (U : G.Opens) (hsU : s ⊆ U) : ∃ b : Γ(G, W), s ⊆ G.basicOpen b ∧ G.basicOpen b ≤ U := by
  obtain ⟨b, h₁, h₂⟩ := exists_basicOpen_le_of_finite (A := Γ(G, W)) (hW.fromSpec ⁻¹' s)
    (hs.preimage hW.fromSpec.isOpenEmbedding.injective.injOn) _
    (hW.fromSpec ⁻¹ᵁ U).2 (fun p hp => hsU hp)
  refine ⟨b, fun p hp => ?_, ?_⟩
  · have : p ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hsW hp
    obtain ⟨q, rfl⟩ := this
    rw [← hW.fromSpec_image_basicOpen]
    exact ⟨q, h₁ hp, rfl⟩
  · rw [← hW.fromSpec_image_basicOpen]
    rintro _ ⟨q, hq, rfl⟩
    exact h₂ hq

theorem exists_affine_preimage_eq_basicOpen {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {W : G.Opens} (hW : IsAffineOpen W) (y : Y) (hfin : (κ '' {p | φ p = y}).Finite)
    (hy : ∀ p, φ p = y → κ p ∈ W) :
    ∃ (O : Y.Opens) (b : Γ(G, W)), y ∈ O ∧ IsAffineOpen O ∧ φ ⁻¹ᵁ O = κ ⁻¹ᵁ G.basicOpen b := by
  obtain ⟨N, hyN, hN⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ W) hy
  obtain ⟨_, ⟨O₁, hO₁, rfl⟩, hyO₁, hO₁N⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyN N.2
  let U : G.Opens := ⟨(κ '' ((φ ⁻¹ᵁ O₁ : F.Opens) : Set F)ᶜ)ᶜ,
    (κ.isClosedEmbedding.isClosedMap _ (φ ⁻¹ᵁ O₁).2.isClosed_compl).isOpen_compl⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_basicOpen_le_of_finite' hW _ hfin (by rintro _ ⟨p, hp, rfl⟩; exact hy p hp) U (by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
    obtain rfl := κ.isClosedEmbedding.injective e
    apply hq
    change φ q ∈ O₁
    rw [hp]; exact hyO₁)
  have hle : κ ⁻¹ᵁ G.basicOpen b₁ ≤ φ ⁻¹ᵁ O₁ := fun p hp => by
    by_contra h
    exact hb₁' hp ⟨p, h, rfl⟩
  obtain ⟨N₂, hyN₂, hN₂⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ G.basicOpen b₁)
    (fun p hp => hb₁ ⟨p, hp, rfl⟩)
  obtain ⟨g, hg, hyg⟩ := IsAffineOpen.exists_basicOpen_le hO₁ (V := N₂) ⟨y, hyN₂⟩ hyO₁
  have hS : IsAffineOpen (κ ⁻¹ᵁ W) := hW.preimage κ
  rw [Scheme.preimage_basicOpen] at hle hN₂
  obtain ⟨s, hs⟩ := hS.basicOpen_basicOpen_is_basicOpen (κ.app W b₁) (φ.appLE O₁ _ hle g)
  obtain ⟨b, rfl⟩ := κ.app_surjective W hW s
  refine ⟨Y.basicOpen g, b, hyg, hO₁.basicOpen g, ?_⟩
  rw [Scheme.preimage_basicOpen κ, hs, Scheme.basicOpen_appLE, eq_comm, inf_eq_right]
  exact fun p hp => hN₂ (hg hp)

theorem exists_affine_preimage_iff_not_mem {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {A : Type} [CommRing A] (J : Sp A ⟶ G) [IsOpenImmersion J] (y : Y)
    (hfin : (κ '' {p | φ p = y}).Finite) (hy : ∀ p, φ p = y → κ p ∈ Set.range J) :
    ∃ (O : Y.Opens) (b : A), y ∈ O ∧ IsAffineOpen O ∧
      ∀ p, φ p ∈ O ↔ ∃ q : PrimeSpectrum A, J q = κ p ∧ b ∉ q.asIdeal := by
  obtain ⟨O, b, h₁, h₂, h₃⟩ := exists_affine_preimage_eq_basicOpen κ φ hφ (isAffineOpen_opensRange J) y hfin hy
  have e : (⊤ : (Sp A).Opens) ≤ J ⁻¹ᵁ J.opensRange := fun q _ => ⟨q, rfl⟩
  refine ⟨O, (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b), h₁, h₂, fun p => ?_⟩
  have h₄ := basicOpen_eq_of_affine' (R := .of A) (J.appLE _ _ e b)
  rw [Scheme.basicOpen_appLE, top_inf_eq] at h₄
  have h₅ : ∀ q : PrimeSpectrum A, J q ∈ G.basicOpen b ↔
      (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b) ∉ q.asIdeal := fun q => by
    change q ∈ J ⁻¹ᵁ G.basicOpen b ↔ _
    rw [h₄]; rfl
  change p ∈ φ ⁻¹ᵁ O ↔ _
  rw [h₃]
  change κ p ∈ G.basicOpen b ↔ _
  constructor
  · intro h
    obtain ⟨q, hq⟩ := G.basicOpen_le b h
    exact ⟨q, hq, (h₅ q).1 (by rw [hq]; exact h)⟩
  · rintro ⟨q, hq, h⟩
    rw [← hq]; exact (h₅ q).2 h

theorem exists_act_eq_of_apply_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (hG : IsGal (algebraMap R R')) {F G T : Scheme.{0}} (t : T ⟶ Sp R')
    [IsClosedImmersion t] (κ : F ⟶ G) (gm : G ⟶ Sp R') (s : F ⟶ T) (hs : κ ≫ gm = s ≫ t)
    (act : Gal (algebraMap R R') → (G ⟶ G)) (hact : ∀ σ, act σ ≫ gm = gm ≫ spMap (Gal.hom σ)) (Y : Over (Sp R))
    (hY : Flat Y.hom) (φ : F ⟶ Y.left) (hφ : IsPullback φ s Y.hom (t ≫ spMap (algebraMap R R')))
    (hinv : ∀ σ, ∃ h : F ⟶ F, h ≫ κ = κ ≫ act σ ∧ h ≫ φ = φ) (p q : F) (e : φ p = φ q) :
    ∃ σ, act σ (κ p) = κ q := by
  let u : F ⟶ pullback Y.hom (spMap (algebraMap R R')) := pullback.lift φ (s ≫ t) (by rw [hφ.w, Category.assoc])
  have hu₁ : u ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd _ _ = s ≫ t := pullback.lift_snd _ _ _
  have hu : IsPullback s u t (pullback.snd Y.hom (spMap (algebraMap R R'))) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) ?_ hu₂.symm (IsPullback.of_hasPullback _ _).flip
    rw [hu₁]; exact hφ.flip
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hu inferInstance
  obtain ⟨σ, h, h₁, h₂, h₃⟩ := _root_.GlobalTheory.Mum.gal_transitive_on_fibres R R' hinj hG Y hY _ _ _ (IsPullback.of_hasPullback _ _) (u p) (u q) (by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hu₁, e])
  obtain ⟨k, k₁, k₂⟩ := hinv σ
  have hk : k ≫ u = u ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, hu₁, k₂]
    · rw [Category.assoc, Category.assoc, h₂, hu₂, ← Category.assoc u, hu₂, ← hs, ← Category.assoc k, k₁, Category.assoc,
        hact, Category.assoc]
  have hkp : k p = q := u.isClosedEmbedding.injective (by
    rw [← h₃, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk])
  exact ⟨σ, by rw [← hkp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, k₁]⟩

theorem mem_range_thick_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R')
    (hρ : ρ.Finite) (P : Sp R') (hP : spMap ρ P = closedPoint R) (e : ℕ) :
    P ∈ Set.range (thick R' (maximalIdeal R') e) := by
  have h₁ : (P.asIdeal.comap ρ).IsMaximal := by
    have : P.asIdeal.comap ρ = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hP
    rw [this]; infer_instance
  have := P.2
  have h₂ : P.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ h₁
  have h₃ : P.asIdeal = maximalIdeal R' := eq_maximalIdeal h₂
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R' ^ (e + 1))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  intro a ha
  change a ∈ P.asIdeal
  rw [h₃]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e) ha

theorem exists_affine_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  intro R _ _ _ R' _ _ _ _ hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec Y φ hY hφ _ hh x hx
  have := hG.1
  have := Fintype.ofFinite (Gal (algebraMap R R'))
  have hx₀ : H.ι x ∈ Set.range (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := by
    rw [Scheme.Pullback.range_fst]
    exact mem_range_thick_of_finite _ hF.2.2 _ hx 0
  obtain ⟨x₀, hx₀⟩ := hx₀
  have ht : IsClosedImmersion (thick R' (maximalIdeal R') 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hρ : IsFinite (spMap (algebraMap R R')) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hfin : IsFinite (φ 0) := MorphismProperty.of_isPullback (P := @IsFinite) (hφ 0).flip inferInstance
  have orb := exists_act_eq_of_apply_eq hF.2.1 hG (thick R' (maximalIdeal R') 0)
    (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) G'.hom _ pullback.condition act hact Y inferInstance (φ 0) (hφ 0) (hh 0)
  have hh₀ := hh 0
  have hκ : IsClosedImmersion (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := inferInstance
  generalize pullback.fst G'.hom (thick R' (maximalIdeal R') 0) = κ at *
  obtain ⟨_, ⟨V₁, hV₁, rfl⟩, hxV₁, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlr, hpb, -, -, hcomm, -, hC⟩ :=
    _root_.GlobalTheory.Mum.quot_affine_spec_invariants R R' hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec V₁ hV₁
  have lift : ∀ (z : H.toScheme) (w : Sp C), π z = l w → ∃ q : Sp C', j q = z ∧ spMap (algebraMap C C') q = w :=
    fun z w e => Scheme.exists_preimage_of_isPullback hpb z w e
  have hw : ∀ q, π (j q) = l (spMap (algebraMap C C') q) := fun q => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have hc : ∀ σ q, (j ≫ H.ι) (spMap (actC σ : C' →+* C') q) = act σ ((j ≫ H.ι) q) := fun σ q => by
    rw [← Scheme.Hom.comp_apply, hcomm, ← Scheme.Hom.comp_apply, Category.assoc]
  obtain ⟨w₀, hw₀⟩ : π x ∈ Set.range l := by rw [hlr]; exact hxV₁
  obtain ⟨q₀, hq₀, -⟩ := lift x w₀ hw₀.symm
  have hq₀' : (j ≫ H.ι) q₀ = κ x₀ := by rw [Scheme.Hom.comp_apply, hq₀, hx₀]
  obtain ⟨O, b, hyO, hO, hb⟩ := exists_affine_preimage_iff_not_mem κ (φ 0) (φ 0).isClosedMap (j ≫ H.ι) (φ 0 x₀)
    ((Set.finite_range fun σ => act σ (κ x₀)).subset (by
      rintro _ ⟨p, hp, rfl⟩
      exact orb x₀ p hp.symm))
    (fun p hp => by
      obtain ⟨σ, hσ⟩ := orb x₀ p hp.symm
      exact ⟨_, (hc σ q₀).trans (by rw [hq₀', hσ])⟩)
  let c : C := ⟨∏ σ, actC σ b, (hC _).2 fun τ => by
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => by simp⟩
  have key : ∀ p, φ 0 p ∈ O ↔ ∃ q : PrimeSpectrum C', (j ≫ H.ι) q = κ p ∧ (c : C') ∉ q.asIdeal := fun p => by
    constructor
    · intro hp
      obtain ⟨q, hq, -⟩ := (hb p).1 hp
      refine ⟨q, hq, fun hm => ?_⟩
      obtain ⟨σ, -, hσ⟩ := (q.2.prod_mem_iff).1 hm
      obtain ⟨k, k₁, k₂⟩ := hh₀ σ
      obtain ⟨q', hq', hb'⟩ := (hb (k p)).1 (by rw [← Scheme.Hom.comp_apply, k₂]; exact hp)
      have : q' = spMap (actC σ : C' →+* C') q := (j ≫ H.ι).isOpenEmbedding.injective
        ((hq'.trans (by rw [hq, ← Scheme.Hom.comp_apply k κ, k₁, Scheme.Hom.comp_apply])).trans (hc σ q).symm)
      rw [this] at hb'
      exact hb' hσ
    · rintro ⟨q, hq, hm⟩
      refine (hb p).2 ⟨q, hq, fun hm' => hm ?_⟩
      exact (q.2.prod_mem_iff).2 ⟨1, Finset.mem_univ _, by simpa using hm'⟩
  have key₂ : ∀ z : H.toScheme, π z ∈ l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens) ↔
      ∃ q : PrimeSpectrum C', j q = z ∧ (c : C') ∉ q.asIdeal := fun z => by
    constructor
    · rintro ⟨w, hw', e⟩
      obtain ⟨q, hq, rfl⟩ := lift z w e.symm
      exact ⟨q, hq, hw'⟩
    · rintro ⟨q, rfl, hq⟩
      exact ⟨_, hq, (hw q).symm⟩
  refine ⟨l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens), O, ?_, ?_, hO, ?_⟩
  · obtain ⟨q, hq, hm⟩ := (key x₀).1 hyO
    refine (key₂ x).2 ⟨q, H.ι.isOpenEmbedding.injective ?_, hm⟩
    rw [← hx₀, ← hq]; exact (Scheme.Hom.comp_apply _ _ _).symm
  · refine IsAffineOpen.image_of_isOpenImmersion ?_ l
    rw [← basicOpen_eq_of_affine (R := .of C)]
    exact (isAffineOpen_top _).basicOpen _
  · ext p
    refine (key p).trans ⟨?_, ?_⟩
    · rintro ⟨q, hq, hm⟩
      exact ⟨j q, (key₂ _).2 ⟨q, rfl, hm⟩, hq⟩
    · rintro ⟨z, hz, e⟩
      obtain ⟨q, rfl, hm⟩ := (key₂ z).1 hz
      exact ⟨q, e, hm⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenSpread

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} (hF : FormEq φ₁ ε₁ φ₂ ε₂)
    {t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t₁ r z J * (val t₂ r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 (hF U h))
    (LB.mulGen L _ _ _ _ t₁ (LB.invGen L _ _ t₂)) (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ (DVR.invGen_isGen _ _ _ _ h₂))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

def fnOn {R : Type} [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Sp S) (a : R) :
    gs (spMap f) z ⊤ (fnOn a) = gs (𝟙 (Sp S)) z ⊤ (fnOn (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have := gs_pull (𝟙 (Sp S)) (spMap f) z ⊤ trivial (fnOn a)
  rw [Category.id_comp] at this
  rw [← this]
  exact congrArg (gs (𝟙 (Sp S)) z ⊤) e.symm

def gsHom {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom

theorem gsHom_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gsHom r z a = gs r z ⊤ a :=
  (gs_eq r z ⊤ trivial a).symm

theorem gs_res_fn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (W : (Sp R).Opens) (r : Sp S ⟶ W.toScheme)
    (hr : r ≫ W.ι = spMap f) (z : Sp S) (a : R) :
    gsHom r z (W.ι.appTop.hom (fnOn a)) = gsHom (𝟙 (Sp S)) z (fnOn (f a)) := by
  rw [gsHom_apply, gsHom_apply, ← gs_spMap, ← hr]
  exact gs_pull r W.ι z ⊤ trivial _

theorem eq_zero_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens)
    (lam : Sp (FractionRing R) ⟶ W.toScheme) (hl : lam ≫ W.ι = jK R) (z : Sp (FractionRing R))
    (d : Γ(W.toScheme, ⊤)) (hd : gsHom lam z d = 0) : d = 0 := by
  haveI : AlgebraicGeometry.IsReduced W.toScheme := isReduced_of_isOpenImmersion W.ι
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ W.toScheme.basicOpen d := by
    by_contra h
    exact hne (le_bot_iff.1 fun w hw => h ⟨w, hw⟩)
  have hsp : W.ι (lam z) ⤳ W.ι w := by
    have e : W.ι (lam z) = jK R z := by rw [← hl]; rfl
    rw [e]
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have hz : (z : PrimeSpectrum (FractionRing R)).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime z).ne_top
    have ha' : algebraMap R (FractionRing R) a ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := ha
    rw [hz, Ideal.mem_bot] at ha'
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (ha'.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  have hsp' : lam z ⤳ w := W.ι.isOpenEmbedding.isInducing.specializes_iff.1 hsp
  have hm : z ∈ lam ⁻¹ᵁ W.toScheme.basicOpen d := hsp'.mem_open (W.toScheme.basicOpen d).isOpen hw
  rw [Scheme.preimage_basicOpen] at hm
  have hu := (Scheme.mem_basicOpen _ (U := lam ⁻¹ᵁ ⊤) _ z trivial).1 hm
  exact not_isUnit_zero (hd ▸ hu : IsUnit (0 : (Sp (FractionRing R)).presheaf.stalk z))

theorem val_spread : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  intro R V _ _ _ _ θ W X L hL K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ hF t₁ t₂ h₁ h₂ lam hl g hg x y k k' hy hk hk' H z J hJ
  obtain ⟨c, hc⟩ := exists_ratio hL hF h₁ h₂
  have hu : ∀ {F : Type} [Field F] (u : Fˣ) (w : Sp F),
      (gm (𝟙 (Sp F)) w ⊤ (unitOn u)).val = gsHom (𝟙 (Sp F)) w (fnOn (u : F)) := fun u w =>
    ((gsHom_apply _ _ _).trans (gs_unit _ w ⊤ trivial (unitOn u))).symm
  let z₀ : Sp (FractionRing R) := (⊥ : PrimeSpectrum (FractionRing R))
  choose I hI using fun χ : (TK R).left ⟶ X => exists_chart hL (χ z₀)
  have e₀ : gsHom lam z₀ c = gsHom (𝟙 (Sp (FractionRing R))) z₀ (fnOn (k : FractionRing R)) := by
    have := hc _ lam z₀ I hI
    rw [H z₀ I hI, mul_inv_cancel_right] at this
    exact (gsHom_apply _ _ _).trans (this.symm.trans (hu k z₀))
  have e₁ : c * W.ι.appTop.hom (fnOn y) - W.ι.appTop.hom (fnOn x) = 0 := by
    refine eq_zero_of_generic W lam hl z₀ _ ?_
    rw [map_sub, map_mul, gs_res_fn (algebraMap R (FractionRing R)) W lam hl,
      gs_res_fn (algebraMap R (FractionRing R)) W lam hl, ← hk, map_mul, map_mul]
    exact sub_eq_zero.2 (congrArg (· * _) e₀)
  have hg' : g ≫ W.ι = spMap ((algebraMap V (FractionRing V)).comp θ) :=
    hg.trans (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  have e₂ := congrArg (gsHom (Z := Sp (FractionRing V)) g z) (sub_eq_zero.1 e₁)
  rw [map_mul, gs_res_fn _ W g hg', gs_res_fn _ W g hg', RingHom.comp_apply, RingHom.comp_apply, ← hk', map_mul,
    map_mul] at e₂
  have hy' : IsUnit (algebraMap V (FractionRing V) (θ y)) :=
    isUnit_iff_ne_zero.2 fun h => hy (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))
  have e₃ := ((hy'.map fnOn).map (gsHom (𝟙 (Sp (FractionRing V))) z)).mul_right_cancel e₂
  refine mul_inv_eq_iff_eq_mul.1 (Units.ext ?_)
  exact (hc _ g z J hJ).trans ((gsHom_apply _ _ _).symm.trans (e₃.trans (hu k' z).symm))

end GlobalTheory.GenSpread

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GdegPullProof

theorem chernInt_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {B : LB X} (φ : Weight p σ B) (D : ℕ) :
    φ.chernInt D Set.univ (fun _ => 1) =
      (φ.chernPart D 1 Set.univ).toReal - (φ.chernPart D (-1) Set.univ).toReal := by
  simp [Weight.chernInt, Measure.real]

theorem mass {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) (hY : IsArithVar q D)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hη : π (genericPoint Y) = genericPoint X)
    (hδ : π.residueDegree (genericPoint Y) ≠ 0) (L : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ) :
    ((L.φ σ).pull π hπ).chernPart D ε Set.univ =
      (π.residueDegree (genericPoint Y) : ℝ≥0∞) * (L.φ σ).chernPart D ε Set.univ := by
  obtain ⟨U, hUη, hU⟩ := _root_.GlobalTheory.CoverDeg.exists_open_covering_charts hX hY π hπ hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hU σ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hcY : (ptsIn q σ (π ⁻¹ᵁ U))ᶜ =
      {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ} := by
    ext z
    simp [mem_ptsIn]
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have h0Y := _root_.GlobalTheory.ChernNull.chernPart_over_closed hY ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ (π ⁻¹ᵁ U).isOpen.isClosed_compl
    (by simp [hη, hUη]) σ ((L.φ σ).pull π hπ) ε
  have h0X := _root_.GlobalTheory.ChernNull.chernPart_over_closed hX ((U : X.Opens) : Set X)ᶜ U.isOpen.isClosed_compl (by simp [hUη]) σ
    (L.φ σ) ε
  rw [← hcY] at h0Y
  rw [← hcX] at h0X
  have h3 := _root_.GlobalTheory.CoverChern.chernPart_preimage_of_cover hX hY π hπ (L.φ σ) (L.cInf σ) ε (ptsIn p σ U) (isOpen_ptsIn U) _ hcard
    hchart hlift (fun c c' hc w hw => _root_.GlobalTheory.PullChartDens.chernDens_pull_of_chart π hπ (L.φ σ) (L.cInf σ) c c' hc w hw) _
    (isOpen_ptsIn U).measurableSet subset_rfl
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.GdegPullProof

namespace GlobalTheory.CovTest

theorem gdegPull : GdegPull := by
  intro k _ X Y _ _ p q D hX hY π hπ hη hδ L
  have key : ∀ σ, ((L.pull π hπ).φ σ).chernInt D Set.univ (fun _ => 1) =
      (π.residueDegree (genericPoint Y) : ℝ) * (L.φ σ).chernInt D Set.univ (fun _ => 1) := by
    intro σ
    change ((L.φ σ).pull π hπ).chernInt D Set.univ (fun _ => 1) = _
    rw [GdegPullProof.chernInt_one, GdegPullProof.chernInt_one,
      GdegPullProof.mass hX hY π hπ hη hδ L σ 1, GdegPullProof.mass hX hY π hπ hη hδ L σ (-1),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]
  simp only [gdeg, chInt]
  simp_rw [key]
  rw [mul_finsum]

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

namespace GlobalTheory.OpenGeomIrr

theorem geometricallyIrreducible_comp_of_isOpenImmersion : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j →
    ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  intro T W X j hj f hf hs
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h₁ : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hne : Nonempty ↥(Limits.pullback (j ≫ f) x) := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (.of K)) := inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (j ≫ f) x).surjective p
    exact ⟨z⟩
  let e := pullbackRightPullbackFstIso f x j
  have hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x)) := ⟨e.inv hne.some⟩
  have h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x)) :=
    (Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace
  exact e.hom.homeomorph.irreducibleSpace_iff.1 h₂

end GlobalTheory.OpenGeomIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem mapsAt₂_val : ∀ (Y X X₁ X₂ Z : Scheme.{0}) (L : LB X) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ) (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))) (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))), MapsAt₂ w p n a b₁ b₂ → ∀ (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι), Good L z J → Good L₁ z J₁ → Good L₂ z J₂ → val b₁ r z J₁ * val b₂ r z J₂ = gm (r ≫ p) z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p))) ^ n * val a r z J := by
  intro Y X X₁ X₂ Z L L₁ L₂ f₁ f₂ w p n a b₁ b₂ hM r z J J₁ J₂ hJ hJ₁ hJ₂
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U
      (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p)) :=
    ⟨⟨Set.mem_iInter.2 fun _ => hJ₁ (r ≫ p ≫ f₁), Set.mem_iInter.2 fun _ => hJ₂ (r ≫ p ≫ f₂)⟩, hJ (r ≫ p)⟩
  have e := congrArg (gm r z _) (hM (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)) (J (r ≫ p)))
  rw [map_mul, map_mul, map_zpow] at e
  exact (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _)).symm.trans
    (e.trans (congrArg₂ (· * ·) (congrArg (· ^ n) (gm_pull r p z _ hm _)) (gm_res r z _ hm _)))

end GlobalTheory.MumProd
end

