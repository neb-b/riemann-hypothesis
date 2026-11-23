module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_schemeTheoreticallyDominant {W Y X Z : Scheme.{0}} (φ : W ⟶ Y)
    [IsSchemeTheoreticallyDominant φ] (i : Z ⟶ X) [IsClosedImmersion i] (a : Y ⟶ X) (c : W ⟶ Z)
    (h : c ≫ i = φ ≫ a) : ∃ b : Y ⟶ Z, b ≫ i = a := by
  have H : i.ker ≤ a.ker := by
    have h1 : i.ker ≤ (c ≫ i).ker := Scheme.Hom.le_ker_comp c i
    rwa [h, ← Scheme.IdealSheafData.map_ker, φ.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h1
  exact ⟨IsClosedImmersion.lift i a H, IsClosedImmersion.lift_fac i a H⟩

theorem over_ext_of_schemeTheoreticallyDominant {S W : Scheme.{0}} {Y X : Over S}
    [IsSeparated X.hom] (φ : W ⟶ Y.left) [IsSchemeTheoreticallyDominant φ] {a b : Y ⟶ X}
    (h : φ ≫ a.left = φ ≫ b.left) : a = b := by
  have hY : a.left ≫ X.hom = b.left ≫ X.hom := by rw [Over.w a, Over.w b]
  let e : Y.left ⟶ pullback X.hom X.hom := pullback.lift a.left b.left hY
  have he1 : e ≫ pullback.fst X.hom X.hom = a.left := pullback.lift_fst _ _ _
  have he2 : e ≫ pullback.snd X.hom X.hom = b.left := pullback.lift_snd _ _ _
  have hc : (φ ≫ a.left) ≫ pullback.diagonal X.hom = φ ≫ e := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullback.diagonal_fst, he1, Category.comp_id]
    · simp only [Category.assoc]
      rw [pullback.diagonal_snd, he2, Category.comp_id, h]
  have hs2 : pullback.lift (φ ≫ a.left) φ hc ≫ pullback.snd (pullback.diagonal X.hom) e = φ :=
    pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ := exists_lift_of_schemeTheoreticallyDominant φ
    (pullback.snd (pullback.diagonal X.hom) e) (𝟙 _) (pullback.lift _ _ hc)
    (by rw [hs2, Category.comp_id])
  have key : ∀ g : pullback X.hom X.hom ⟶ X.left, e ≫ g =
      s ≫ pullback.fst (pullback.diagonal X.hom) e ≫ pullback.diagonal X.hom ≫ g := by
    intro g
    rw [pullback.condition_assoc, ← Category.assoc s, hs, Category.id_comp]
  have ha := key (pullback.fst X.hom X.hom)
  have hb := key (pullback.snd X.hom X.hom)
  rw [he1, pullback.diagonal_fst, Category.comp_id] at ha
  rw [he2, pullback.diagonal_snd, Category.comp_id] at hb
  exact Over.OverMorphism.ext (ha.trans hb.symm)

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem pullback_map_injective_of_flat {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom]
    {a b : Y ⟶ X} (h : (Over.pullback f).map a = (Over.pullback f).map b) : a = b := by
  apply over_ext_of_schemeTheoreticallyDominant (pullback.fst Y.hom f)
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have kb : ((Over.pullback f).map b).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ b.left :=
    pullback.lift_fst _ _ _
  rw [← ka, ← kb, h]

theorem existsUnique_lift_of_flat {Y X Z : Over S} (i : Z ⟶ X) (a : Y ⟶ X)
    (a' : (Over.pullback f).obj Y ⟶ (Over.pullback f).obj Z) [Flat Y.hom]
    [IsClosedImmersion i.left] (h : a' ≫ (Over.pullback f).map i = (Over.pullback f).map a) :
    ∃! b : Y ⟶ Z, b ≫ i = a ∧ (Over.pullback f).map b = a' := by
  have ki : ((Over.pullback f).map i).left ≫ pullback.fst X.hom f = pullback.fst Z.hom f ≫ i.left :=
    pullback.lift_fst _ _ _
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have hc : (a'.left ≫ pullback.fst Z.hom f) ≫ i.left = pullback.fst Y.hom f ≫ a.left := by
    rw [Category.assoc, ← ki, ← ka, ← h, Over.comp_left, Category.assoc]
  obtain ⟨b₀, hb₀⟩ := exists_lift_of_schemeTheoreticallyDominant (pullback.fst Y.hom f) i.left
    a.left (a'.left ≫ pullback.fst Z.hom f) hc
  have hw : b₀ ≫ Z.hom = Y.hom := by
    rw [← Over.w i, ← Category.assoc, hb₀, Over.w a]
  have kb1 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.fst Z.hom f =
      pullback.fst Y.hom f ≫ b₀ := pullback.lift_fst _ _ _
  have kb2 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.snd Z.hom f =
      pullback.snd Y.hom f := pullback.lift_snd _ _ _
  have h3 : a'.left ≫ pullback.snd Z.hom f = pullback.snd Y.hom f := Over.w a'
  refine ⟨Over.homMk b₀ hw, ⟨Over.OverMorphism.ext hb₀, ?_⟩, ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [← cancel_mono i.left, kb1, Category.assoc, Category.assoc, hb₀, ← hc, Category.assoc]
    · rw [kb2, h3]
  · rintro b ⟨hb, -⟩
    apply Over.OverMorphism.ext
    rw [← cancel_mono i.left]
    have hb' := congrArg CommaMorphism.left hb
    exact hb'.trans hb₀.symm

theorem isMonHom_of_pullback_of_flat {G G' : Over S} [MonObj G] [MonObj G'] (F : G ⟶ G')
    [Flat G.hom] [IsSeparated G'.hom] [h : IsMonHom ((Over.pullback f).map F)] : IsMonHom F := by
  have h1 : Flat (𝟙_ (Over S)).hom := by
    change Flat (𝟙 S)
    infer_instance
  have h2 : Flat (G ⊗ G).hom := by
    change Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  constructor
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.one_hom ((Over.pullback f).map F)
    simp only [Functor.obj.η_def, Category.assoc] at this
    rw [Functor.map_comp]
    exact (cancel_epi _).1 this
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.mul_hom ((Over.pullback f).map F)
    simp only [Functor.obj.μ_def, Category.assoc] at this
    rw [Functor.LaxMonoidal.μ_natural_assoc] at this
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi _).1 this

end

theorem schemeTheoreticallyDominant_fractionField (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] :
    IsSchemeTheoreticallyDominant (spMap (algebraMap T K)) := by
  have hinj : Function.Injective (algebraMap T K) := IsFractionRing.injective T K
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap T K))
  have h : Function.Injective (spMap (algebraMap T K)).appTop := by
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at h2
    simp only at h2
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T)).hom).1 (hinj h2)
  refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩]
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).1 h

theorem flat_dvr_generic_fibre :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X : Over (Sp T)), Flat Y.hom → IsSeparated X.hom → ∀ a b : Y ⟶ X, (Over.pullback (spMap (algebraMap T K))).map a = (Over.pullback (spMap (algebraMap T K))).map b → a = b) ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X Ga : Over (Sp T)) (io : Ga ⟶ X) (a : Y ⟶ X) (a' : (Over.pullback (spMap (algebraMap T K))).obj Y ⟶ (Over.pullback (spMap (algebraMap T K))).obj Ga), Flat Y.hom → IsClosedImmersion io.left → a' ≫ (Over.pullback (spMap (algebraMap T K))).map io = (Over.pullback (spMap (algebraMap T K))).map a → ∃! b : Y ⟶ Ga, b ≫ io = a ∧ (Over.pullback (spMap (algebraMap T K))).map b = a') ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'] (F : G ⟶ G'), Flat G.hom → IsSeparated G'.hom → IsMonHom ((Over.pullback (spMap (algebraMap T K))).map F) → IsMonHom F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T K _ _ _ _ _ _ Y X hY hX a b h
    have := schemeTheoreticallyDominant_fractionField T K
    exact pullback_map_injective_of_flat (spMap (algebraMap T K)) h
  · intro T K _ _ _ _ _ _ Y X Ga io a a' hY hio h
    have := schemeTheoreticallyDominant_fractionField T K
    exact existsUnique_lift_of_flat (spMap (algebraMap T K)) io a a' h
  · intro T K _ _ _ _ _ _ G G' _ _ F hG hG' hF
    have := schemeTheoreticallyDominant_fractionField T K
    exact isMonHom_of_pullback_of_flat (spMap (algebraMap T K)) F

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory

theorem adjunction_homEquiv_symm_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Monoidal] {Y : C} {M : D} [MonObj M] (a b : Y ⟶ R.obj M) :
    (adj.homEquiv Y M).symm (a * b) = (adj.homEquiv Y M).symm a * (adj.homEquiv Y M).symm b := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, ← Category.assoc,
    adj.homEquiv_naturality_right_symm]
  congr 1
  ext
  · rw [← adj.homEquiv_naturality_right_symm]; simp
  · rw [← adj.homEquiv_naturality_right_symm]; simp

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

noncomputable def splitTorusPoint (t : Multiplicative X →* kˣ) :
    𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom) (by
    erw [Category.assoc, torusIso_hom_hom, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have : (torusEval t).toRingHom.comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k :=
      (torusEval t).comp_algebraMap
    rw [this]
    exact Spec.map_id _)

theorem splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    (splitTorusPoint t).left =
      Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom := rfl

theorem splitTorusPoint_bijective :
    Function.Bijective (splitTorusPoint : (Multiplicative X →* kˣ) → _) := by
  constructor
  · intro s t h
    have h1 := congrArg (·.left) h
    simp only [splitTorusPoint_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).1 h1)
    exact torusEval_bijective.1 (AlgHom.coe_ringHom_injective (congrArg (·.hom) h2))
  · intro x
    let g : Spec (.of k) ⟶ Spec (.of (AddMonoidAlgebra k X)) := x.left ≫ (torusIso k X).inv
    have hg : CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k X)) ≫ Spec.preimage g = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← torusIso_hom_hom, Spec.map_id]
      simp only [g]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨t, ht⟩ := torusEval_bijective.2 ⟨(Spec.preimage g).hom, fun r => congr($hg r)⟩
    refine ⟨t, Over.OverMorphism.ext ?_⟩
    rw [splitTorusPoint_left, ht]
    change Spec.map (Spec.preimage g) ≫ _ = _
    rw [Spec.map_preimage]
    simp only [g]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def splitTorusDown (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ splitTorusAff ZU X :=
  (Over.homMk (𝟙 (Sp k)) (specULiftZIsTerminal.hom_ext _ _) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ (Over.map (toZ (Sp k))).obj (𝟙_ (Over (Sp k)))) ≫
    ((Over.mapPullbackAdj (toZ (Sp k))).homEquiv _ _).symm x

theorem splitTorusDown_left (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (splitTorusDown x).left = x.left ≫ torusFst (Sp k) X := by
  simp [splitTorusDown, Adjunction.homEquiv_symm_apply, torusFst]
  rfl

theorem splitTorusDown_mul (x y : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    splitTorusDown (x * y) = splitTorusDown x * splitTorusDown y := by
  unfold splitTorusDown
  rw [← comp_mul]
  exact congrArg _ (adjunction_homEquiv_symm_mul (Over.mapPullbackAdj _) x y)

theorem splitTorusDown_injective :
    Function.Injective (splitTorusDown : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) → _) := by
  intro x y h
  have h1 := congrArg (·.left) h
  simp only [splitTorusDown_left] at h1
  exact Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w x).trans (Over.w y).symm))

noncomputable def torusEvalInt (t : Multiplicative X →* kˣ) :
    AddMonoidAlgebra ZU.{0} X →ₐ[ZU.{0}] k :=
  AddMonoidAlgebra.lift _ k X ((Units.coeHom k).comp t)

theorem splitTorusDown_point (t : Multiplicative X →* kˣ) :
    splitTorusDown (splitTorusPoint t) = Spec.mapMulEquiv (WithConv.toConv (torusEvalInt t)) := by
  refine Over.OverMorphism.ext ?_
  rw [splitTorusDown_left, splitTorusPoint_left]
  erw [Category.assoc, torusIso_hom_fst, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (torusEvalInt t).toRingHom)
  rw [← CommRingCat.ofHom_comp]
  congr 2
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt]

theorem torusEvalInt_mul (s t : Multiplicative X →* kˣ) :
    WithConv.toConv (torusEvalInt (s * t)) =
      WithConv.toConv (torusEvalInt s) * WithConv.toConv (torusEvalInt t) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt, AlgHom.convMul_def]

theorem splitTorusPoint_mul (s t : Multiplicative X →* kˣ) :
    splitTorusPoint (s * t) = splitTorusPoint s * splitTorusPoint t := by
  apply splitTorusDown_injective
  rw [splitTorusDown_mul, splitTorusDown_point, splitTorusDown_point, splitTorusDown_point,
    torusEvalInt_mul, map_mul]


variable (k X) in
noncomputable def splitTorusPointEquiv :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  { Equiv.ofBijective _ splitTorusPoint_bijective with map_mul' := splitTorusPoint_mul }

theorem range_splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by
  have h : ∀ p, (splitTorusPoint t).left p = (torusIso k X).hom (torusPrime t) := fun p => by
    have hp : p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hp]
    rfl
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact h p
  · rintro rfl
    exact ⟨_, h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

theorem finite_of_isClosed_splitTorus_of_pow_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ X _ _ _ n hp hn C Z hZ hC htors
  haveI : NeZero (n : k) := ⟨hn⟩
  let e := splitTorusPointEquiv (k := k) (X := X)
  have hcl : @IsClosed _ (torusZariski k X)
      (C.comap e.toMonoidHom : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_pow_eq_one hp.two_le hcl fun s hs h1 =>
    e.injective (by rw [map_one]; exact htors _ hs (by rw [← map_pow, h1, map_one]))
  have e' : C.comap e.toMonoidHom ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace UnramifiedEndFlat

open IsLocalRing

theorem flat_of_map_maximalIdeal_self {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : A →+* A) (hm : (maximalIdeal A).map φ = maximalIdeal A)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal A).comap φ := Ideal.le_comap_of_map_le hm.le
  refine flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_
  rw [← hm, Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [show φ (a + b) - (y + z) = (φ a - y) + (φ b - z) by rw [map_add (f := _)]; ring]
    exact add_mem hay hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨d, hd⟩ := h₀ c
    refine ⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [show φ (d * a) - c • y = (φ d - c) * φ a + c * (φ a - y) by
      rw [map_mul, smul_eq_mul]; ring]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hay)
    rw [pow_two]
    exact Ideal.mul_mem_mul hd (hle ha)

theorem flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by
  have he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A :=
    map_maximalIdeal_of_surjective _ e.surjective
  have h : ((e : B →+* A).comp φ).Flat := by
    refine flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_
    obtain ⟨a, ha⟩ := h₀ (e.symm b)
    refine ⟨a, ?_⟩
    have := Ideal.mem_map_of_mem (e : B →+* A) ha
    rw [he] at this
    simpa using this
  have := h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)
  convert this
  ext x
  simp

theorem flat_iff_comp_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C

theorem flat_stalkSpecializes {X : Scheme.{0}} {x x' : X} (h : x ⤳ x') :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  rw [flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _

theorem flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have h' : f x ⤳ f x' := h.map f.continuous
  rw [flat_iff_comp_germ hU (h'.mem_open U.2 hx'),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']
  exact hf.comp (flat_stalkSpecializes h)

theorem flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)

theorem residueFieldMap_surjective {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by
  have h : (residueFieldIsoBase (f ≫ g) x hx).inv =
      Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    simp
  have h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [h] at h2
  exact Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2

theorem flat_stalkMap_of_fixed {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (f : X ⟶ X) (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hfg : f ≫ g = g)
    [FormallyUnramified f] (x : X) (hx : IsClosed {x}) (hfx : f x = x) :
    (f.stalkMap x).hom.Flat := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (f ≫ g) := by rw [hfg]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have h1 := FormallyUnramified.stalkMap f x
  have h2 := LocallyOfFiniteType.stalkMap f x
  refine flat_of_map_maximalIdeal
    (X.presheaf.stalkCongr (Inseparable.of_eq hfx.symm)).commRingCatIsoToRingEquiv _ ?_ fun b => ?_
  · algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Algebra.FormallyUnramified.map_maximalIdeal
  · obtain ⟨a, ha⟩ := residueFieldMap_surjective f g x hx (X.residue x b)
    obtain ⟨a, rfl⟩ := X.residue_surjective (f x) a
    refine ⟨a, Ideal.Quotient.eq.mp ?_⟩
    exact ha

end UnramifiedEndFlat


open UnramifiedEndFlat in
theorem flat_of_formallyUnramified_grpEnd (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k))
    [GrpObj G] (φ : G ⟶ G) (hG : LocallyOfFiniteType G.hom) (hφ : IsMonHom φ)
    (hu : FormallyUnramified φ.left) : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine UnramifiedEndFlat.flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let o : G.left := η[G].left (IsLocalRing.closedPoint k)
  have ho : IsClosed {o} := (pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint k))
  have h0 := UnramifiedEndFlat.flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo
  let α := GrpObj.mulRight (A := G) x'
  let β := GrpObj.mulRight (A := G) (x' ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp [α, β, comp_lift_assoc]
  have hα : η[G] ≫ α.hom = x' := by
    simpa [α, comp_lift_assoc] using lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'
  have hα' : α.hom.left o = x :=
    (congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp h0
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1

end GlobalTheory
end

