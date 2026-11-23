module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalCompactSmall
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

namespace GlobalTheory.GLTwoHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_adicCompletionIntegers_loc (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem eventually_singleNU_mem {N : Set (FiniteAdeleRing (𝓞 E) E)} (hN : N ∈ 𝓝 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ y ∈ w.adicCompletionIntegers E, singleNU w y ∈ N := by
  classical
  let s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous
  have hs0 : s 0 = 0 := rfl
  have h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) :=
    hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)
  rw [nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hIt⟩ := h1
  refine Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_
  have hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y := by
    refine Subtype.ext (funext fun u => ?_)
    change ((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)
    by_cases h : u = w
    · subst h
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]
      rfl
  rw [← hx]
  refine hIt fun u hu => ?_
  have hne : u ≠ w := fun e => hw (e ▸ hu : w ∈ (I : Set _))
  rw [Pi.single_eq_of_ne hne]
  exact mem_of_mem_nhds (ht u)

end GlobalTheory.GLTwoHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePointsEquivGalois
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Published.AbVarRed

variable (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω]
  [IsScalarTower K L Ω]

theorem spMap_algebraMap_tower :
    spMap (algebraMap K Ω) = spMap (algebraMap L Ω) ≫ spMap (algebraMap K L) := by
  rw [IsScalarTower.algebraMap_eq K L Ω]
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {K L Ω} (A : Over (Sp K))

def baseChangePt (x : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) : ptOver K Ω ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) (by
    show (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) ≫ A.hom = spMap (algebraMap K Ω)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hx : x.left ≫ pullback.snd A.hom (spMap (algebraMap K L)) = spMap (algebraMap L Ω) := Over.w x
    rw [hx, spMap_algebraMap_tower K L Ω])

def baseChangePtInv (y : ptOver K Ω ⟶ A) : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A :=
  Over.homMk (pullback.lift y.left (spMap (algebraMap L Ω)) (by
    have hy : y.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w y
    rw [hy, spMap_algebraMap_tower K L Ω])) (pullback.lift_snd _ _ _)

def baseChangePtEquiv [GrpObj A] :
    (ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) ≃* (ptOver K Ω ⟶ A) where
  toFun := baseChangePt A
  invFun := baseChangePtInv A
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  map_mul' x y := by
    have h := isGrpPullback_pullback A (spMap (algebraMap K L))
    apply Over.OverMorphism.ext
    refine Eq.symm <| (mul_left_congr (spMap_algebraMap_tower K L Ω) (baseChangePt A x) (baseChangePt A y)
      (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans ?_
    exact (h.2 _ x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans rfl

end GlobalTheory.Published.AbVarRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadConn

variable {S : Scheme.{0}}

theorem unit_comp (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := by
  have h := Over.w (η[G])
  have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
  rwa [h2] at h

theorem hom_unit (G : Over S) [GrpObj G] (s : S) : G.hom ((η[G]).left s) = s := by
  rw [← Scheme.Hom.comp_apply, unit_comp]
  rfl

theorem isConnected_fibre (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : G.hom ⁻¹' {s} ⊆ U) : _root_.IsConnected (G.hom ⁻¹' {s}) := by
  have hu : (η[G]).left s ∈ G.hom ⁻¹' {s} := hom_unit G s
  have he : connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) = G.hom ⁻¹' {s} := by
    refine (connectedComponentIn_subset _ _).antisymm fun x hx => ?_
    have h1 := (hU x).1 (h hx)
    have hx' : G.hom x = s := hx
    rwa [hx'] at h1
  rw [← he]
  exact isConnected_connectedComponentIn_iff.2 hu

theorem subset_of_isPreconnected (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : _root_.IsPreconnected (G.hom ⁻¹' {s})) : G.hom ⁻¹' {s} ⊆ U := by
  intro x hx
  have hx' : G.hom x = s := hx
  refine (hU x).2 ?_
  rw [hx']
  exact h.subset_connectedComponentIn (hom_unit G s) subset_rfl hx

theorem geometricallyConnected_fibre (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] (s : S) (h : _root_.IsConnected (G.hom ⁻¹' {s})) :
    GeometricallyConnected (G.hom.fiberToSpecResidueField s) := by
  have hc : ConnectedSpace (G.hom.fiber s) :=
    (G.hom.fiberHomeo s).connectedSpace_iff.2 (isConnected_iff_connectedSpace.1 h)
  exact GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint (S.residueField s)
    (Over.mk (G.hom.fiberToSpecResidueField s))
    (inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField s))))
    (inferInstanceAs (QuasiCompact (pullback.snd G.hom (S.fromSpecResidueField s)))) hc
    ⟨Over.homMk (pullback.lift (S.fromSpecResidueField s ≫ (η[G]).left) (𝟙 _)
      (by rw [Category.assoc, unit_comp, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _)⟩

theorem isConnected_of_geometricallyConnected_fibre {X : Scheme.{0}} (f : X ⟶ S) (s : S)
    (h : GeometricallyConnected (f.fiberToSpecResidueField s)) : _root_.IsConnected (f ⁻¹' {s}) := by
  have hc : ConnectedSpace (f.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s)
  exact isConnected_iff_connectedSpace.2 ((f.fiberHomeo s).connectedSpace_iff.1 hc)

end GlobalTheory.SpreadConn

namespace GlobalTheory.SpreadConn

theorem geometricallyConnected_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  intro R _ _ _ G _ hs hq K _ e he hgc
  obtain ⟨G₀, _, j, -, hjo, hj⟩ := GlobalTheory.identityComponentOpen (Sp R) G hs
  let U : Set G.left := Set.range j.left
  let η₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η₀ ∈ Set.range (spMap e) := ⟨(default : PrimeSpectrum K), by
    apply PrimeSpectrum.ext
    change Ideal.comap e (default : PrimeSpectrum K).asIdeal = ⊥
    have h0 : (default : PrimeSpectrum K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h0]
    exact Ideal.comap_bot_of_injective _ he⟩
  have hgen : GeometricallyConnected (G.hom.fiberToSpecResidueField η₀) :=
    GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom (spMap e)
      ((Sp R).fromSpecResidueField η₀)
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hη) hgc
  have hsub0 : G.hom ⁻¹' {η₀} ⊆ U := subset_of_isPreconnected G U hj η₀
    (isConnected_of_geometricallyConnected_fibre G.hom η₀ hgen).isPreconnected
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have hUo : IsOpen U := j.left.isOpenEmbedding.isOpen_range
  have hZ : Topology.IsConstructible Uᶜ :=
    (IsRetrocompact.isConstructible hUo fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _).compl
  have hC : Topology.IsConstructible (G.hom '' Uᶜ) := G.hom.isConstructible_image hZ
  obtain ⟨V, hV, h1, h2⟩ := GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible continuous_id hC.compl
  rw [Set.preimage_id] at h1 h2
  have hηC : η₀ ∈ (G.hom '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, hxη⟩
    exact hx (hsub0 hxη)
  have hgenz : ∀ p : Sp R, η₀ ⤳ p := fun p =>
    (PrimeSpectrum.le_iff_specializes (η₀ : PrimeSpectrum R) (p : PrimeSpectrum R)).1
      (show (⊥ : Ideal R) ≤ (p : PrimeSpectrum R).asIdeal from bot_le)
  have hcl : closure (G.hom '' Uᶜ)ᶜ = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    exact closure_mono (Set.singleton_subset_iff.2 hηC) (specializes_iff_mem_closure.1 (hgenz p))
  rw [hcl, Set.inter_univ] at h1 h2
  have hVne : V.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h2
    exact Set.empty_ne_univ h2
  obtain ⟨p₀, hp₀⟩ := hVne
  have hηV : η₀ ∈ V := (hgenz p₀).mem_open hV hp₀
  obtain ⟨_, ⟨f, rfl⟩, hf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηV hV
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).1 hf ?_, fun F _ ψ hψ => ?_⟩
  · rw [he (h0.trans (map_zero e).symm)]
    exact zero_mem _
  · let p : Sp R := spMap ψ (default : PrimeSpectrum F)
    have hpf : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine (PrimeSpectrum.mem_basicOpen f (p : PrimeSpectrum R)).2 fun hfp => ?_
      change ψ f ∈ (default : PrimeSpectrum F).asIdeal at hfp
      exact (default : PrimeSpectrum F).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfp hψ)
    have hpC : p ∉ G.hom '' Uᶜ := h1 (hfV hpf)
    have hsub : G.hom ⁻¹' {p} ⊆ U := fun x hx => by
      by_contra hxU
      exact hpC ⟨x, hxU, hx⟩
    have hfib := geometricallyConnected_fibre G p (isConnected_fibre G U hj p hsub)
    refine GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom
      ((Sp R).fromSpecResidueField p) (spMap ψ) ?_ hfib
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨y, rfl⟩
    show spMap ψ y = p
    rw [Subsingleton.elim (α := PrimeSpectrum F) y default]

end GlobalTheory.SpreadConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SmoothRelDim

theorem smoothOfRelativeDimension_of_generic (R : Type) [CommRing R] [IsDomain R] (X : Over (Sp R))
    [Smooth X.hom] (K : Type) [Field K] (e : R →+* K) (he : Function.Injective e) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e))) :
    SmoothOfRelativeDimension g X.hom := by
  have hdom : IsDominant (spMap e) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have key : ∀ x, n x = g := fun x => by
    have ho : IsOpen (X.hom.base '' (W x : Set X.left)) := X.hom.isOpenMap _ (W x).isOpen
    obtain ⟨s, ⟨y, hyW, hy⟩, t, rfl⟩ :=
      hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y t hy
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x

theorem exists_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  intro R _ _ _ X hX _ K _ e he g hg
  haveI := hX
  refine ⟨1, by simp, fun F _ ψ _ => ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _)
    (smoothOfRelativeDimension_of_generic R X K e he g hg)

end GlobalTheory.SmoothRelDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem sec_eq_zero_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = 0) : s = 0 := by
  apply GlobalTheory.LB.f_injective
  funext i
  refine finSec_eq_zero_of_cover V hc (s.f i) fun a => ?_
  have h₁ : rs X (inf_le_left : L.U i ⊓ V a ≤ L.U i) (s.f i) =
      rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)) (L.g i (c a)).val *
        rs X (inf_le_right : L.U i ⊓ V a ≤ V a) (rs X (hV a) (s.f (c a))) := by
    have h := congrArg (rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)))
      (s.compat i (c a))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  rw [h₁, h a, map_zero, mul_zero]

theorem sec_eq_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s t : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = rs X (hV a) (t.f (c a))) : s = t :=
  sub_eq_zero.1 (sec_eq_zero_of_local V hc c hV _ fun a => by rw [GlobalTheory.LB.sub_f, map_sub, h a, sub_self])

section PerfSec

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
  {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) {g : R →+* R'} {π : X' ⟶ X}
  {f' : X' ⟶ Spec (CommRingCat.of R')}
  (E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π))

theorem Perf.iSup_preimage : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Q.cover]
  exact top_unique fun _ _ => trivial


include Q in
theorem Perf.sec_add
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (v w : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨v.1 + w.1, by rw [Matrix.mulVec_add, v.2, w.2, add_zero]⟩ = E v + E w := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ ((map_add (rs X' (le_pull M π (Q.le i))) ((E v).f fun _ => Q.ch i)
    ((E w).f fun _ => Q.ch i)).trans (congrArg₂ (· + ·) (hE v i) (hE w i))).symm)
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]


include Q in
theorem Perf.sec_smul
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (r : R') (v : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨r • v.1, by rw [Matrix.mulVec_smul, v.2, smul_zero]⟩ = cst f' ⊤ r • E v := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  have key : rs X' (le_pull M π (Q.le i)) (resG X' le_top (cst f' ⊤ r)) = cst f' (π ⁻¹ᵁ Q.W i) r := by
    change rs X' _ (rs X' le_top _) = _
    rw [rs_rs, rs_cst]
  refine (hE _ i).trans (Eq.trans ?_ ((map_mul (rs X' (le_pull M π (Q.le i))) (resG X' le_top (cst f' ⊤ r))
    ((E v).f fun _ => Q.ch i)).trans (congrArg₂ (· * ·) key (hE v i))).symm)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]

end PerfSec

theorem finSecPullId_add {X : Scheme.{0}} {M : LB X} (s t : LB.Sec M) :
    finSecPullId (s + t) = finSecPullId s + finSecPullId t := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact map_add _ _ _

theorem finSecPullId_smul {X : Scheme.{0}} {M : LB X} (a : Γ(X, ⊤)) (s : LB.Sec M) :
    finSecPullId (a • s) = a • finSecPullId s := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact (map_mul _ _ _).trans (congrArg (· * _) (rs_rs _ _ _))

theorem eq_zero_of_finSecPullId {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (s : LB.Sec M)
    (hs : finSecPullId s = 0) : s = 0 := by
  refine sec_eq_zero_of_local Q.W Q.cover Q.ch Q.le s fun j => ?_
  have hle : Q.W j ≤ (M.pull (𝟙 X)).U (fun _ => Q.ch j) :=
    le_trans (show Q.W j ≤ (𝟙 X) ⁻¹ᵁ Q.W j from fun _ hx => hx) (le_pull M (𝟙 X) (Q.le j))
  have h := congrArg (fun σ : LB.Sec (M.pull (𝟙 X)) => rs X hle (σ.f (fun _ => Q.ch j))) hs
  refine Eq.trans ?_ (h.trans (map_zero (rs X hle)))
  exact (rs_rs _ _ _).symm

end GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_basis_sec_of_isDiscreteValuationRing : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  intro W _ _ _ X f M hf hp hM
  obtain ⟨Q⟩ := nonempty_perf_of_noetherian W X f hf hp M hM
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id W))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec W (RingHom.id W) X (𝟙 X) f hpb
  let φ : LB.Sec M → Fin Q.a → W := fun s => (E.symm (finSecPullId s)).1
  have hadd : ∀ s t, φ (s + t) = φ s + φ t := by
    intro s t
    have h := Q.sec_add E hE (E.symm (finSecPullId s)) (E.symm (finSecPullId t))
    rw [E.apply_symm_apply, E.apply_symm_apply, ← finSecPullId_add, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have hsmul : ∀ (r : W) s, φ (cst f ⊤ r • s) = r • φ s := by
    intro r s
    have h := Q.sec_smul E hE r (E.symm (finSecPullId s))
    rw [E.apply_symm_apply, ← finSecPullId_smul, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have φ0 : φ 0 = 0 := by
    have h := hsmul 0 0
    rwa [smul_zero, zero_smul] at h
  have hinj : ∀ s t, φ s = φ t → s = t := by
    intro s t h
    have hst : finSecPullId s = finSecPullId t := E.symm.injective (Subtype.ext h)
    have e := finSecPullId_add (s - t) t
    rw [sub_add_cancel, hst] at e
    have h2 : finSecPullId (s - t) = 0 := add_right_cancel (e.symm.trans (zero_add _).symm)
    exact sub_eq_zero.1 (eq_zero_of_finSecPullId Q _ h2)
  let N : Submodule W (Fin Q.a → W) :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s + t, hadd s t⟩
      zero_mem' := ⟨0, φ0⟩
      smul_mem' := by
        rintro r _ ⟨s, rfl⟩
        exact ⟨cst f ⊤ r • s, hsmul r s⟩ }
  have memN : ∀ s, φ s ∈ N := fun s => ⟨s, rfl⟩
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun W (Fin Q.a)) N
  have hb : ∀ j, ∃ s, φ s = (b j).1 := fun j => (b j).2
  choose t ht using hb
  let φh : LB.Sec M →+ (Fin Q.a → W) := { toFun := φ, map_zero' := φ0, map_add' := hadd }
  have hsum : ∀ c : Fin n → W, φ (∑ j, cst f ⊤ (c j) • t j) = ∑ j, c j • (b j).1 := by
    intro c
    change φh _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (hsmul (c j) (t j)).trans (by rw [ht])
  refine ⟨n, t, fun u => ⟨fun j => b.repr ⟨φ u, memN u⟩ j, ?_, ?_⟩⟩
  · apply hinj
    rw [hsum]
    have h := congrArg Subtype.val (b.sum_repr ⟨φ u, memN u⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · intro c hc
    have h : (⟨φ u, memN u⟩ : N) = ∑ j, c j • b j := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum, ← hc]
    funext j
    rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
section
namespace GlobalTheory

theorem geometricLemmaFiltration_holds : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory
end

