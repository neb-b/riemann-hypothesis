module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CechDescentTwistOfProperSurjectiveStrictlyHensel
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0010
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0019
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0032
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTateTwistSectionsEquivLocallyConstant
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecIntegralAlgebraStrictHenselian
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CurveEtaleDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem qcqs_id (X : Scheme.{0}) : QcqsOver (𝟙 (sch.obj X)) := by
  intro k
  refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
  simp
  exact Category.id_comp _

private theorem qcqs_cech {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] :
    QcqsOver (cechAug f ≫ 𝟙 (sch.obj X)) := by
  intro k
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsProper Y X f inferInstance k
  haveI := hπ
  refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
  simpa using he

private theorem stalk_eqv (R : Type) [CommRing R] (F : Shv R) {Y X T : Scheme.{0}} (f : Y ⟶ X) (s : T ⟶ X)
    (h : Eqv R (cechAug (pullback.snd f s)) F) :
    Eqv R ((bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)) F := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  obtain ⟨m, hpb, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback Y X (pullback f s) T (pullback.fst f s) (pullback.snd f s) f s
    (IsPullback.of_hasPullback f s)
  have hpb' : IsPullback m (cechAug (pullback.snd f s)) (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    rw [Category.comp_id]
    exact hpb
  let g : pullback (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) ⟶ pullback (𝟙 (sch.obj X)) (sch.map s) :=
    (bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)
  have hsnd : g ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = pullback.snd (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    dsimp only [g, bcMap]
    erw [pullback.lift_snd]
    exact Category.comp_id _
  have hQ : Eqv R (pullback.snd (𝟙 (sch.obj X)) (sch.map s)) F := hiso _ _ _ inferInstance
  have hι : Eqv R hpb'.isoPullback.hom F := hiso _ _ _ inferInstance
  have key : (hpb'.isoPullback.hom ≫ g) ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = cechAug (pullback.snd f s) := by
    rw [Category.assoc, hsnd, hpb'.isoPullback_hom_snd]
  have h1 : Eqv R (hpb'.isoPullback.hom ≫ g) F := by
    refine (hcomp _ _ _ _ _).2.2 hQ ?_
    rw [key]
    exact h
  exact ((hcomp _ _ _ _ _).2.1 hι h1 : Eqv R g F)

theorem UpperTheory.curve_etale_descent :
    LateralTheory.E.E4.LeafDesc := by
  intro hH q _ k _ hq Y X p _ f _ _ i
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X _ _ (cechAug f) (𝟙 (sch.obj X)) (UpperTheory.Cb.tateTwist_finitary q i)
    (qcqs_cech f) (qcqs_id X) ?_
  intro O _ s hs
  apply stalk_eqv
  have hqO : IsUnit ((q : ℕ) : O) := by
    have φ := Spec.preimage (s ≫ p)
    simpa using hq.map φ.hom
  exact UpperTheory.cech_descent_twist_of_proper_surjective_strictly_henselian hH q O hs.1 hqO (pullback.snd f s) i
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyExcisionAxiomHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem bijective_pull_spMap_tw_zero : ∀ (q : ℕ) [NeZero q] (i : ℤ) (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B'), IsUnit (q : B) →
    (∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) →
    (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') →
    Function.Bijective (pull _ (spMap φ) (tw q i) 0) := by
  intro q _ i B B' _ _ φ hq ⟨ζ, hζ⟩ hid
  obtain ⟨E, hE⟩ := UpperTheory.exists_tateTwist_sections_equiv_locallyConstant q i
  obtain ⟨-, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom φ)
  let ζ₀ : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ⟨ζ, hq, hζ⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    have h1 := UpperTheory.locallyConstant_comap_bijective B B' φ (ZMod q) hid
    have hc : ∀ s, E _ (ζ₀.map g.appTop.hom) (Sec.res g s) = (E _ ζ₀ s).comap ⟨g, g.continuous⟩ := hE _ _ g ζ₀
    have hcomp : (E _ (ζ₀.map g.appTop.hom)) ∘ (Sec.res (F := tw q i) g) = (fun a : LocallyConstant (PrimeSpectrum B) (ZMod q) => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) ∘ (E _ ζ₀) := by
      funext s
      exact hc s
    refine (Function.Bijective.of_comp_iff' (E _ (ζ₀.map g.appTop.hom)).bijective _).1 ?_
    rw [hcomp]
    exact h1.comp (E _ ζ₀).bijective
  have hp : (pull _ (sch.map g) (tw q i) 0) ∘ (e _) = (e _) ∘ (Sec.res (F := tw q i) g) := by
    funext s
    exact he g s
  refine (Function.Bijective.of_comp_iff _ (e _).bijective).1 ?_
  rw [hp]
  exact (e _).bijective.comp hres

private theorem eqv_ring : ∀ (q : ℕ) (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K]
    [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K)) (tw q i) := by
  intro q O R K _ _ _ _ _ _ _ hSH hq i n
  obtain ⟨hH, -⟩ := id hSH
  haveI : NeZero q := ⟨by
    rintro rfl
    simp at hq⟩
  have hqR : IsUnit (q : R) := by simpa using hq.map (algebraMap O R)
  haveI : Algebra.IsIntegral O (R ⊗[O] K) := by
    have : Algebra.IsIntegral R (R ⊗[O] K) := inferInstance
    exact Algebra.IsIntegral.trans R
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hs := (_root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero (ZMod q) (tw q i)).1
    haveI := hs (sp R) n hn
    haveI := hs (sp (R ⊗[O] K)) n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨ζ, hζ⟩ := UpperTheory.exists_cyclotomic_root_of_strictHenselian q O hSH hq
    refine bijective_pull_spMap_tw_zero q i R _ _ hqR ⟨algebraMap O R ζ, ?_⟩ (UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian O R K hSH)
    rw [Polynomial.aeval_algebraMap_apply, hζ, map_zero]
  · haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O R hSH hq n i hn
    haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O (R ⊗[O] K) hSH hq n i hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem T_key : ∀ (q : ℕ) (O K : Type) [CommRing O] [Field K] [Algebra O K] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) →
    ∀ (i : ℤ) {Z Z' W : Scheme.{0}} (r : Z ⟶ W) [IsIntegralHom r] (e : W ≅ Spec (CommRingCat.of O)) (c : Z' ⟶ Z)
      (g' : Z' ⟶ Spec (CommRingCat.of K)),
      IsPullback c g' r (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv) → Eqv _ (sch.map c) (tw q i) := by
  intro q O K _ _ _ _ hSH hq i Z Z' W r _ e c g' hpb
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hg : IsIntegralHom (r ≫ e.hom) := inferInstance
  haveI : IsAffine Z := isAffine_of_isAffineHom (r ≫ e.hom)
  let φ : CommRingCat.of O ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ r ≫ e.hom)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ r ≫ e.hom := Spec.map_preimage _
  letI alg : Algebra O Γ(Z, ⊤) := φ.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤))) = Z.isoSpec.inv ≫ r ≫ e.hom := hφ
  haveI hint : Algebra.IsIntegral O Γ(Z, ⊤) := by
    have h2 : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤)))) := by
      rw [hmap]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at h2
    exact (algebraMap_isIntegral_iff (R := O) (A := Γ(Z, ⊤))).1 h2
  have sq1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O Γ(Z, ⊤) K)
  have sq2 : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := Γ(Z, ⊤)) (B := K)).toRingHom)) (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso sq1 (Iso.refl _) Z.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [hmap]
    · simp
  have sq3 : IsPullback c g' (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  obtain ⟨u, hu⟩ : ∃ u : Z' ≅ Spec (CommRingCat.of (Γ(Z, ⊤) ⊗[O] K)), u.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv = c :=
    ⟨_, sq3.isoIsPullback_hom_fst _ _ sq2⟩
  have hE := eqv_ring q O Γ(Z, ⊤) K hSH hq i
  have h1 : sch.map c ≫ sch.map Z.isoSpec.hom = sch.map u.hom ≫ spMap (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K) := by
    rw [← sch.map_comp, ← sch.map_comp, ← hu]
    simp
  have h2 : Eqv _ (sch.map c ≫ sch.map Z.isoSpec.hom) (tw q i) := by
    rw [h1]
    exact (hcomp _ _ _ _ _).1 (hiso _ _ _ inferInstance) hE
  exact (hcomp _ _ _ _ _).2.2 (hiso _ _ _ inferInstance) h2

private theorem eqv_of_forall_conn {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : ∀ m, UpperTheory.RedSh.Conn f F m) : Eqv R f F := fun n => (h (n + 1)).1 n (by omega)

private theorem conn_of_eqv {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : Eqv R f F) (m : ℤ) : UpperTheory.RedSh.Conn f F m := ⟨fun n _ => h n, (h m).1⟩

private theorem L_loc : ∀ (q : ℕ) (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∀ (i : ℤ) {Y W : Scheme.{0}} (g : Y ⟶ W)
    [IsIntegralHom g] [Surjective g] (e : W ≅ Spec (CommRingCat.of O)), Eqv _ (cechAug g) (tw q i) := by
  intro q O _ hSH hq i Y W g _ _ e
  obtain ⟨hH, hS⟩ := id hSH
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  haveI : Algebra.IsIntegral O (IsLocalRing.ResidueField O) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId O (IsLocalRing.ResidueField O)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral O K := Algebra.IsIntegral.trans (IsLocalRing.ResidueField O)
  let b : Spec (CommRingCat.of K) ⟶ W := Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv
  have hpb := IsPullback.of_hasPullback g b
  haveI : IsIntegralHom (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  haveI : Surjective (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨s, hs⟩ := UpperTheory.exists_section_of_integral_surjective_algClosed K (pullback.snd g b)
  have hsplit : Eqv _ (cechAug (pullback.snd g b)) (tw q i) := UpperTheory.cechAugmentation_equiv_of_section _ _ s hs _
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ _ _ _ _ hpb
  have hb : Eqv _ (sch.map b) (tw q i) := by
    have : IsPullback b (𝟙 _) (𝟙 W) b := IsPullback.of_vert_isIso ⟨by simp⟩
    exact T_key q O K hSH hq i (𝟙 W) e b (𝟙 _) this
  have hlev : Eqv _ m (tw q i) := by
    refine eqv_of_forall_conn fun n => UpperTheory.sheafConnected_of_levelwise_connected _ _ m n fun k => conn_of_eqv ?_ _
    obtain ⟨Z, π, ez, hπ, hz⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ g inferInstance (op (SimplexCategory.mk k))
    have hpz := IsPullback.of_hasPullback (π ≫ g) b
    obtain ⟨ez', hez'⟩ := UpperTheory.cechNerve_pullback_representable_of_isPullback g (pullback.snd g b) b m hm (op (SimplexCategory.mk k)) ez (π ≫ g)
      (pullback.fst (π ≫ g) b) (pullback.snd (π ≫ g) b) hz hpz
    have h1 : Eqv _ (sch.map (pullback.fst (π ≫ g) b)) (tw q i) :=
      T_key q O K hSH hq i (π ≫ g) e _ _ hpz
    have h3 : Eqv _ (disc.map ez'.hom ≫ disc.map (m.app (op (SimplexCategory.mk k)))) (tw q i) := by
      rw [← Functor.map_comp, hez', Functor.map_comp]
      exact (hcomp _ _ _ _ _).1 h1 (hiso _ _ _ inferInstance)
    exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
  have hc : m ≫ cechAug g = cechAug (pullback.snd g b) ≫ sch.map b := hm.w
  have h2 : Eqv _ (m ≫ cechAug g) (tw q i) := by
    rw [hc]; exact (hcomp _ _ _ _ _).1 hsplit hb
  exact (hcomp _ _ _ _ _).2.1 hlev h2

theorem UpperTheory.etaleCohomology_excisionAxiom_holds : GlobalTheory.EtC.B4 := by
  intro q Y X f _ _ hq i
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hqc₁ : QcqsOver (cechAug f ≫ sch.map (𝟙 X)) := by
    intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ f inferInstance k
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id, Category.comp_id]
    exact he
  have hqc₂ : QcqsOver (sch.map (𝟙 X)) := by
    intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id]
    simp
    rfl
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change _ (tw q i) X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X)) (UpperTheory.Cb.tateTwist_finitary q i)
    hqc₁ hqc₂ ?_
  intro O _ s hs
  obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
  have hO : IsUnit (q : O) := by
    simpa using (hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
  let w : pullback (𝟙 X) (Over.mk s).hom ≅ Spec (CommRingCat.of O) := asIso (pullback.snd _ _)
  have hfst : IsPullback (pullback.fst f (pullback.fst (𝟙 X) (Over.mk s).hom)) (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) f (pullback.fst (𝟙 X) (Over.mk s).hom) := IsPullback.of_hasPullback _ _
  haveI : IsIntegralHom (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  haveI : Surjective (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  have h2 : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
    L_loc q O hs.1 hO i _ w
  have h3 : Eqv _ (e₁.hom ≫ (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s)) (tw q i) := by
    rw [h]
    exact (hcomp _ _ _ _ _).1 h2 (hiso _ _ _ inferInstance)
  exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HodgeCohomologyOpenRestrictionEquiv
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

private theorem formPull_ι_bijective {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V W : Z.Opens) (h : W ≤ V) (a : ℕ) :
    Function.Bijective (formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a) := by
  haveI := isIso_ι_app V W h
  have hsα := semiHom_appSec (s := s) (s' := V.ι ≫ s) (f := V.ι) rfl W
  let α := appSec s (V.ι ≫ s) V.ι W
  let β : Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ W) →+* Sec s W := (inv (V.ι.app W)).hom
  have hαβ : ∀ b, α (β b) = b := fun b => by
    simp only [α, β, appSec]
    exact IsIso.inv_hom_id_apply (V.ι.app W) b
  have hβα : ∀ b, β (α b) = b := fun b => by
    simp only [α, β, appSec]
    exact IsIso.hom_inv_id_apply (V.ι.app W) b
  have hαinj : Function.Injective α := fun x y hxy => by
    rw [← hβα x, ← hβα y, hxy]
  have hsβ : SemiHom (RingHom.id k) β := fun r b => by
    apply hαinj
    rw [hαβ, hsα, hαβ]
    rfl
  have hid₁ : SemiHom (RingHom.id k) (RingHom.id (Sec s W)) := fun r b => rfl
  have hid₂ : SemiHom (RingHom.id k) (RingHom.id (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ W))) := fun r b => rfl
  have hf : formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a = hsα.mOm a := rfl
  rw [hf, Function.bijective_iff_has_inverse]
  refine ⟨hsβ.mOm a, fun x => ?_, fun y => ?_⟩
  · rw [SemiHom.mOm_mOm hsα hsβ hid₁ hβα x, SemiHom.mOm_id hid₁ (fun _ => rfl)]
  · rw [SemiHom.mOm_mOm hsβ hsα hid₂ hαβ y, SemiHom.mOm_id hid₂ (fun _ => rfl)]

private theorem omegaPull_ι_app_bijective {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V W : Z.Opens) (h : W ≤ V) (hW : IsAffineOpen W) (hW' : IsAffineOpen (V.ι ⁻¹ᵁ W)) (a : ℕ) :
    Function.Bijective ((omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W) := by
  have comm : (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W ∘ toOm s a W =
      toOm (V.ι ≫ s) a (V.ι ⁻¹ᵁ W) ∘ formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a :=
    funext fun x ↦ omegaPull_toOmega (f := V.ι) (s' := V.ι ≫ s) rfl a W x
  have hb : Function.Bijective ((omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W ∘ toOm s a W) := by
    rw [comm]
    exact (toOm_bijective (V.ι ≫ s) a hW').comp (formPull_ι_bijective s V W h a)
  exact (Function.Bijective.of_comp_iff _ (toOm_bijective s a hW)).1 hb

private theorem isIso_restrict_omegaPull {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V : Z.Opens) (a : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a)) := by
  apply GroundTheory.Arith.SchemeCoh.isIso_of_bijective_app_affine
  intro U hU
  have hle : V.ι ''ᵁ U ≤ V := Scheme.Opens.ι_image_le V U
  have hW := hU.image_of_isOpenImmersion V.ι
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ (V.ι ''ᵁ U)) := by
    rw [Scheme.Hom.preimage_image_eq]
    exact hU
  exact omegaPull_ι_app_bijective s V (V.ι ''ᵁ U) hle hW hW' a

set_option maxHeartbeats 800000 in
theorem UpperTheory.hodgeCohomology_open_restriction_equiv :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (V : Z.Opens) (a b : ℕ), ∃ e : cohOn (Omega s a) V b ≃ hodgeH (V.ι ≫ s) a b, ∀ x : hodgeH s a b, e (cohOn.res ℤ (Omega s a) (le_top : V ≤ ⊤) b x) = hodgePull (f := V.ι) (s' := V.ι ≫ s) rfl a b x := by
  intro Z s V a b
  haveI := isIso_restrict_omegaPull s V a
  let θ : (Omega s a).restrict V.ι ⟶ Omega (V.ι ≫ s) a :=
    (Scheme.Modules.restrictFunctor V.ι).map (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app _
  haveI : IsIso θ := by
    dsimp only [θ]
    infer_instance
  have hZ : ∀ r : ℤ, (ConcreteCategory.hom (Scheme.Hom.appTop V.ι)) ((algebraMap ℤ Γ(Z, ⊤)) r) =
      (algebraMap ℤ Γ((V : Scheme), ⊤)) r := fun r => by simp
  have himg : V.ι ''ᵁ ⊤ = V := by simp
  have hmor : (Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a) ≫
      (Scheme.Modules.pushforward V.ι).map θ = omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a := by
    have key := (Scheme.Modules.restrictAdjunction V.ι).unit_naturality
      (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a)
    have tri := (Scheme.Modules.restrictAdjunction V.ι).right_triangle_components (Omega (V.ι ≫ s) a)
    dsimp only [θ]
    rw [Functor.map_comp, ← Category.assoc, key, Category.assoc, tri, Category.comp_id]
  have hle : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ V := by
    simp
  have h1 : ∀ y, cohOn.restrictEquiv ℤ hZ (Omega s a) himg b y =
      cohOn.pull (σ := RingHom.id ℤ) hZ ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) hle b y := by
    intro y
    rfl
  refine ⟨((cohOn.restrictEquiv ℤ hZ (Omega s a) himg b).trans
    (cohOn.mapIso ℤ ⊤ b (asIso θ))).toEquiv, fun (x : cohOn (Omega s a) ⊤ b) => ?_⟩
  have htop : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ ⊤ := le_top
  have hA := cohOn.pull_res (G := (Omega s a).restrict V.ι) (σ := RingHom.id ℤ) hZ
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) (le_top : V ≤ ⊤) hle x
  have hB := cohOn.map_pull (G := (Omega s a).restrict V.ι) (σ := RingHom.id ℤ) hZ
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) θ htop x
  have hC : cohOn.pull (σ := RingHom.id ℤ) hZ ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a) ≫
      (Scheme.Modules.pushforward V.ι).map θ) htop b x =
      cohOn.pull (σ := RingHom.id ℤ) hZ (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) htop b x :=
    congrArg (fun φ => cohOn.pull (σ := RingHom.id ℤ) hZ φ htop b x) hmor
  have h3 : cohOn.map ℤ θ ⊤ b (cohOn.restrictEquiv ℤ hZ (Omega s a) himg b
      (cohOn.res ℤ (Omega s a) (le_top : V ≤ ⊤) b x)) =
      cohOn.pull (σ := RingHom.id ℤ) hZ (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) htop b x :=
    (congrArg (cohOn.map ℤ θ ⊤ b) ((h1 _).trans hA)).trans (hB.trans hC)
  exact h3
end

