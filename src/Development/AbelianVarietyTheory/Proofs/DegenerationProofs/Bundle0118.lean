module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitDataStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  first | exact @GlobalTheory.arc_abLocus_of_traitData | exact GlobalTheory.arc_abLocus_of_traitData | (intros; apply GlobalTheory.arc_abLocus_of_traitData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimagesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatumMatch_length_symm_preimages : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) := by
  first | exact @GlobalTheory.LN.be_symm_eq_of_match | exact GlobalTheory.LN.be_symm_eq_of_match | (intros; apply GlobalTheory.LN.be_symm_eq_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeries
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcExtends

theorem exists_lift_finite {K : Type} [Field K] {Z X : Scheme.{0}} (π : Z ⟶ X) [IsFinite π] [Surjective π]
    (x : Sp K ⟶ X) : ∃ (L : Type) (_ : Field L) (σ : K →+* L) (z : Sp L ⟶ Z), σ.Finite ∧ z ≫ π = spMap σ ≫ x := by
  have : CompactSpace ↥(pullback π x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (default : PrimeSpectrum K)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π x)) ⟨p, trivial⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback π x).fromSpecResidueField q ≫ pullback.snd π x)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨(pullback π x).residueField q, inferInstance, φ.hom,
    (pullback π x).fromSpecResidueField q ≫ pullback.fst π x, (IsFinite.SpecMap_iff φ).1 hf, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφ]
  rfl

theorem spMap_jK {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ jK R = jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem finite_fractionRing {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) : gam.Finite := by
  letI := g.toAlgebra
  letI := gam.toAlgebra
  have : Module.Finite R R₁ := hg
  have : IsScalarTower R (FractionRing R) (FractionRing R₁) := IsScalarTower.of_algebraMap_eq fun r => (h r).symm
  have : FaithfulSMul R R₁ := (faithfulSMul_iff_algebraMap_injective R R₁).2 fun a b e =>
    IsFractionRing.injective R (FractionRing R) (gam.injective (by
      rw [h, h]; exact congrArg _ e))
  show Module.Finite (FractionRing R) (FractionRing R₁)
  exact Module.Finite.of_isLocalization R R₁ (nonZeroDivisors R)

theorem exists_normalisation (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R) {R₁ : Type} [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) {L : Type} [Field L] {σ : FractionRing R₁ →+* L} (hσ : σ.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (_ : IsNoetherianRing R₂)
      (_ : IsIntegrallyClosed R₂) (_ : CharZero R₂) (g₂ : R₁ →+* R₂) (f : L →+* FractionRing R₂),
      (∀ r, (f.comp σ) (algebraMap R₁ _ r) = algebraMap R₂ _ (g₂ r)) ∧ (g₂.comp g).IsIntegral := by
  letI := (σ.comp gam).toAlgebra
  letI := ((σ.comp gam).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) L := hσ.comp (finite_fractionRing h hg)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hc L
  have hR : ∀ r, algebraMap R L r = σ (algebraMap R₁ _ (g r)) := fun r => congrArg σ (h r)
  have hi : ∀ r : R₁, (σ.comp (algebraMap R₁ (FractionRing R₁))) r ∈ integralClosure R L := fun r => by
    obtain ⟨p, hp, e⟩ := hg.to_isIntegral r
    refine ⟨p, hp, ?_⟩
    have e' := congrArg (σ.comp (algebraMap R₁ (FractionRing R₁))) e
    rw [Polynomial.hom_eval₂, map_zero] at e'
    rw [← e']
    congr 1
    exact RingHom.ext hR
  have hinj : Function.Injective (algebraMap R L) :=
    (σ.comp gam).injective.comp (IsFractionRing.injective R (FractionRing R))
  have : CharZero L := charZero_of_injective_algebraMap hinj
  let g₂ : R₁ →+* integralClosure R L := (σ.comp (algebraMap R₁ (FractionRing R₁))).codRestrict _ hi
  refine ⟨integralClosure R L, inferInstance, inferInstance, h₂, h₃, h₄, inferInstance, g₂,
    (FractionRing.algEquiv (integralClosure R L) L).symm.toRingHom, fun r => ?_, ?_⟩
  · exact (FractionRing.algEquiv (integralClosure R L) L).symm.commutes (g₂ r)
  · have e : g₂.comp g = algebraMap R (integralClosure R L) := RingHom.ext fun r => Subtype.ext (hR r).symm
    rw [e]
    exact (RingHom.finite_algebraMap.2 h₁).to_isIntegral

theorem arcBase_complete {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : ArcBase O' ϖ) :
    ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
  rcases h with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
  · letI := hF.toField
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨inferInstance, inferInstance, ?_⟩
    rwa [hi.maximalIdeal_eq]

theorem polAt_moduli {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K]
    (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have hm : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp := isGrpPullback_pullback Y.t.G (y ≫ Y.j)
  let ψ : ((Over.pullback (y ≫ Y.j)).obj Y.t.G).left ⟶ Y.oF.t.G.left :=
    hm.1.lift (pullback.fst Y.t.G.hom (y ≫ Y.j)) (pullback.snd Y.t.G.hom (y ≫ Y.j) ≫ y)
      (by rw [Category.assoc]; exact pullback.condition)
  have e₁ : ψ ≫ Y.m.φ = pullback.fst Y.t.G.hom (y ≫ Y.j) := hm.1.lift_fst _ _ _
  have hq : IsGrpPullback ((Over.pullback (y ≫ Y.j)).obj Y.t.G) Y.oF.t.G y ψ :=
    IsGrpPullback.cancel hm (hp.congr rfl e₁.symm) (hm.1.lift_snd _ _ _)
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have hI : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (pullback.fst Y.t.G.hom (y ≫ Y.j))) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L _ _ _ ψ fun _ => e₁.symm) ⟨w, hw⟩
  have := Y.oF.proper
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hq.1 Y.oF.proper,
    amplePt _ K y _ _ ψ hq _ _ Y.oF.t.PP.isLB (pull_isLB Y.t.PP.isLB _) hI.symm Y.oF.ample Y.oF.ktriv⟩

theorem exists_extension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  intro hL hL₂ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hO m Z π t mt hfin hsurj ⟨Am⟩ R₁ _ _ g y₁ gam hgam hg _ y hy hs
    ⟨θ₁, hθ₁⟩ ⟨n, f₁, hf₁⟩
  obtain ⟨_, _, hc⟩ := arcBase_complete hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨L, _, σ, z, hσ, hz⟩ := exists_lift_finite π (y₁ ≫ Y.j)
  obtain ⟨R₂, _, _, _, _, _, hch, g₂, f, hf, hint⟩ :=
    exists_normalisation (PowerSeries O') ReciprocityTheory.P1.isAdicComplete_ps hgam hg hσ
  have hx : (spMap f ≫ z) ≫ π = spMap (f.comp σ) ≫ y₁ ≫ Y.j := by
    rw [Category.assoc, hz, spMap_comp, Category.assoc]
  have hP := polAt_moduli Y y₁
  obtain ⟨θ, hθ, bθ⟩ := _root_.GlobalTheory.FramePull.frame_pull hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP 1 1 _ hθ₁
  obtain ⟨ff, hff, bff⟩ := _root_.GlobalTheory.FramePull.frame_pull hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP (m ^ 2) n _ hf₁
  obtain ⟨θ', rfl⟩ : ∃ θ', θ = fun _ : Fin 1 => θ' := ⟨θ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hab : Set.range (spMap f ≫ z) ⊆ abLocus t.G := by
    rintro _ ⟨p, rfl⟩
    refine (abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 (abLocusOne _ Y.t.G Y.t.semi _ _ hP.1 ?_)
    exact ⟨spMap (f.comp σ) p, (congrArg (fun q => q p) hx).symm⟩
  obtain ⟨e, he, hE⟩ := GlobalTheory.FrameGen.exists_gen_of_frames Z t.G t.PP.L t.PP.isLB (m ^ 2) Am Am.A rfl R₂ _ hab θ' n ff hθ hff bθ bff hch
  have := projProper _ _ _ Y.proj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ Y.s)
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ Y.s)
  have hG : ∀ r, ((f.comp σ).comp gam) (algebraMap (PowerSeries O') _ r) = algebraMap R₂ _ ((g₂.comp g) r) := fun r =>
    (congrArg (f.comp σ) (hgam r)).trans (hf _)
  have hx' : (spMap f ≫ z) ≫ π = spMap ((f.comp σ).comp gam) ≫ y ≫ Y.j := by
    rw [hx, ← hy, spMap_comp gam]
    simp only [Category.assoc]
  obtain ⟨χ₂, hχ₂⟩ := GlobalTheory.ExtLB.exists_extension Z Am.A Am.isLB Am.ample R₂ _ e he fun V _ _ _ hV φ gV hgV => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists (π ≫ Y.s) (spMap gV ≫ spMap f ≫ z)
      (spMap φ ≫ spMap (g₂.comp g) ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
        rw [Category.assoc, ← Category.assoc (spMap f ≫ z), hx', Category.assoc, Category.assoc, hs,
          ← Category.assoc (spMap _) (jK _), spMap_jK hG, Category.assoc, ← Category.assoc (spMap gV), spMap_jK hgV,
          Category.assoc])
    exact ⟨χ, hχ.symm, hE V hV φ gV hgV χ hχ.symm⟩
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.extension_descends_of_isIntegral _ R₂ _ _ hG hint Y.X (y ≫ Y.j) (χ₂ ≫ π)
    (by rw [← Category.assoc, hχ₂, hx'])
  exact ⟨χ, hχ⟩

end GlobalTheory.LN.ArcExtends
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.CubicalFibreAmple

section General
variable {X X' Y : Scheme.{0}}

theorem pw_pw (H : LB X) (a b : ℤ) : pw (pw H a) b = pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_linComb_pw {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Triv (LB.LinComb L φ ε)) (d : ℤ) : Triv (LB.LinComb (pw L d) φ ε) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_⟩
  have e := congrArg (· ^ d) (ht i j)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
  exact (zpow_comm _ _ _).trans (congrArg (· ^ ε k)
    ((map_zpow _ _ d).symm.trans (congrArg _ (map_zpow (pullU (φ k) _) _ d).symm)))

theorem exists_pull_mem {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ z, π z ∈ nonzeroLocus s → z ∈ nonzeroLocus t := by
  obtain ⟨t, ht⟩ := SpreadSec.exists_pull s π
  refine ⟨t, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := AmpleSpan.exists_chart_of_mem s hz
  refine (mem_nonzeroLocus t z).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩
  rw [ht (fun _ => k) z hk]
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s π z hk).1 hz

theorem exists_mem_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {M : LB X} (hM : M.IsLB) (σ : LB.Sec (M.pull π)) {z : X'} (hz : z ∈ nonzeroLocus σ) :
    ∃ u : LB.Sec M, π z ∈ nonzeroLocus u := by
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have e := (AmpleSpan.mem_nonzeroLocus_iff_gs σ (𝟙 X') z (k := fun _ => k) (mem_pull.2 hk)).1 hz
  rw [hu z k hk] at e
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum e
  exact ⟨u i, (AmpleSpan.mem_nonzeroLocus_iff_gs _ π z hk).2 (isUnit_of_mul_isUnit_right hi)⟩

theorem exists_finite_cover [CompactSpace X] {M : LB X} (s₀ : LB.Sec M)
    (h : ∀ x, ∃ u : LB.Sec M, x ∈ nonzeroLocus u) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec M => (nonzeroLocus u : Set X)) (fun u => (nonzeroLocus u).isOpen)
    (fun y _ => Set.mem_iUnion.2 (h y))
  refine ⟨F.card, Fin.cons s₀ (fun i => (F.equivFin.symm i : LB.Sec M)), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end General

theorem exists_mem_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left) (hN : N.IsLB)
    (s : LB.Sec N) (x : G.left) (hx : x ∈ nonzeroLocus s) :
    ∃ t : LB.Sec N, ∃ y ∈ nonzeroLocus t, G.hom y = IsLocalRing.closedPoint V := by
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  have hmax : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have : IsIntegral (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GeometricallyIntegral.geometrically_isIntegral (thick V (IsLocalRing.maximalIdeal V) 0) _ _
      (IsPullback.of_hasPullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 fun j => by
      refine eq_zero_of_basicOpen_eq_bot (X := pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) _
        (le_bot_iff.1 fun z hz => ?_)
      let p := pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0)
      have hz' : p z ∈ G.left.basicOpen (σ.f j) :=
        (SetLike.ext_iff.1 (Scheme.preimage_basicOpen p (σ.f j)) z).2 hz
      refine hcon σ (p z) (TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz'⟩) ?_
      have e : G.hom (p z) = thick V (IsLocalRing.maximalIdeal V) 0
          (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0) z) :=
        congrArg (fun q => q z) (pullback.condition (f := G.hom) (g := thick V (IsLocalRing.maximalIdeal V) 0))
      rw [e]
      refine PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top fun a ha => ?_).symm
      change Ideal.Quotient.mk _ a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ k, s.f k = 0 :=
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN s fun n =>
        (ThickDiv.main V ϖ hϖ G N s n).2 (h1 n s)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  rw [h2, Scheme.basicOpen_zero] at hk
  exact hk

theorem exists_valuationRing (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A] :
    ∃ (O : ValuationSubring (AlgebraicClosure (FractionRing A))) (g : A →+* O), g.Flat ∧ IsLocalHom g := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A (AlgebraicClosure (FractionRing A)))
  refine ⟨O, _, ?_, hl⟩
  have inj : Function.Injective (algebraMap A (AlgebraicClosure (FractionRing A))) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A)]
    exact (algebraMap (FractionRing A) _).injective.comp (IsFractionRing.injective A _)
  letI := ((algebraMap A (AlgebraicClosure (FractionRing A))).codRestrict O.toSubring h).toAlgebra
  refine Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (eq_bot_iff.2 ?_)
  rintro x ⟨⟨a, ha⟩, e⟩
  have e' : algebraMap A (AlgebraicClosure (FractionRing A)) a * x.1 = 0 := congrArg Subtype.val e
  exact Subtype.ext ((mul_eq_zero.1 e').resolve_left
    ((map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero ha)))

theorem relAmple_of_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  intro _ _ A _ _ _ _ _ B _ _ hB M h
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  have hL := M.L.isLB
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ _ _ (LB.isLB_pull hL _)).1 (h _ (jK A))
  have hH := isLB_pw hL d

  have h₁ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x, x ∈ nonzeroLocus σ := by
    have hσ : ∃ (σ : LB.Sec ((pw M.L.L d).pull (pullback.fst B.hom (jK A)))) (z : _), z ∈ nonzeroLocus σ := by
      rw [GlobalTheory.TrivLocus.pull_pw]
      have hz : (η[(Over.pullback (jK A)).obj B]).left (default : PrimeSpectrum (FractionRing A)) ∈
          ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨s i, _, hi⟩
    obtain ⟨σ, z, hz⟩ := hσ
    obtain ⟨u, hu⟩ := exists_mem_of_flat (algebraMap A (FractionRing A))
      (RingHom.flat_algebraMap_iff.2 inferInstance) (IsPullback.of_hasPullback B.hom (jK A)) hH σ hz
    exact ⟨u, _, hu⟩
  have h₂ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x ∈ nonzeroLocus σ, B.hom x = IsLocalRing.closedPoint A := by
    obtain ⟨σ, x, hx⟩ := h₁
    by_cases hA : IsLocalRing.maximalIdeal A = ⊥
    · refine ⟨σ, x, hx, PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top) ?_)⟩
      exact hA.le.trans bot_le
    · have : IsDiscreteValuationRing A := { not_a_field' := hA }
      exact exists_mem_closed_fibre A B hB _ hH σ x hx
  obtain ⟨σ, x, hx, hxc⟩ := h₂

  obtain ⟨O, g, hg, hl⟩ := exists_valuationRing A
  let t : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom g)
  let π := pullback.fst B.hom t
  have ht : Function.Surjective t := by
    letI := g.toAlgebra
    have : Module.Flat A O := hg
    have : IsLocalHom (algebraMap A O) := hl
    have : Module.FaithfullyFlat A O := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := O)
  have hB' := CubeGen.isAb_baseChange hB t
  obtain ⟨_, _, c, -⟩ := exists_isCPMap M (toBase_mul_pullback B t) _ (pull_isLB hL π) _ (pullIso_isGen hL π)
  have cube : Triv (Theta ((Over.pullback t).obj B) ((pw M.L.L d).pull π)) := by
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact triv_linComb_pw ⟨c.t, c.isGen⟩ d
  obtain ⟨σ', hσ'⟩ := exists_pull_mem σ π
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) x
    (IsLocalRing.closedPoint O) (hxc.trans (IsLocalRing.comap_closedPoint g).symm)
  have hu := SquareGenerated.exists_secs_sq_generate O (AlgebraicClosure (FractionRing A)) _ hB' _
    (LB.isLB_pull hH π) cube σ' ⟨z, hσ' z (by rw [← hz₁] at hx; exact hx), hz₂⟩
  rw [← GlobalTheory.TrivLocus.pull_pw, pw_pw, show (d : ℤ) * 2 = ((d * 2 : ℕ) : ℤ) by push_cast; rfl] at hu
  obtain ⟨m, u, hu⟩ := hu

  have hH₂ := isLB_pw hL ((d * 2 : ℕ) : ℤ)
  have gen : ∀ y, ∃ v : LB.Sec (pw M.L.L ((d * 2 : ℕ) : ℤ)), y ∈ nonzeroLocus v := fun y => by
    obtain ⟨q, hq⟩ := ht (B.hom y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) y q hq.symm
    have hw' : w ∈ ⨆ i, nonzeroLocus (u i) := by rw [hu]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hw'
    rw [← hw]
    exact exists_mem_of_flat g hg (IsPullback.of_hasPullback B.hom t) hH₂ (u i) hi
  obtain ⟨m', v, hv⟩ := exists_finite_cover (gen x).choose gen
  have aff := _root_.GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres A _ B.hom M.L.L (d * 2) m' v (by omega) hB.proper hL hv (fun q hq =>
    ⟨q.ResidueField, inferInstance, algebraMap A _, Ideal.ker_algebraMap_residueField q, h _ _⟩)
  obtain ⟨e, he, hw⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci A _ B.hom _ m' v hH₂ hv aff
  rw [pw_pw, ← Nat.cast_mul] at hw
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B M.L.L hL).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hw⟩

end GlobalTheory.CubicalFibreAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralGauge
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralGauge

theorem exists_chart_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (ψ : Sp V ⟶ X) : ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j := by
  have h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩

theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

theorem exists_integral_gauge (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) :
    ∃ J : (Sp F ⟶ D.P.A.left) → D.P.L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) ∧ ∀ x : TF (R := R) F ⟶ D.P.A,
      ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (J x.left) := by
  have key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧
      ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) →
        ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB x₀
      exact ⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB ψ
      exact ⟨j, hj, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩

end GlobalTheory.IntegralGauge
end

