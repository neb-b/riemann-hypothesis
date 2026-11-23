module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem FrameCarried.exists_near_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hnz y hyc hy
  obtain ⟨R₁, _, _, _, ρ₁, hF₁, hE₁, V₀, hV₀, τ, hτ, hτc⟩ := _root_.GlobalTheory.Mum.exists_carried_frame_upstairs R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y hyc hy
  exact _root_.GlobalTheory.Mum.FrameCarried.descend_finiteEtale R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact R₁ ρ₁ hF₁ hE₁ V₀ y hV₀ τ hτ hτc

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.Mum GlobalTheory.Mum.Conj in
theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (_root_.GlobalTheory.Mum.Conj.secTw_bijective R A N σ).comp (hE.bij.comp (_root_.GlobalTheory.Mum.Conj.FamBij.famTw_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add R A N σ _ _ _ (hE.add _ _ _ (_root_.GlobalTheory.Mum.Conj.famTw_add_f R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (_root_.GlobalTheory.Mum.Conj.famTw_isSmul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (_root_.GlobalTheory.Mum.Conj.txFrame_frTw R D.toPre N τ p p₀ hp₀ w hw) (GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint R A N τ _ _ θ hθ hx) (_root_.GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [_root_.GlobalTheory.Mum.Conj.famTw_eq_of_over R _ D.toPre N τ F₀ s hs]
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate R A N σ (E s)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_invariant_nbhd_of_orbits {X : Scheme.{0}} [X.IsSeparated] {Γ : Type} [Group Γ] [Finite Γ]
    (act : Γ → (X ⟶ X)) (act_one : act 1 = 𝟙 X) (act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ)
    (Z : Set X) (hZ : IsCompact Z)
    (horb : ∀ z ∈ Z, ∃ O : X.Opens, IsAffineOpen O ∧ ∀ σ, act σ z ∈ O) :
    ∃ H : X.Opens, (∀ σ, act σ ⁻¹ᵁ H = H) ∧ (∀ z ∈ Z, z ∈ H) ∧ IsCompact (H : Set X) ∧
      (∀ x ∈ H, ∃ O : X.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) := by
  classical
  have hiso : ∀ σ, IsIso (act σ) := fun σ =>
    ⟨act σ⁻¹, by rw [← act_mul, mul_inv_cancel, act_one], by rw [← act_mul, inv_mul_cancel, act_one]⟩
  have hmul : ∀ σ τ (x : X), act (σ * τ) x = act τ (act σ x) := fun σ τ x => by
    rw [act_mul, Scheme.Hom.comp_apply]
  have hone : ∀ x : X, act 1 x = x := fun x => by rw [act_one]; rfl
  have hW : ∀ z : Z, ∃ V : X.Opens, IsAffineOpen V ∧ z.1 ∈ V ∧ ∀ σ, ∀ x ∈ V, act σ x ∈ V := by
    intro z
    obtain ⟨O, hO, hz⟩ := horb z.1 z.2
    have hmem : ∀ x : X, x ∈ (⨅ σ, act σ ⁻¹ᵁ O) ↔ ∀ σ, act σ x ∈ O := fun x => by
      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      rfl
    refine ⟨⨅ σ, act σ ⁻¹ᵁ O, IsAffineOpen.iInf fun σ => ?_, (hmem _).2 hz, fun σ x hx => (hmem _).2 fun τ => ?_⟩
    · have := hiso σ
      exact hO.preimage (act σ)
    · rw [← hmul]
      exact (hmem _).1 hx _
  choose V hV hzV hVa using hW
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun z : Z => (V z : Set X)) (fun z => (V z).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
  have hH : ∀ x : X, x ∈ (⨆ z ∈ t, V z) ↔ ∃ z ∈ t, x ∈ V z := fun x => by
    simp [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⨆ z ∈ t, V z, fun σ => ?_, fun z hz => ?_, ?_, fun x hx => ?_⟩
  · ext x
    change act σ x ∈ (⨆ z ∈ t, V z) ↔ x ∈ (⨆ z ∈ t, V z)
    rw [hH, hH]
    refine ⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, ?_⟩, fun ⟨z, hz, hx⟩ => ⟨z, hz, hVa z σ x hx⟩⟩
    have := hVa z σ⁻¹ _ hx
    rwa [← hmul, mul_inv_cancel, hone] at this
  · rw [hH]
    simpa using ht hz
  · have : ((⨆ z ∈ t, V z : X.Opens) : Set X) = ⋃ z ∈ t, (V z : Set X) := by
      ext x
      rw [SetLike.mem_coe, hH]
      simp
    rw [this]
    exact t.isCompact_biUnion fun z _ => (hV z).isCompact
  · obtain ⟨z, hz, hx⟩ := (hH x).1 hx
    exact ⟨V z, hV z, fun y hy => (hH y).2 ⟨z, hz, hy⟩, fun σ => hVa z σ x hx⟩

theorem eq_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {ρ : R →+* R'} (hρ : ρ.Finite) (p : Sp R') (hp : spMap ρ p = closedPoint R) : p = closedPoint R' := by
  have h₁ : Ideal.comap ρ (PrimeSpectrum.asIdeal p) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
  have h₂ : (PrimeSpectrum.asIdeal p).IsMaximal := by
    have := PrimeSpectrum.isPrime p
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ ?_
    rw [h₁]
    infer_instance
  exact PrimeSpectrum.ext (eq_maximalIdeal h₂)

theorem exists_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hS U' a
  classical
  have := hR.2
  have hR' : Base R' := ⟨hρ.1, charZero_of_injective_ringHom hρ.2.1⟩
  have := hG.1
  have := Fintype.ofFinite (Gal ρ)
  have := hS.separated
  have := hS.quasiCompact
  have : G'.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G'.hom]
    infer_instance⟩
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  have hover : ∀ (σ : Gal ρ) (g : G'.left), spMap ρ (G'.hom (a.act σ g)) = spMap ρ (G'.hom g) := fun σ g => by
    have h₁ : a.act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ) := (a.cart σ).1.w
    have h₂ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact σ.2 r
    rw [← Scheme.Hom.comp_apply (a.act σ), h₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (spMap (Gal.hom σ)), h₂]
  have hZ : IsClosed {g : G'.left | spMap ρ (G'.hom g) = closedPoint R} :=
    (isClosed_singleton_closedPoint R).preimage ((spMap ρ).continuous.comp G'.hom.continuous)
  refine exists_invariant_nbhd_of_orbits a.act a.act_one a.act_mul _ hZ.isCompact fun z hz => ?_
  obtain ⟨O, hO, h⟩ := _root_.GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen R' hR' D' A' G' hS U' (Finset.univ.image fun σ => a.act σ z) (fun x hx => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
    exact eq_closedPoint_of_finite hρ.2.2 _ ((hover σ z).trans hz))
  exact ⟨O, hO, fun σ => h _ (Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩)⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrame
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GenericCell

theorem upM_zero_eq {ι : Type} {m : ι → ℕ} {K : Type} [Field K] : upM (0 : Cell m → K) = 1 := by
  funext τ
  ext a b
  simp only [upM, upU, Matrix.of_apply, Pi.zero_apply, Pi.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem exists_inCell_genericPoint : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  intro F _ X Y ι _ m E E' φ f hR z A hA
  have hgX : A ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA
  have hcp : (ratOf X).pt (IsLocalRing.closedPoint X.Fn) = genericPoint X.X := Scheme.fromSpecStalk_closedPoint
  obtain ⟨p, ⟨hpf, hpb⟩, -⟩ := hR.lifts X.Fn (ratOf X).pt A (hcp ▸ hgX) (upM 0) (by rw [upM_zero_eq]; exact Par.one)
  have hfp : f (p (IsLocalRing.closedPoint X.Fn)) = genericPoint X.X := by
    have h1 := congrArg (fun g : Sp X.Fn ⟶ X.X => g (IsLocalRing.closedPoint X.Fn)) hpf
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1.trans hcp
  obtain ⟨u, hu, -⟩ := (_root_.GlobalTheory.FlagCell2.BearsCell.bears_iff F X Y ι m E E' φ f hR A X.Fn p (hfp ▸ hgX) 0).1 hpb
  refine ⟨u, Fr.mem_of_specializes (hfp ▸ hgX) ((genericPoint_specializes _).map f.continuous), Fr.mem_genericPoint hu⟩

end GlobalTheory.FlagCell2.GenericCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GeoDesc

theorem exists_geomIso_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧ (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) ∧ GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hloc D' G' _ _ A' hD hG hU hS
  haveI : CharZero R := hR.2
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (f := (algebraMap (FractionRing R) (Kb R)).comp
    (algebraMap R (FractionRing R))) ((algebraMap (FractionRing R) (Kb R)).injective.comp
      (IsFractionRing.injective R (FractionRing R)))
  let φK : FractionRing R →+* FractionRing W :=
    IsFractionRing.lift (g := (algebraMap W (FractionRing W)).comp φ) ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp φK).toAlgebra
  haveI : Module.IsTorsionFree (FractionRing R) (Kb W) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (FractionRing R) (Kb R) := DivisionSemiring.to_moduleIsTorsionFree
  let e₀ : Kb R →+* Kb W := (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W).toRingHom
  have he₀ : ∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := by
    intro r
    show (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W) (algebraMap _ _ _) = _
    rw [AlgHom.commutes]
    show algebraMap (FractionRing W) (Kb W) (φK _) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  obtain ⟨B, b, hB⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds (algebraMap (FractionRing W) (Kb W)) A'
  have hth : ∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R),
      (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧
      IsThetaPt B (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of (Kb W))).inv.hom (e₀ (v i)) := by
    intro j hj
    obtain ⟨C, _, jC, Ix, x, v, hcov, htor, hC⟩ :=
      _root_.GlobalTheory.Mum.FibreTheta.theta_consts_algebraic R hR D n hn ho hu W hW φ hφ hloc D' G' A' hD hG hU e₀ he₀ B b hB.2.1 hB.2.2.symm j hj
    exact ⟨Ix, x, v, hcov, GlobalTheory.Mum.ThetaDown.isThetaPt_of_map (Sp (Kb W)) B (Kb W) C jC (𝟙 _) (spMap jC) (Category.comp_id _) (n ^ j) Ix x
      (fun i => e₀ (v i)) htor hC⟩
  obtain ⟨A₀, a, ha, hLa⟩ := _root_.GlobalTheory.ThetaDescent.descends (Kb R) (Kb W) e₀ B n hn ho hth
  refine ⟨A₀, e₀, he₀, ?_, B, a, b, ha, hLa, hB.2.1, hB.2.2.symm⟩
  exact GlobalTheory.SymDescentAlgClosed.hypS_of_baseChange (Kb R) (Kb W) e₀ A₀ B a ha hLa (GlobalTheory.T.lineBundleSymmetryHypothesis_baseChange _ _ _ A' B b hB hS)

end GlobalTheory.Mum.GeoDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrder
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LKGeo.CommBC

theorem actOn_tmul_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (a b : R) (c : C) (v : V) :
    actOn rep R (a ⊗ₜ c) (b ⊗ₜ v) = (a * b) ⊗ₜ rep c v := by
  have : actOn rep R (a ⊗ₜ c) = Algebra.ofId R _ a * Module.End.baseChangeHom ℚ R V (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ a c
  rw [this, Module.End.mul_apply]
  simp only [Algebra.ofId_apply, Module.algebraMap_end_apply]
  change a • (LinearMap.baseChange R (rep c)) (b ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem exists_actOn_eq {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) {ι' : Type} (S : ι' → Module.End ℚ V)
    (hrange : ∀ B : Module.End ℚ V, (∀ b, B * S b = S b * B) → ∃ x, rep x = B)
    (R : Type) [CommRing R] [Algebra ℚ R] (A : Module.End R (R ⊗[ℚ] V))
    (hA : ∀ b, A * (S b).baseChange R = (S b).baseChange R * A) : ∃ y, actOn rep R y = A := by
  classical
  let r := Module.Free.chooseBasis ℚ R
  let e : R ⊗[ℚ] V ≃ₗ[ℚ] (Module.Free.ChooseBasisIndex ℚ R →₀ V) :=
    (LinearEquiv.rTensor V r.repr).trans (TensorProduct.finsuppScalarLeft ℚ V _)
  have he : ∀ (a : R) (v : V) k, e (a ⊗ₜ v) k = r.repr a k • v := by
    intro a v k
    simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  let Ak : Module.Free.ChooseBasisIndex ℚ R → Module.End ℚ V := fun k =>
    (Finsupp.lapply k) ∘ₗ e.toLinearMap ∘ₗ (A.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ R V 1)
  have hAk : ∀ k v, Ak k v = e (A (1 ⊗ₜ v)) k := fun k v => rfl
  have heS : ∀ (s : Module.End ℚ V) (x : R ⊗[ℚ] V) k, e (s.baseChange R x) k = s (e x k) := by
    intro s x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [he]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hcomm : ∀ k b, Ak k * S b = S b * Ak k := by
    intro k b; ext v
    simp only [Module.End.mul_apply, hAk]
    have := congrArg (fun f => f ((1 : R) ⊗ₜ v)) (hA b)
    simp only [Module.End.mul_apply, LinearMap.baseChange_tmul] at this
    rw [this, heS]
  choose x hx using fun k => hrange (Ak k) (hcomm k)
  let bV := Module.finBasis ℚ V
  let F := Finset.univ.biUnion fun i => (e (A ((1 : R) ⊗ₜ bV i))).support
  have hzero : ∀ k ∉ F, Ak k = 0 := by
    intro k hk
    refine bV.ext fun i => ?_
    rw [hAk, LinearMap.zero_apply]
    by_contra h
    exact hk (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  refine ⟨∑ k ∈ F, r k ⊗ₜ x k, ?_⟩
  have h1 : ∀ v, actOn rep R (∑ k ∈ F, r k ⊗ₜ x k) ((1 : R) ⊗ₜ v) = A ((1 : R) ⊗ₜ v) := by
    intro v
    apply e.injective
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    simp_rw [actOn_tmul_tmul, _root_.mul_one, hx, he, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul]
    rw [Finset.sum_ite_eq', ← hAk]
    split_ifs with hj
    · rfl
    · rw [hzero j hj, LinearMap.zero_apply]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have : a ⊗ₜ[ℚ] v = a • ((1 : R) ⊗ₜ v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rw [this, map_smul, map_smul, h1]

theorem exists_actOn_eq_of_commute : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
    (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) →
    ∃ y, actOn L.rep (AfP p) y = A := by
  intro p _ D G L A hA
  haveI := D.finLa
  exact exists_actOn_eq L.rep (actQ D) (fun B hB => (L.rep_range B).mpr hB) (AfP p) A hA

end GlobalTheory.LKGeo.CommBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubscheme
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix


open GlobalTheory.Mean4O.CombForm in
theorem exists_subAtlas : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp π _ hπ e A hA hs
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, h⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, h, hπ]⟩
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hq
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hp
  have hc : Continuous (ptMap π hπ σ) := PtsOver.continuous_map π hπ _
  have hinj : Function.Injective (ptMap π hπ σ) := fun a b h =>
    Subtype.ext ((cancel_mono π).1 (congrArg Subtype.val h))
  have hE : IsClosedEmbedding (ptMap π hπ σ) := hc.isClosedEmbedding hinj
  let h : CxPts q σ ≃ₜ Set.range (ptMap π hπ σ) := hE.isEmbedding.toHomeomorph
  haveI : CompactSpace (Set.range (ptMap π hπ σ)) := h.compactSpace
  let A' : FinHolAtlas e (CxPts q σ) := (AnRead.all q σ e).finAtlas
  have hA' : IsAlgAtlas A' := AnRead.isAlgAtlas_finAtlas _
  have hm : HoloMap A' A (ptMap π hπ σ) := hA.holoMap hA' (f := π) fun _ => rfl
  have hB : HoloMap (tAtlas A' h) A Subtype.val := ⟨continuous_subtype_val, fun j l => hm.2 j l⟩
  refine ⟨tAtlas A' h, hB, fun L v hv => ?_⟩
  have hsm (i : Fin e) : (L i).φ.IsSmooth hA.anRead := (Weight.isCInf_iff_isSmooth _).1 (L i).cInf
  have hv' : Continuous fun y => v (ptMap π hπ σ y) := hv.comp hc
  have hP (i : Fin e) : IsPotential A' ((L i).pull π hπ).φ.locPot :=
    Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth _).1 ((L i).pull π hπ).cInf)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact k Y q σ e A' hA' (fun i => (L i).pull π hπ) _ hv'.measurable
  rw [h₂ (h₁.2 (mIntegrableCont _ _ hP _ hv')),
    GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport e _ _ A' h _ _
      (fun i => isPotentialPullback A _ _ hB _ ((hsm i).isPotential hA))
      (hv.comp continuous_subtype_val)]
  exact (SameForm.mInt_eq (fun i => (hsm i).sameForm_pull hA hA' π hπ) _).symm

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieCondition_summand_residueCharP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | exact @GlobalTheory.HTSummand.Corep.exists_summand_lie_p | exact GlobalTheory.HTSummand.Corep.exists_summand_lie_p | (intros; apply GlobalTheory.HTSummand.Corep.exists_summand_lie_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSecStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  first | exact @GlobalTheory.IsoLin.exists_linearisation_isotropic | exact GlobalTheory.IsoLin.exists_linearisation_isotropic | (intros; apply GlobalTheory.IsoLin.exists_linearisation_isotropic <;> assumption)
end

