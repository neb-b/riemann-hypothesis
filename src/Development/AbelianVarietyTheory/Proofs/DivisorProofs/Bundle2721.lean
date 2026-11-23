module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCover

theorem twistedKernel_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left]
    (N : LB (A ⊗ T).left), Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧
    IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧
    ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL hamp T _ N hN
  obtain ⟨T₀, φ, N₀, hT₀, hft, hN₀, hsame⟩ := GlobalTheory.DualApprox.exists_fam_finiteType R A hA T N hN
  obtain ⟨H₀, h₀, hci, hfin, hfl, hsurj, hrep⟩ := _root_.GlobalTheory.TwistKernel.twisted_kernel R A hA L hL hamp T₀ hft N₀ hN₀
  have sq₂ : IsPullback (A ◁ φ) (snd A T) (snd A T₀) φ := GlobalTheory.SS.TorusSlice.isPullback_whiskerLeft A φ
  have sq₁ : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ)) h₀ (A ◁ φ) :=
    IsPullback.of_hasPullback _ _
  have sq : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ) ≫ snd A T) (h₀ ≫ snd A T₀) φ :=
    sq₁.paste_vert sq₂
  have sq₁' := sq₁.map (Over.forget (Sp R))
  have sq' := sq.map (Over.forget (Sp R))
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine ⟨pullback h₀ (A ◁ φ), pullback.snd h₀ (A ◁ φ), ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq₁' hci
  · exact MorphismProperty.of_isPullback (P := @IsFinite) sq' hfin
  · exact MorphismProperty.of_isPullback (P := @Flat) sq' hfl
  · exact MorphismProperty.of_isPullback (P := @Surjective) sq' hsurj
  · intro Y a t

    have key : evc hN.isLB (fst A Y) (snd A Y ≫ t) = evc hN₀.isLB (fst A Y) (snd A Y ≫ t ≫ φ) := by
      have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ t)).left)
        ((same_iff hN.isLB hN₀.isLB (𝟙 T) φ).1 hsame)
      simpa only [pull_evc, lift_fst, lift_snd_assoc, lift_snd, Category.comp_id, Category.assoc] using e
    have e₁ : Same A (abelian₂ A L) N a t ↔ Same A (abelian₂ A L) N₀ a (t ≫ φ) := by
      rw [same_iff hΛ hN.isLB, same_iff hΛ hN₀.isLB, key]
    have e₂ : lift a (t ≫ φ) = lift a t ≫ (A ◁ φ) := by
      ext <;> simp
    rw [e₁, hrep, e₂]
    constructor
    · rintro ⟨z₀, hz₀⟩
      exact ⟨pullback.lift z₀ (lift a t) hz₀, pullback.lift_snd _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ pullback.fst h₀ (A ◁ φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, hz]⟩

end GlobalTheory.DualCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongPullTo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.TraitExt


open GlobalTheory.ArcPull in
theorem exists_unifAlong_pullTo : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f : T.V →+* V₂), IsCN V₂ → IsDiscreteValuationRing V₂ → Function.Injective f → f.Finite → IsLocalHom f → ∃ (D' : DegData V₂ (maximalIdeal V₂)) (_ : IsPullDeg f T.D.toPre D'.toPre) (G' : Over (Sp V₂)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V₂))) (U' : Unif (maximalIdeal V₂) D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' := by
  intro g n F T V₂ _ _ _ f hCN _ hinj hfin hloc
  obtain ⟨hN, hIC, hW, hC⟩ := hCN
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have hR' : AdmBase V₂ (maximalIdeal V₂) := ⟨hN, inferInstance, hIC, hW⟩
  have hI : (maximalIdeal T.V).map f ≤ maximalIdeal V₂ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨D', hD, A', U', gA, πK, gpA, tA, hK, hgen⟩ := exists_pull_gen hR hR' f hinj hI T.semi T.U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ T.A.A A'.A gA gpA
  have sq : spMap (fracMap hinj) ≫ jK T.V = jK V₂ ≫ spMap f :=
    (fracMap_sq hinj).symm.trans (Category.id_comp _)
  refine ⟨D', hD, (Over.pullback (spMap f)).obj T.G, inferInstance, inferInstance, pullback.fst T.G.hom (spMap f),
    A', U', ?_⟩
  refine ⟨isGrpPullback_pullback T.G (spMap f), spMap (fracMap hinj), πK, gA ≫ T.α, β₂ ≫ T.α₂, sq, hK,
    gpA.comp T.cart, isSquare_comp hβ₂ T.sq, hΛ T.A.L A'.L _ F.univ.P T.α₂ T.A.isLB A'.isLB F.univ.isLB tA T.lb, ?_⟩
  rw [← Category.assoc, hgen, Category.assoc]

end GlobalTheory.TraitExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UExt

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q f f rfl)

end GlobalTheory.Mum.UExt


open GlobalTheory.Mum.UExt in
theorem GlobalTheory.Mum.exists_unif_finExt_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨hdvr, hcomp, hchar⟩ := hR
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  obtain ⟨L', hL', hLL'⟩ := _root_.GlobalTheory.Mum.lb_extends_over_dvr R G (A.L.pull gen.hom.left) hL
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    _root_.GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen.hom hgen A.L _ A.isLB (LB.isLB_pull hL' _) A.sym hLL'
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R G hG hpr L' hL' hsym
  subst hP
  obtain ⟨R', _, _, _, ρ, G₁, _, _, β, β₂, P₁, A₁, gen₁, hR', hρ, hβ, hsq, hgen₁, hL₁, hLam, hEven⟩ :=
    _root_.GlobalTheory.Mum.exists_even_translate R ⟨hdvr, hcomp, hchar⟩ G hG P A gen hgen hLL'
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hchar⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (Geo.Tor.IsSemiAbelian.pullback (spMap ρ) G hG)
  obtain ⟨D, U, hU, -⟩ := _root_.GlobalTheory.Mum.exists_unif_even R' hB' G₁ P₁ hG₁ hEven A₁ gen₁ hgen₁ hL₁
  have hE : LBIso (abelian₂ G P.L.L) PP := _root_.GlobalTheory.Mum.lbIso_lam_of_extLam R G hG P.L.L _ PP P.L.isLB hL hLL' hPP
  refine ⟨R', _, _, _, ρ, D, G₁, _, _, β, β₂, A₁, U, hR', hρ, hβ, hsq, ?_⟩
  rw [hU]
  exact LBIso.trans (lam_isLB G₁ P₁.L.isLB) (LB.isLB_pull (lam_isLB G P.L.isLB) _) (LB.isLB_pull hPP.1 _) hLam
    (lbIso_pull hE β₂)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.HeckeUnif

open GlobalTheory.TangentOrigin

theorem existsUnique_linear_lift_of_hom :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
      SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e' : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (β : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e' → (∀ z w, β (z + w) = β z * β w) →
      IsHolTo Set.univ (fun z => (β z).left) → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = β z := by
  intro X G _ _ g hab hsm y e' β he' hβ hholG
  obtain ⟨Λ, hdisc, -, hker⟩ := _root_.GlobalTheory.ExpKernel.kernel_isFullLattice X G g hab hsm y e' he'
  letI : CommGroup (Over.mk y ⟶ G) := inferInstance
  let ex : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e' z)) he'.1
  let G' : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (β z)) hβ
  let pt : (Over.mk y).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (Over.mk y).left, q = pt := fun q ↦ Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (e' 0).left pt) (U := ⊤) (Set.mem_univ _)
  have h0 : ⊤ ≤ (e' 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker' : (ex.ker : Set (Fin g → ℂ)) = Λ := Set.ext fun z ↦ hker z
  have hS0 : (0 : Additive (Over.mk y ⟶ G)) ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U} := by
    rw [← map_zero ex]
    exact h0
  have hsep : ∀ a ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      ∀ b ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      (∀ s : Γ(G.left, U), valAt' (Additive.toMul a).left U s = valAt' (Additive.toMul b).left U s) → a = b := by
    intro a ha b hb h
    exact Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦
        (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))))
  have hSe : IsOpen {z : Fin g → ℂ | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    have := (he'.2.2.1 U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hSG : IsOpen {z : Fin g → ℂ | ⊤ ≤ (β z).left ⁻¹ᵁ U} := by
    have := (hholG U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfe : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (e' z).left U s) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    intro s
    have := (he'.2.2.1 U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfG : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (β z).left U s)
      {z | ⊤ ≤ (β z).left ⁻¹ᵁ U} := by
    intro s
    have := (hholG U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hD : ∀ w : Fin g → ℂ, (∀ s : Γ(G.left, U), fderiv ℂ (fun z ↦ valAt' (e' z).left U s) 0 w = 0) → w = 0 := by
    intro w hw
    obtain ⟨v, hv, -⟩ := he'.2.2.2.1 w
    obtain ⟨v0, hv0, -⟩ := he'.2.2.2.1 0
    have hvU : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff v.left U).2 (hv.1 ▸ h0)
    have hv0U : ⊤ ≤ v0.left ⁻¹ᵁ U := (top_le_preimage_iff v0.left U).2 (hv0.1 ▸ h0)
    have key : ∀ (u : Sp (DualNumber ℂ) ⟶ G.left) (hu : ⊤ ≤ u ⁻¹ᵁ U) (x : Sp ℂ ⟶ G.left) (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (s : Γ(G.left, U)), spMap fstC ≫ u = x → (evalPt u U hu s).fst = evalPt x U hx s := by
      rintro u hu x hx s rfl
      exact (evalPt_spMap_comp fstC u U hu hx s).symm
    have heq : v.left = v0.left := by
      refine ext_evalPt (R := DualNumber ℂ) hU hvU hv0U (RingHom.ext fun s ↦ TrivSqZeroExt.ext ?_ ?_)
      · exact (key _ hvU _ h0 s hv.1).trans (key _ hv0U _ h0 s hv0.1).symm
      · have a := hv.2 U hvU s
        have b := hv0.2 U hv0U s
        rw [map_zero] at b
        exact a.trans ((hw s).trans b.symm)
    have hv0' : IsDerivAt0 (fun z ↦ (e' z).left) w v0.left := heq ▸ hv
    exact (he'.2.2.2.2 v0 hv0.1).unique hv0' hv0
  obtain ⟨F, hF, hu⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') he'.2.1
    (hker' ▸ isDiscrete_iff_discreteTopology.2 hdisc)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(G.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    hS0 hsep hSe hSG hfe hfG hD
  exact ⟨F, hF, fun M hM ↦ hu M hM⟩

theorem eq_zero_of_real_smul_mem {g : ℕ} (A : AddSubgroup (Fin g → ℂ)) (hA : DiscreteTopology A) (z : Fin g → ℂ)
    (hz : ∀ r : ℝ, (r : ℂ) • z ∈ A) : z = 0 := by
  by_contra hne
  have hopen : IsOpen ({⟨0, A.zero_mem⟩} : Set A) := isOpen_discrete _
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.mp hopen
  have h0U : (0 : Fin g → ℂ) ∈ U := by
    have : (⟨0, A.zero_mem⟩ : A) ∈ Subtype.val ⁻¹' U := by rw [hUe]; rfl
    exact this
  have hc : Continuous (fun r : ℝ => (r : ℂ) • z) := by fun_prop
  have hV : IsOpen ((fun r : ℝ => (r : ℂ) • z) ⁻¹' U) := hU.preimage hc
  have h0 : (0 : ℝ) ∈ (fun r : ℝ => (r : ℂ) • z) ⁻¹' U := by simpa using h0U
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  have hr : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hmem : (⟨((ε / 2 : ℝ) : ℂ) • z, hz _⟩ : A) ∈ Subtype.val ⁻¹' U := hball hr
  rw [hUe] at hmem
  have h2 : ((ε / 2 : ℝ) : ℂ) • z = 0 := congrArg Subtype.val hmem
  rcases smul_eq_zero.mp h2 with h | h
  · have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h
    linarith
  · exact hne h

end GlobalTheory.HeckeUnif

namespace GlobalTheory.UPel.HT.Hecke

open GlobalTheory.UnifPull GlobalTheory.HeckeUnif

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOverOfClauses
section
noncomputable section

section WeilOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

theorem exists_weil_over_of_clauses (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {Γ : Type} [Group Γ] [Fintype Γ]
    {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hlev : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hmod : R.IsModels)
    (sc : Consts) (G : GridData R.toLevCh sc) : ∃ W : G.Weil, W.Over R := by
  have hψ := (hch.ωX A.μ0).std
  obtain ⟨W, hWψ⟩ := _root_.GlobalTheory.GridWeil.exists_weil hW D T R.toLevCh A.μ0 hlev sc G R.ψ hψ
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have lt : ∀ j, j < D.R.m → G.V (.grid 0 j) = Yc D j := fun j h => congrArg LSp.sp (colY_lt R.toLevCh h)
  have top : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m R.toLevCh)
  have h1 : ∀ X : Node, ∃ s B, (X.InRange D.R.m → IsMaj (G.V X) s B) ∧
      (∀ j, j < D.R.m → X = .grid 0 j → HEq s (cart (R.MY j)) ∧ HEq B (onb (R.MY j))) ∧
      (X = .grid 0 D.R.m → HEq s (cart R.MX) ∧ HEq B (onb R.MX)) := fun X => by
    by_cases h : ∃ j, j < D.R.m ∧ X = .grid 0 j
    · obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨s, B, a, b⟩ := exists_maj_heq (lt j hj) (R.MY j)
      refine ⟨s, B, fun _ => a, fun k _ hk => ?_, fun hk => ?_⟩
      · cases hk; exact b
      · exact absurd (Node.grid.inj hk).2 hj.ne
    by_cases h' : X = .grid 0 D.R.m
    · subst h'
      obtain ⟨s, B, a, b⟩ := exists_maj_heq top R.MX
      exact ⟨s, B, fun _ => a, fun k hk e => absurd ⟨k, hk, e⟩ h, fun _ => b⟩
    exact ⟨W.cart X, W.onb X, fun hX τ => ⟨W.cart_is X hX τ, W.onb_is X hX τ⟩, fun k hk e => absurd ⟨k, hk, e⟩ h,
      fun e => absurd e h'⟩
  have h2 : ∀ p : Pair T, ∃ ω, (p.InRange D.R.m → IsWeilDatumO R.ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) ω) ∧
      (∀ t k, k + 1 < D.R.m → p = .mu t 0 k → HEq ω (R.ωY t k)) ∧
      (∀ t k, k + 1 = D.R.m → p = .mu t 0 k → HEq ω (R.ωX t)) := fun p => by
    by_cases h : ∃ t k, k + 1 < D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h
      have := hch.ωY t k hk
      rw [← G.chr_mu_zero t hk.le] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (lt k (by omega)) (lt (k + 1) hk) this
      refine ⟨ω, fun _ => a, fun t' k' _ e => ?_, fun t' k' hk' e => ?_⟩
      · cases e; exact b
      · cases e; omega
    by_cases h' : ∃ t k, k + 1 = D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h'
      have e0 := G.chr_mu_zero t hk.le
      rw [hk] at e0
      have := hch.ωX t
      rw [← e0] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (S' := G.V (.grid 0 k)) (T' := G.V (.grid 0 (k + 1)))
        ((lt k (by omega)).trans (congrArg (Yc D) (by omega))) (hk ▸ top) this
      refine ⟨ω, fun _ => a, fun t' k' hk' e => ?_, fun t' k' _ e => ?_⟩
      · cases e; omega
      · cases e; exact b
    exact ⟨W.om p, fun hp => hWψ ▸ W.om_is p hp, fun t k hk e => absurd ⟨t, k, hk, e⟩ h,
      fun t k hk e => absurd ⟨t, k, hk, e⟩ h'⟩
  choose s B hs sY sX using h1
  choose om hom oY oX using h2
  obtain ⟨W', a1, a2, a3, a4, a5⟩ := exists_weil G (fun i hi => by
    have : (G.node (.grid i 0)).IsV (rankV D i 0) ((D.R.m - 0) / 2) := by
      cases i with
      | zero => exact _root_.GlobalTheory.ChiGrid.colY_isV D T R.toLevCh A.μ0 hlev 0 hi
      | succ i => exact G.sp.V_is (i + 1) 0 (by omega) hi (Nat.zero_le _)
    exact ⟨this.sigOK, this.sd⟩) he hψ hmod.inf s B hs om hom
  exact ⟨W', a1, a2, fun j hj => a3 ▸ (sY _ j hj rfl).1, a3 ▸ (sX _ rfl).1, fun j hj => a4 ▸ (sY _ j hj rfl).2,
    a4 ▸ (sX _ rfl).2, fun t k hk => a5 ▸ oY _ t k hk rfl, fun t k hk => a5 ▸ oX _ t k hk rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end WeilOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoi
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem finite_orbits_of_finite_pts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  intro p _ G v wt Kf f hfi K' f' hfi' β x t hx hT
  let F : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
    Quot.lift (orbOfDat G v β x t hx Kf K') (fun a b h => orbOfDat_eq_of_same G v β x t hx _ _ h)
  let PL : Pts G v β x t hx Kf K' → Prop :=
    Quot.lift (DatWt G v β x t hx f f') (fun a b h => propext (datWt_iff_of_same G v β x t hx _ _ hfi hfi' h))
  refine (hT.image F).subset ?_
  rintro o ⟨y, hy⟩
  unfold cxF at hy
  split_ifs at hy with hc
  on_goal 2 => exact absurd rfl hy
  let d : Dat G v β := (LeftCosets.rep _ _ (Quotient.out o).1,
    ⟨Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)), hc.1⟩)
  have hd : DatWt G v β x t hx f f' d := ⟨y, hc.2, left_ne_zero_of_mul hy⟩
  refine ⟨Quot.mk _ d, ?_, ?_⟩
  · have e : PL (Quot.mk _ (Quot.out (Quot.mk (Same G v β x t hx Kf K') d))) = PL (Quot.mk _ d) :=
      congrArg PL (Quot.out_eq _)
    exact (e : DatWt G v β x t hx f f' _ = DatWt G v β x t hx f f' d).mpr hd
  · show orbOfDat G v β x t hx Kf K' d = o
    simp only [orbOfDat, d, LeftCosets.mk_rep]
    convert Quotient.out_eq' o using 2
    exact Prod.ext rfl (Projectivization.mk_rep _)

end GlobalTheory.CxUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  first | exact @GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_equivariant_torsion_values_ultrametric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  first | exact @GlobalTheory.Mum.Recog.recognition_core | exact GlobalTheory.Mum.Recog.recognition_core | (intros; apply GlobalTheory.Mum.Recog.recognition_core <;> assumption)
end

