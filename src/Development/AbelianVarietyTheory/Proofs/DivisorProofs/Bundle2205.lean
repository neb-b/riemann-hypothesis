module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem comp_one₂ {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

theorem pullUnivP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ actH Y u AE _ φE ηE hE hηu huniv T g AT _ φ act eta hT hact heta
  let Tg : Over H := Over.mk g
  let e : Tg ⟶ Over.mk ((𝟙_ (Over T)).hom ≫ g) := Over.homMk (𝟙 T) (by simp [Tg])
  let u' : D.La → (Tg ⟶ AH) := fun x => e ≫ pushHom hT (𝟙_ (Over T)) (eta x)
  have hu'l : ∀ x, (u' x).left = (eta x).left ≫ φ := fun x => by
    show 𝟙 T ≫ (eta x).left ≫ φ = _
    rw [Category.id_comp]
  have hadd : ∀ x y, u' (x + y) = u' x * u' y := fun x y => by
    show e ≫ pushHom hT _ (eta (x + y)) = (e ≫ pushHom hT _ (eta x)) * (e ≫ pushHom hT _ (eta y))
    rw [heta.1, map_mul, MonObj.comp_mul]
  have hlin : ∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c := fun c x => by
    apply Over.OverMorphism.ext
    show (u' (c • x)).left = (u' x ≫ actH.act c).left
    rw [hu'l, Over.comp_left, hu'l, heta.2.1, Over.comp_left, Category.assoc, hact, Category.assoc]
  have hker : ∀ x, u' (N • x) = 1 := fun x => by
    show e ≫ pushHom hT _ (eta (N • x)) = 1
    rw [heta.2.2, map_one, comp_one₂]
  obtain ⟨h, hh, hun⟩ := huniv Tg u' hadd hlin hker
  have hz : h.left ≫ Y.hom = g := Over.w h
  have hw : φ ≫ AH.hom = (AT.hom ≫ h.left) ≫ Y.hom := by rw [hT.1.w, Category.assoc, hz]
  let ψ : AT.left ⟶ AE.left := hE.1.lift φ (AT.hom ≫ h.left) hw
  have hψ₁ : ψ ≫ φE = φ := hE.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ AE.hom = AT.hom ≫ h.left := hE.1.lift_snd _ _ _
  have hhl : ∀ y, h.left ≫ (u y).left = (eta y).left ≫ φ := fun y => by
    rw [← Over.comp_left, hh y, hu'l]
  refine ⟨h.left, ⟨hz, ψ, ?_, hψ₁, fun y => ?_⟩, ?_⟩
  · exact IsGrpPullback.cancel hE (hT.congr hz.symm hψ₁.symm) hψ₂
  · apply hE.1.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hηu, hhl]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (eta y), Category.assoc, Over.w (ηE y)]
      rfl
  · rintro z₂ ⟨hz₂, ψ₂, -, hψ₂₁, he₂⟩
    let h₂ : Tg ⟶ Y := Over.homMk z₂ hz₂
    have : h₂ = h := hun h₂ fun x => by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu'l]
      show z₂ ≫ (u x).left = _
      rw [← hηu, ← Category.assoc, ← he₂, Category.assoc, hψ₂₁]
    exact congrArg (fun k => k.left) this

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory

theorem basisLin_oLinear : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  intro p _ D H Y AH _ _ actH u hu ιO ιL bO bL hb

  have hcomp : ∀ (f : Y ⟶ AH) (b c : D.O), f ≫ actH.act (b + c) = (f ≫ actH.act b) * (f ≫ actH.act c) := by
    intro f b c
    rw [actH.add, MonObj.comp_mul]

  have u0 : u 0 = 1 := by
    have h := hu 0 0
    simp only [add_zero] at h
    have := congrArg (fun t => t * (u 0)⁻¹) h
    simpa using this.symm
  let U : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x)
      map_zero' := by simp [u0]
      map_add' := fun x y => by simp [hu] }

  have step1 : ∀ i (c : D.O), u (c • bL i) = u (bL i) ≫ actH.act c := by
    intro i
    let F : D.O →+ Additive (Y ⟶ AH) := U.comp ((LinearMap.toSpanSingleton D.O D.La (bL i)).toAddMonoidHom)
    let G : D.O →+ Additive (Y ⟶ AH) :=
      { toFun := fun c => Additive.ofMul (u (bL i) ≫ actH.act c)
        map_zero' := by
          have h := hcomp (u (bL i)) 0 0
          simp only [add_zero] at h
          have : u (bL i) ≫ actH.act 0 = 1 := by
            have := congrArg (fun t => t * (u (bL i) ≫ actH.act 0)⁻¹) h
            simpa using this.symm
          simp [this]
        map_add' := fun b c => by simp [hcomp] }
    have hFG : F.toIntLinearMap = G.toIntLinearMap := bO.ext fun j => by
      simp [F, G, U, hb]
    intro c
    have := congrArg (fun L => L c) hFG
    simpa [F, G, U] using this
  intro c
  let F : D.La →+ Additive (Y ⟶ AH) := U.comp (DistribSMul.toAddMonoidHom D.La c)
  let G : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x ≫ actH.act c)
      map_zero' := by
        haveI := actH.hom c
        simp [u0, MonObj.one_comp]
      map_add' := fun x y => by
        haveI := actH.hom c
        simp [hu, MonObj.mul_comp] }
  have hFG : F.toIntLinearMap = G.toIntLinearMap := bL.ext fun i => by
    simp [F, G, U, step1]
  intro x
  have := congrArg (fun L => L x) hFG
  simpa [F, G, U] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem obstructionPullback_eq_zero_of_naturalLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l C'' _ F'' L'' m u v hl hu hun hvp hvn w c hc
  obtain ⟨κ, σ', z, hκ, hσ', rfl, hz⟩ := hc
  choose σ'' hσ'' using fun T : C'' ↦ _root_.GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T)

  have hdiff : ∀ (T : C'') (b : L.B (n.G.obj (m.G.obj T))),
      (u T).comp (l (m.G.obj T)) b - v T b ∈ I.map (algebraMap R (L''.B T)) := fun T b ↦ by
    refine (L''.ker T _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (hu T _).trans ((congrArg (m.α T) (hl _ b)).trans (hvp T b).symm)
  choose th hth using fun T : C'' ↦ ((theta_classify R R₀ (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T)))
    (L''.B T) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) ((u T).comp (l (m.G.obj T)))).1 (v T) (hdiff T)).exists

  have key : ∀ (T T' : C'') (a : T ⟶ T'),
      L''.ρ a (th T (w.1 (n.G.obj (m.G.obj T)))) =
        u T' (κ _ _ (m.G.map a) (w.1 (n.G.obj (m.G.obj T)))) + th T' (w.1 (n.G.obj (m.G.obj T'))) := by
    intro T T' a
    have h1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L'.B (m.G.obj T')) (L''.B T') _ _ _ (hκ _ _ (m.G.map a))).1 (u T')
    have h2 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T'))) (F.obj (n.G.obj (m.G.obj T'))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T') (L''.B T') _ _ _ (hth T')).2 (L.ρ (n.G.map (m.G.map a)))
      (mp F (n.G.map (m.G.map a))) (fun x ↦ L.nat _ x)
    rw [AlgHom.comp_assoc] at h2
    have h3 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ _ _ _ h1).2.1 h2
    have h4 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T) (L''.B T') _ _ _ (hth T)).1 (L''.ρ a)
    have e1 : (L''.ρ a).comp ((u T).comp (l (m.G.obj T))) =
        (u T').comp ((L'.ρ (m.G.map a)).comp (l (m.G.obj T))) := AlgHom.ext fun b ↦ hun a _
    have e2 : (L''.ρ a).comp (v T) = (v T').comp (L.ρ (n.G.map (m.G.map a))) := AlgHom.ext fun b ↦ hvn T T' a b
    rw [e1, e2] at h4
    have h5 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ ((v T').comp (L.ρ (n.G.map (m.G.map a)))) _ _ h4).2.2 |>.1 <| h3
    have h6 := DFunLike.congr_fun h5 (w.1 (n.G.obj (m.G.obj T)))
    rw [w.2 (n.G.map (m.G.map a))]
    exact h6
  choose g hgK hg using fun T : C'' ↦ (_root_.GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T) (σ'' T) (hσ'' T)).2.2.2 (-(th T (w.1 (n.G.obj (m.G.obj T)))))
    (neg_mem ((hth T).mem _))
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  refine ⟨g, ?_⟩
  funext T T' a
  have sg := _root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T) (L''.semi T) (L''.surj T)
    (L''.ker T) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (L''.ρ a) (mp F'' a)
    (fun b ↦ L''.nat a b) (σ'' T) (σ'' T') (hσ'' T) (hσ'' T')
  have su := _root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L'.B (m.G.obj T')) (F'.obj (m.G.obj T')) (L'.p _) (L'.semi _)
    (L'.surj _) (L'.ker _) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (u T')
    (coefHom m T') (fun b ↦ hu T' b) (σ' _) (σ'' T') (hσ' _) (hσ'' T')
  haveI : Algebra.Smooth R (L''.B T') := L''.smooth T'
  change g T' - extHom R₁ (mp F'' a) (g T) = extHom R₁ (coefHom m T') (z.1 _ _ (m.G.map a))
  refine sub_eq_zero.1 (_root_.GlobalTheory.Obs.sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L''.B T') (F''.obj T') (L''.p T') (L''.semi T')
    (L''.surj T') (L''.ker T') (σ'' T') (hσ'' T') _ ?_ ?_)
  · have k1 := hgK T'
    have k2 := sg.2 _ (hgK T)
    have k3 := su.2 _ (hz _ _ (m.G.map a)).1
    unfold Aug.KerQ at k1 k2 k3 ⊢
    rw [map_sub, map_sub, k1, k2, k3, sub_zero, sub_zero]
  · rw [map_sub, map_sub, hg T', ← sg.1, hg T, ← su.1, (hz _ _ _).2, map_neg, key T T' a]
    abel

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.ord_fnPull_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  intro k _ X Y _ _ p s _ hs E' E h g
  let φ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring fun a => (h _).1 a.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hs.1 (congrArg Subtype.val e)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hs.2 (b : Y.functionField)
    exact ⟨⟨a, (h a).2 (ha ▸ b.2)⟩, Subtype.ext ha⟩
  let e : E.ring ≃+* E'.ring := RingEquiv.ofBijective φ hφ
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, u, eg⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := Y.functionField) (ht.map e)
    (Units.map e.toMonoidHom u) m
  rw [← eg, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have eg' : ((fnPull s g : Y.functionFieldˣ) : Y.functionField) =
      algebraMap E'.ring Y.functionField (Units.map e.toMonoidHom u : E'.ringˣ) *
        algebraMap E'.ring Y.functionField (e t) ^ m := by
    change functionFieldMap s (g : X.functionField) = _
    rw [eg, map_mul, map_zpow₀]
    rfl
  rw [← eg', ordTop_vw_of_ne_zero _ (fnPull s g).ne_zero, WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderAtCodimOneEqOne
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

theorem ord_fnOf_eq_one_of_generates (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha : a ≠ 0) (haP : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  set P := (hU.primeIdealOf ⟨z, hz⟩).asIdeal with hP
  have halg : ∀ b : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk z) b = X.presheaf.germ U z hz b :=
    fun b => rfl
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk z) =
      Ideal.span {X.presheaf.germ U z hz a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk z)]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro g hgP
      obtain ⟨r, hr⟩ := hg g hgP
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      obtain ⟨u, hu⟩ := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) P t).2 ht
      refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk z) r * ↑u⁻¹, ?_⟩
      have e := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk z)) hr
      rw [map_mul, map_mul, ← hu] at e
      rw [← halg]
      calc algebraMap Γ(X, U) (X.presheaf.stalk z) g
          = ↑u⁻¹ * (↑u * algebraMap Γ(X, U) (X.presheaf.stalk z) g) := by simp
        _ = _ := by rw [e]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← halg]
      exact Ideal.mem_map_of_mem _ haP
  have hne : X.presheaf.germ U z hz a ≠ 0 := fun h0 =>
    ha (fnOf_injective U (gen_mem hz) (by rw [← algebraMap_germ hz, h0, map_zero, map_zero]))
  rw [← algebraMap_germ hz a, ord_algebraMap h1 hne, ← hmax]
  haveI := (isSimpleModule_iff_isCoatom.2
    (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk z)).out :
      IsSimpleModule _ (X.presheaf.stalk z ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk z)))
  simp [Module.length_eq_one]

end GlobalTheory.Cartier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderOffCodimOneEqZero
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

theorem GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  intro X _ _ U hU z hz a t hcz hdiv v hv ht hne
  by_cases ha : v ∈ X.basicOpen a
  · exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hv _ a).2 ha)
  refine Scheme.ord_eq_zero_of_coheight_neq_one (fun hcv => ?_) _
  have key : ∀ (w : X) (hw : w ∈ U) (f : Γ(X, U)),
      w ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
    intro w hw f
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hw⟩ : U)
    haveI := hU.isLocalization_stalk ⟨w, hw⟩
    rw [X.mem_basicOpen f w hw]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w) _ f
  have hle : (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
    intro g hg
    obtain ⟨r, hr⟩ := hdiv g hg
    have haP : a ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
      by_contra h
      exact ha ((key v hv a).2 h)
    have htP : t ∉ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := (key v hv t).1 ht
    have htg : t * g ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := hr ▸ Ideal.mul_mem_right _ _ haP
    exact ((hU.primeIdealOf ⟨v, hv⟩).isPrime.mem_or_mem htg).resolve_left htP
  have hsp : z ⤳ v := by
    have h1 := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h1
  have hvz : v ≤ z := hsp
  have hlt : v < z := lt_of_le_not_ge hvz (fun h => hne (hsp.antisymm h).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [hcz, hcv] at h2
  exact absurd h2 (by norm_num)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormalStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧ (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra; Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  first | exact @GlobalTheory.CoordsOrigin.noetherian_free_cotangent | exact GlobalTheory.CoordsOrigin.noetherian_free_cotangent | (intros; apply GlobalTheory.CoordsOrigin.noetherian_free_cotangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

theorem baseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  intro R k Ω _ _ _ _ _ _ _ V W f g h
  have hu : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h1 : pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left =
      pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ g.left := by
    have := congrArg (fun φ => φ.left ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) h
    simp only [Over.pullback_map_left, pullback.lift_fst] at this
    exact this
  set s := Spec.map (CommRingCat.ofHom (algebraMap R k)) with hs
  set t := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with ht
  rw [hu] at h1
  have f₁ : Flat t := by
    rw [ht, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  have f₂ : Surjective t :=
    ⟨fun y => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi (pullback.fst (pullback.snd V.hom s) t) := Flat.epi_of_flat_of_surjective _
  have key : pullback.fst V.hom s ≫ f.left = pullback.fst V.hom s ≫ g.left := by
    rw [← cancel_epi (pullback.fst (pullback.snd V.hom s) t)]
    have hc : (pullback.fst (pullback.snd V.hom s) t ≫ pullback.fst V.hom s) ≫ V.hom =
        pullback.snd (pullback.snd V.hom s) t ≫ t ≫ s := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
    have he := pullback.lift_fst _ _ hc
    rw [← Category.assoc, ← Category.assoc, ← he, Category.assoc, Category.assoc, h1]
  apply Over.OverMorphism.ext
  simp only [Over.pullback_map_left]
  apply pullback.hom_ext
  · erw [pullback.lift_fst, pullback.lift_fst]
    exact key
  · erw [pullback.lift_snd, pullback.lift_snd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  intro K _ T P P₀ f a h
  have h2 : SmoothOfRelativeDimension P.g P₀.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ P₀.smoothDim h2 (eSec P₀.A (default : PrimeSpectrum K))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_eq_one_of_geometric_points_torsion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  first | (exact @GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (exact GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (intros; apply GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points  <;> assumption)
end

