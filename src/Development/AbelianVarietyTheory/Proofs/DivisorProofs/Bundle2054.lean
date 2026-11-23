module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (y : Sp B) :
    gm (spMap f) y ⊤ (unitOn u) = gm (𝟙 (Sp B)) y ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact congrArg ((Sp B).presheaf.germ ⊤ y trivial).hom nat.symm

theorem evenDefect_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  intro R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc _ hψ h hE χ z J₂ hJ₂
  beta_reduce
  have hgam' : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hgam
  have cx : ∀ a, D₂.xK a ≫ β = spMap gam ≫ D₁.xK (xe a) := fun a => by
    show (jK R₂ ≫ (D₂.c a).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam', Category.assoc]
  have cn : D₂.xK (-χ) = D₂.xK χ ≫ (ι[D₂.P.A]).left := by
    show (toUnit _ ≫ D₂.c (-χ)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  choose J₁ hJ₀ using fun φ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (φ z)
  have hJ₁ : Good D₁.P.L z J₁ := hJ₀
  have vψ : ∀ a, val (D₁.psi (xe a)) (spMap gam) z J₁ =
      (gw v (D₂.xK a) z (J₁ (D₂.xK a ≫ β)) (J₂ (D₂.xK a)))⁻¹ * val (D₂.psi a) (𝟙 _) z J₂ := fun a => by
    have := GlobalTheory.CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ₁ hJ₂
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have hcorr := corr_of_val D₁.P.isLB (t := LB.mulGen _ _ _ _ _ (D₁.psi (-(xe χ))) (LB.pullGen _ _ _ D₁.sym (D₁.xK (xe χ))))
    (t' := GlobalTheory.UU.scaleGen (unitOn (h (xe χ))) (D₁.psi (xe χ))) fun y J hJ => by
      rw [val_mul hJ, val_pull hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, Category.id_comp]
      exact hE (xe χ) y J hJ
  have e := val_corr hJ₁ hcorr (spMap gam)
  have hg : gm (spMap gam) z ⊤ (unitOn (h (xe χ))) =
      gm (𝟙 (TK R₂).left) z ⊤ (unitOn (Units.map gam.toMonoidHom (h (xe χ)))) := gm_spMap_unitOn gam _ z
  rw [val_mul hJ₁, val_pull hJ₁, GlobalTheory.UU.val_scaleGen _ _ _ hJ₁, hg, ← cx, ← map_neg xe χ, vψ, vψ] at e
  have hs := GlobalTheory.PsiRing.val_sym_comp GlobalTheory.globalFns_holds gp hv (D₂.xK χ) z hJ₁ hJ₂
  rw [← cn] at hs
  rw [hs] at e
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCover
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientLocal

theorem exists_quotient_of_openImmersion (S : Scheme.{0}) [IsLocallyNoetherian S] (R : CommRingCat.{0})
    (f : Spec R ⟶ S) [IsOpenImmersion f] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A)
    (hA : IsAbelianScheme A) (hi : IsMonHom i) (hm : Mono i) (hf : IsFinite H.hom) (hfl : Flat H.hom) :
    ∃ (B : Over (Spec R)) (_ : GrpObj B) (q : (Over.pullback f).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback f).obj H) ((Over.pullback f).obj A) ≫
          (Over.pullback f).map i) * snd ((Over.pullback f).obj H) ((Over.pullback f).obj A))
        (snd ((Over.pullback f).obj H) ((Over.pullback f).obj A)) q q := by
  have hN : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := R)).1 hN
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have hi' : IsMonHom ((Over.pullback f).map i) := inferInstance
  have hm' : Mono ((Over.pullback f).map i) := inferInstance
  have hf' : IsFinite ((Over.pullback f).obj H).hom := by
    show IsFinite (pullback.snd H.hom f)
    infer_instance
  have hfl' : Flat ((Over.pullback f).obj H).hom := by
    show Flat (pullback.snd H.hom f)
    infer_instance
  obtain ⟨B, hB, q, -, h1, h2, h3, h4, h5, -, h6⟩ :=
    GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme R ((Over.pullback f).obj A)
      ((Over.pullback f).obj H) ((Over.pullback f).map i) hA' hi' hm' hf' hfl'
  exact ⟨B, hB, q, h1, h2, h3, h4, h5, h6⟩

theorem exists_local_quotient : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  intro S _ A _ H _ i hA hi hm hf hfl j
  haveI : IsOpenImmersion (S.affineCover.f j) := S.affineCover.map_prop j
  exact @exists_quotient_of_openImmersion S _ _ (S.affineCover.f j) this A _ H _ i hA hi hm hf hfl

end GlobalTheory.AbQuotientLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
section
open CategoryTheory Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbBaseChangeSq

theorem exists_baseChange_and_sq : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp R₁)) (_ : GrpObj B) (pr : B.left ⟶ A.left) (pr' : (B ⊗ B).left ⟶ (A ⊗ A).left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsPullback pr B.hom A.hom (spMap (algebraMap R₀ R₁)) ∧ IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom (spMap (algebraMap R₀ R₁)) ∧ (μ[B]).left ≫ pr = pr' ≫ (μ[A]).left ∧ (fst B B).left ≫ pr = pr' ≫ (fst A A).left ∧ (snd B B).left ≫ pr = pr' ≫ (snd A A).left ∧ (CartesianMonoidalCategory.lift (𝟙 B) (1 : B ⟶ B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ A)).left ∧ (CartesianMonoidalCategory.lift (1 : B ⟶ B) (𝟙 B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (1 : A ⟶ A) (𝟙 A)).left := by
  intro R₀ R₁ _ _ _ A _ g hA hg
  let f : Sp R₁ ⟶ Sp R₀ := spMap (algebraMap R₀ R₁)
  let F := Over.pullback f
  let B : Over (Sp R₁) := F.obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A B _ g hB hA hg
  have mapL : ∀ {X Y : Over (Sp R₀)} (a : X ⟶ Y),
      (F.map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  let m := Functor.LaxMonoidal.μ F A A
  refine ⟨B, inferInstance, pullback.fst A.hom f, m.left ≫ pullback.fst (A ⊗ A).hom f, hAB, hgB, hB.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : IsIso m := inferInstanceAs (IsIso (Functor.Monoidal.μIso F A A).hom)
    haveI : IsIso m.left := (Over.forget _).map_isIso m
    have h1 : IsPullback m.left (B ⊗ B).hom (F.obj (A ⊗ A)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w m⟩
    have h2 := h1.paste_horiz (IsPullback.of_hasPullback (A ⊗ A).hom f)
    rwa [Category.id_comp] at h2
  · have e : μ[B] = m ≫ F.map μ[A] := Functor.obj.μ_def (F := F) A
    rw [e, Over.comp_left, Category.assoc, mapL, Category.assoc]
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · have e : lift (𝟙 B) (1 : B ⟶ B) ≫ m = F.map (lift (𝟙 A) (1 : A ⟶ A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]
  · have e : lift (1 : B ⟶ B) (𝟙 B) ≫ m = F.map (lift (1 : A ⟶ A) (𝟙 A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]

end GlobalTheory.AbBaseChangeSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Adapt

set_option maxHeartbeats 1000000 in
theorem main : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  intro V _ _ _ _ hV D A G _ _ hS U C _ _ _ _ _ _ hC N ν hν
  haveI := hV
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := GlobalTheory.TorusModel.exists_isGt hG (GlobalTheory.TorusModel.splitExt D.toPre)
  obtain ⟨Φ, hp, ha⟩ := GlobalTheory.TorusModel.exists_points hG hH
  have hΦ : GlobalTheory.TorusModel.Represents Φ := ⟨hp, ha⟩
  obtain ⟨vB, hvB⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.toPre.P.A D.toPre.P.smoothDim
  let r := Module.finrank ℤ N.X
  let bX : Module.Basis (Fin r) ℤ N.X := Module.finBasis ℤ N.X
  let bD : Module.Basis (Fin r) ℤ D.toPre.X := bX.map ν.eX.toIntLinearEquiv
  choose lf hlf using fun i => (GlobalTheory.MBLow.GtVec.main V D.toPre).1 (vB i) (hvB.1 i)
  choose tv htv using fun l : Fin r => _root_.GlobalTheory.MBLow.TorVec.exists_torus_tangent V D.toPre ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom)
  have hco : ∀ (l : Fin r) (χ : D.toPre.X), ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom) χ = ((bD.repr χ l : ℤ) : V) :=
    fun l χ => by simp [Module.Basis.coord_apply]
  let gm₀ : Fin D.toPre.P.g ⊕ Fin r → GtPt D.toPre (epsR V) := Sum.elim lf tv
  have hgt : ∀ j, GtTan (gm₀ j) := fun j => by
    cases j with
    | inl i => exact (hlf i).1
    | inr l => exact (htv l).1
  let x : Fin D.toPre.P.g ⊕ Fin r → (epsR V ⟶ H) := fun j => (Φ _).symm (gm₀ j)
  have hx : ∀ j, Φ _ (x j) = gm₀ j := fun j => Equiv.apply_symm_apply _ _
  have hxB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := fun n σ =>
    _root_.GlobalTheory.GtBasis.main V D.toPre H Φ hΦ r vB bD x hvB (fun j => by rw [hx]; exact hgt j) (fun i => by rw [hx]; exact (hlf i).2)
      (fun l => by
        rw [hx]
        refine ⟨(htv l).2.1, fun χ Z q z J hJ => ?_⟩
        rw [← hco]
        exact (htv l).2.2 χ Z q z J hJ) n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GlobalTheory.MBLow.GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  let red : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) GlobalTheory.MBLow.GtVec.red_comp
  have tanG : ∀ w : epsR V ⟶ H, GtTan (Φ _ w) ↔ red ≫ w = 1 := fun w =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((GlobalTheory.TorusModel.isPull_unique (hp _ _ red w) h).trans
      (GlobalTheory.MBLow.GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ red w⟩⟩
  have tanH : ∀ w : epsR V ⟶ H, IsTangent w ↔ red ≫ w = 1 := fun w => by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      refine h.trans ?_
      show _ = (toUnit _ ≫ η[H]).left
      simp
    · intro h
      have := congrArg (·.left) h
      refine this.trans ?_
      show (toUnit _ ≫ η[H]).left = _
      simp
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have : Module.Flat V (DualNumber V) := inferInstanceAs (Module.Flat V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (IsLocalRing.maximalIdeal V) (epsR V) :=
    GlobalTheory.TorusModel.isAdicColimit_of_finite_flat (IsLocalRing.maximalIdeal V) (RingHom.id V) (by rwa [Ideal.map_id])
      (fun a ha => ⟨1, by rw [Ideal.map_id, pow_one]; exact ha⟩) (DualNumber V)
  let Rel : (epsR V ⟶ G) → (epsR V ⟶ H) → Prop := fun y w => TanRel U.toUnifPre y (Φ _ w)
  have h1 : Rel 1 1 := (tanRel_iff_isPointOf U.toUnifPre 1 (Φ _ 1)).2 (GlobalTheory.FormalPoint.isPointOf_one U.toUnifPre (hz _))
  have hmul : ∀ y y' w w', Rel y w → Rel y' w' → Rel (y * y') (w * w') := fun y y' w w' h h' =>
    GlobalTheory.MBLow.TanAdd.tanRel_mul U.toUnifPre y y' _ _ _ h h' (ha _ w w')
  have hsc : ∀ (c : V) (y : epsR V ⟶ G) (w : epsR V ⟶ H) (y' : epsR V ⟶ G) (w' : epsR V ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → w'.left = spMap (epsScaleR c) ≫ w.left → Rel y w → Rel y' w' := by
    intro c y w y' w' e e' h
    obtain rfl : y' = GlobalTheory.SecJet.epsScale V c ≫ y := Over.OverMorphism.ext e
    obtain rfl : w' = GlobalTheory.SecJet.epsScale V c ≫ w := Over.OverMorphism.ext e'
    exact GlobalTheory.MBLow.TanAdd.tanRel_scale U.toUnifPre c y _ _ h (hp _ _ _ w)
  have hex : ∀ y, IsTangent y → ∃ w, IsTangent w ∧ Rel y w := fun y hy => by
    obtain ⟨gm, h₁, h₂, -⟩ := GlobalTheory.MBLow.TanLift.exists_tan U.toUnifPre y hy
    refine ⟨(Φ _).symm gm, (tanH _).2 ((tanG _).1 (by rw [Equiv.apply_symm_apply]; exact h₂)), ?_⟩
    show TanRel _ _ _
    rw [Equiv.apply_symm_apply]; exact h₁
  have huy : ∀ y y' w, IsTangent y → IsTangent y' → Rel y w → Rel y' w → y = y' := fun y y' w _ _ h h' =>
    ((tanRel_iff_isPointOf _ _ _).1 h).unique ((tanRel_iff_isPointOf _ _ _).1 h')
  have hux : ∀ y w w', Rel y w → Rel y w' → w = w' := fun y w w' h h' =>
    (GlobalTheory.TorusModel.existsUnique_lift U.toUnifPre hΦ hT y).unique ((tanRel_iff_isPointOf _ _ _).1 h)
      ((tanRel_iff_isPointOf _ _ _).1 h')
  choose yy hyy using fun j => (existsUnique_tangent_of_gtTan V hV D A G hS U (gm₀ j) (hgt j)).exists
  have hyB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => yy (σ k)) := fun n σ =>
    _root_.GlobalTheory.LieTransfer.isLieBasis_of_rel V G H Rel h1 hmul hsc hex huy hux n _ _ (hxB n σ) fun k => ⟨(hyy _).1, by
      show TanRel _ _ _
      rw [hx]; exact (hyy _).2⟩
  have hdim : D.toPre.P.g + r = A.g := _root_.GlobalTheory.LieRankUnif.card_eq_g V D A G U.toUnifPre _ _ (hyB _ finSumFinEquiv.symm)
  let σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  choose gmC hgmC using fun j => _root_.GlobalTheory.MBLow.TanPull.main V D.toPre C N ν (gm₀ j) (hgt j)
  refine ⟨vB, r, bX, σ, fun k => yy (σ k), fun k => gm₀ (σ k), fun k => gmC (σ k), hyB _ σ,
    ⟨hvB, fun j => (hgmC _).2.1, fun i => ?_, fun l => ?_⟩, fun k => ⟨(hyy _).2, hgt _, (hgmC _).1⟩⟩
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inl i), (hgmC _).1.1]
    show _ ≫ (lf i).b.left = _
    rw [(hlf i).2]
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inr l)]
    refine ⟨(hgmC _).2.2.1 (htv l).2.1, fun χ => ?_⟩
    refine ((hgmC _).2.2.2 (((bD.repr (ν.eX χ) l : ℤ) : V)) (ν.eX χ) fun Z q z J hJ => ?_).trans ?_
    · have hv := (htv l).2.2 (ν.eX χ) Z q z J hJ
      rw [hco] at hv
      exact hv
    · have e : bD.repr (ν.eX χ) l = bX.repr χ l := by
        show (bX.map ν.eX.toIntLinearEquiv).repr (ν.eX χ) l = _
        rw [Module.Basis.map_repr]
        simp
      rw [e, map_intCast]

end GlobalTheory.MBLow.Adapt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmooth
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.Pinch

theorem appTop_ι_comp_eq {C Z : Scheme.{0}} (e : C ⟶ Z) (U : C.Opens) :
    (U.ι ≫ e).appTop = e.appLE ⊤ U le_top ≫ U.topIso.inv := by
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso, Scheme.Hom.comp_appTop, Scheme.Opens.ι_app]
  simp [← Functor.map_comp]

theorem exists_affine_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z),
    SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧
      ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  intro g C Z _ e he x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) e he
    ⟨⊤, isAffineOpen_top Z⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨t, ht⟩, hxt⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen t
  have h1 := h' t ht Γ(C, C.basicOpen t)
  refine ⟨C.basicOpen t, hW.basicOpen t, hxt, fun r => ?_⟩
  have hl2 := (hW.basicOpen t).isLocalization_basicOpen r
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).right
    Γ(C, C.basicOpen r) r _ h1
  have h3 : (e.appLE ⊤ (C.basicOpen r) le_top).hom.IsStandardSmoothOfRelativeDimension g := by
    convert h2 using 1
    ext a
    change _ = (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) ((C.presheaf.map (homOfLE (C.basicOpen_le t)).op) _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map]
  rw [appTop_ι_comp_eq, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (C.basicOpen r).topIso.symm.commRingCatIsoToRingEquiv h3

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbAffineUnit

theorem exists_affine_nonzeroLocus_unit : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  intro R _ _ _ G _ hG _
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hR : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R G.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
  set y₀ : G.left := (η[G]).left (closedPoint R) with hy₀
  have hy : G.hom y₀ = closedPoint R := by
    have h2 := Scheme.Hom.comp_apply (η[G]).left G.hom (closedPoint R : (𝟙_ (Over (Sp R))).left)
    rw [he] at h2
    exact h2.symm
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y₀) trivial
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.SS.exists_nonzeroLocus_eq_of_isAffineOpen G.left hst W hW ⟨_, hyW⟩
  exact ⟨L, s, hL, hs ▸ hW, y₀, hs ▸ hyW, hy⟩

end GlobalTheory.SemiAbAffineUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_affine_basicOpen_nbhd : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i →
    IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O →
    ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  intro B' C Y i q hi hq hB y O hO hyO
  have hF : (q ⁻¹' {q y}).Finite := q.finite_preimage_singleton (q y)
  classical
  obtain ⟨V₀, hV₀, hFV₀⟩ := hB ((hF.image i).toFinset)
  have hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀) := hV₀.preimage i
  obtain ⟨h, hFh, hhO⟩ := GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF
    (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx; simp [hx, hyO])
  have hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ) :=
    q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl
  have hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hFh (by simpa using hxy))
  let W : C.Opens := ⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩
  obtain ⟨r, hrW, hyr⟩ := hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO
  have hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h := by
    intro x hx
    by_contra hxh
    exact hrW hx ⟨x, hxh, rfl⟩
  have hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r) := Scheme.preimage_basicOpen q r
  obtain ⟨f', hf'⟩ := hY₀.basicOpen_basicOpen_is_basicOpen h
    (Y.presheaf.map (homOfLE hhO).op (q.app O r))
  rw [Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle] at hf'
  obtain ⟨t, ht⟩ := i.app_surjective V₀ hV₀ f'
  refine ⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩
  · have : y ∈ i ⁻¹ᵁ B'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, hf']; exact hyr
    exact this
  · rw [Scheme.preimage_basicOpen, ht, hf']

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem exists_isPull : ∀ (Z V : Scheme.{0}) [IsIntegral Z] [IsIntegral V] (q : Z ⟶ V) [IsDominant q]
    (E : CartierDiv V), ∃ D : CartierDiv Z, IsPull q D E := by
  intro Z V _ _ q _ E
  obtain ⟨D, -, hD⟩ := GlobalTheory.Cartier.exists_pullback_cartierDiv V Z q E
  exact ⟨D, fun y b hb x hx => hD x b (hx ▸ hb)⟩

end GlobalTheory.FlagPush
end

