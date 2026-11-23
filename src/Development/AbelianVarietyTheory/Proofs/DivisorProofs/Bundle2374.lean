module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescHom

theorem ext_of_open {T : Scheme.{0}} {W X Y : Over T} (j : W ⟶ X) [IsOpenImmersion j.left] [Surjective W.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y} (h : j ≫ f = j ≫ g) : f = g := by
  have hfib : ∀ x : X.left, x ∈ closure ((j.left.opensRange : Set X.left) ∩ X.hom ⁻¹' {X.hom x}) := by
    intro x
    have hirr : IsIrreducible (X.hom ⁻¹' {X.hom x}) :=
      X.hom.isIrreducible_preimage X.hom.isOpenMap isIrreducible_singleton
    obtain ⟨w, hw⟩ := W.hom.surjective (X.hom x)
    have hne : (X.hom ⁻¹' {X.hom x} ∩ (j.left.opensRange : Set X.left)).Nonempty := by
      refine ⟨j.left w, ?_, ⟨w, rfl⟩⟩
      show X.hom (j.left w) = X.hom x
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hw
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible
      j.left.opensRange.isOpen hne (show x ∈ X.hom ⁻¹' {X.hom x} from rfl)
    rwa [Set.inter_comm] at hsub
  have hl : j.left ≫ f.left = j.left ≫ g.left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  refine GlobalTheory.FibreDense.main X.left T Y.left X.hom Y.hom j.left.opensRange hfib f.left g.left
    (by rw [Over.w f, Over.w g]) ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hl]

theorem isMonHom_of_open {T : Scheme.{0}} {W X Y : Over T} [GrpObj X] [GrpObj Y] (j : W ⟶ X) [IsOpenImmersion j.left]
    [Surjective W.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] (φ : X ⟶ Y)
    (h : ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ)) : IsMonHom φ := by
  have hmuX : (μ : X ⊗ X ⟶ X) = fst X X * snd X X := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hmuY : (μ : Y ⊗ Y ⟶ Y) = fst Y Y * snd Y Y := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hoi : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (by simp) (by simp)
  have hsurj : Surjective (W ⊗ W).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hsm : Smooth (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hgi : GeometricallyIrreducible (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp _ _
  have hmul : μ ≫ φ = (φ ⊗ₘ φ) ≫ μ := by
    apply ext_of_open (j ⊗ₘ j)
    have lhs : (j ⊗ₘ j) ≫ μ ≫ φ = ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ := by
      rw [hmuX, ← Category.assoc, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    have rhs : (j ⊗ₘ j) ≫ (φ ⊗ₘ φ) ≫ μ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ) := by
      rw [hmuY, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc]
    rw [lhs, rhs, h]
  have hcomp : ∀ {Z : Over T} (a b : Z ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ) := by
    intro Z a b
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
  have hone : η ≫ φ = η := by
    have h1 : ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) * ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) = (1 : 𝟙_ (Over T) ⟶ X) ≫ φ := by
      rw [← hcomp, _root_.mul_one]
    have h2 : (1 : 𝟙_ (Over T) ⟶ X) ≫ φ = 1 := _root_.mul_eq_left.mp h1
    have e1 : ∀ {M : Over T} [MonObj M], (1 : 𝟙_ (Over T) ⟶ M) = η := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← e1, ← e1]
    exact h2
  exact ⟨hone, hmul⟩

theorem geometricallyIrreducible_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) :
    GeometricallyIrreducible G.hom := by
  obtain ⟨_, hsm, _, _, hgc, _⟩ := hG
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S G
  infer_instance

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem surjective_near [GrpObj G] [Surjective π] (N : Near π G) : Surjective N.U.hom := by
  have := N.smooth
  have hcl : closedPoint R ∈ Set.range N.U.hom := by
    obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
    have he : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w η[G]
    have hGs : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
      rw [← Scheme.Hom.comp_apply, he]; rfl
    obtain ⟨y, hy⟩ := N.all _ (by rw [hGs, hs])
    refine ⟨pullback.fst N.U.hom π y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over,
      Scheme.Hom.comp_apply, hy, hGs, hs]
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (specializes_closedPoint x) hcl⟩

theorem isPullback_embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
  have hA : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π))
      (pullback.snd N.U.hom π) p := by
    have outer : IsPullback (Desc.toS N p hp ≫ pullback.fst N.U.hom π)
        (pullback.snd N.U.hom (pullback.fst π π ≫ π)) N.U.hom (p ≫ π) := by
      rw [Desc.toS, pullback.lift_fst, hp]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right outer (by rw [Desc.toS, pullback.lift_snd]) (IsPullback.of_hasPullback _ _)
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback G.hom p)
  · rw [Desc.embL, pullback.lift_snd, N.u_over]
    exact hA
  · rw [Desc.embL, pullback.lift_fst]

theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp) N.isOpen

theorem isMonHom_of_sum_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  intro R _ _ _ _ S π _ _ _ G' _ _ hG N p p' hp hp' φ hsum hemb
  have : Surjective N.U.hom := surjective_near N
  have : GeometricallyIrreducible G'.hom := geometricallyIrreducible_of_semiAbelian G' hG
  obtain ⟨_, hsm, hsep, _, _, _⟩ := hG
  have : IsOpenImmersion (Desc.emb N p hp).left := isOpenImmersion_emb N p hp
  have : Surjective (Desc.UT N).hom := by
    show Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
  have : Smooth ((Over.pullback p).obj G').hom := by
    show Smooth (pullback.snd G'.hom p); infer_instance
  have : GeometricallyIrreducible ((Over.pullback p).obj G').hom := by
    show GeometricallyIrreducible (pullback.snd G'.hom p); infer_instance
  have : IsSeparated ((Over.pullback p').obj G').hom := by
    show IsSeparated (pullback.snd G'.hom p'); infer_instance
  refine isMonHom_of_open (Desc.emb N p hp) φ ?_
  change Desc.sum N p hp ≫ φ = _
  rw [hsum, Desc.sum, ← hemb]

end GlobalTheory.Mum.DescHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section

namespace GlobalTheory.Mum.EndThick

theorem commGroup_torusCoordinate_mul_identity {U : Type} [CommGroup U] {vxy wXY ux uy vX vY wx wy c₁ c₂ uxy : U}
    (m₁ : wXY * c₁ = vX * vY) (m₂ : vxy * c₂ = wx * wy) (r : uxy * c₁ = c₂ * (ux * uy))
    (ex : vX = wx * ux) (ey : vY = wy * uy) : vxy * uxy = wXY := by
  rw [eq_mul_inv_of_mul_eq m₁, eq_mul_inv_of_mul_eq m₂, eq_mul_inv_of_mul_eq r, ex, ey]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare in
theorem isMonHom_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → IsMonHom F := by
  intro R _ _ I D e G _ _ g a a' _ _ h' hc u hu h₀ F hF
  obtain ⟨hF₁, hF₂⟩ := hF
  have hG := GlobalTheory.globalFns_holds
  have him : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G),
      im g (x ≫ F) = im g x ≫ a := fun x =>
    Over.OverMorphism.ext ((Category.assoc x.left F.left _).trans
      ((congrArg (x.left ≫ ·) hF₁).trans (Category.assoc _ _ _).symm))
  have hU : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) (χ : D.X)
      (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) x.left z J =
        val₂ u z J (cPt T χ) (im g x) :=
    fun x χ z J hJ => val_pull_lift u χ g.pG ((Over.map (thick R I e)).map x) hJ
  have mul : ∀ (T) (x y : T ⟶ thickObj R I e G), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro T x y
    refine Over.OverMorphism.ext (ext_of_val g _ _ ?_ fun χ z J hJ => ?_)
    · have : im g ((x * y) ≫ F) = im g ((x ≫ F) * (y ≫ F)) := by
        rw [him, im_mul, im_mul, him, him, MonObj.mul_comp]
      exact congrArg (·.left) this
    · have e₁ := hF₂ χ _ (x * y).left z J hJ
      have ex := hF₂ χ _ x.left z J hJ
      have ey := hF₂ χ _ y.left z J hJ
      have m₁ := val_t_mul_points g hG χ (x ≫ F) (y ≫ F) z J hJ
      have m₂ := val_t_mul_points g hG (h' χ) x y z J hJ
      have r := (ros_add D.cub hG D.P.isAb a' a u hu h₀ hJ (im g x) (im g y) (cPt T χ)).2
      have c₁ : cubeVal g χ z J (x ≫ F) (y ≫ F) = cubV D.cub z J (cPt T χ) (im g x ≫ a) (im g y ≫ a) := by
        unfold cubeVal
        rw [him, him]
      have c₂ : cubeVal g (h' χ) z J x y = cubV D.cub z J (cPt T χ ≫ a') (im g x) (im g y) := by
        unfold cubeVal
        congr 1
        show toUnit _ ≫ D.c (h' χ) = (toUnit _ ≫ D.c χ) ≫ a'
        rw [hc, Category.assoc]
      rw [c₁] at m₁
      rw [c₂] at m₂
      rw [hU _ χ z J hJ, im_mul] at e₁
      rw [hU _ χ z J hJ] at ex ey
      refine e₁.trans (commGroup_torusCoordinate_mul_identity m₁ m₂ r ex ey)
  refine ⟨?_, ?_⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ _ ⟶ thickObj R I e G) ≫ F = 1 := mul_eq_left.1 h.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h'
  · have h := mul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.OpenImmersionDescent

theorem openImm_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine Y] [X.IsQuasiAffine] (g : X ⟶ Y) [IsIso g.appTop] :
    IsOpenImmersion g := by
  have e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [e]; infer_instance

theorem bij_congr {X Y : Scheme.{0}} (f : X ⟶ Y) (V W : Y.Opens) (h : V = W) (hb : Function.Bijective (f.app W)) :
    Function.Bijective (f.app V) := by subst h; exact hb

end GlobalTheory.Desc.OpenImmersionDescent


open GlobalTheory.Desc.OpenImmersionDescent in
theorem GlobalTheory.Desc.openIn_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc
  refine ⟨hm, ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_
  obtain ⟨k, hk, b, hb, hz⟩ := hP.cover (pullback.fst p (spMap ρ) z)
  refine ⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩
  haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)
  have hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (hP.affine k hk b hb).preimage _
  haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA
  have hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b) := by
    ext y
    change pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hloc k hk b hb y
  haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine :=
    _root_.GlobalTheory.Desc.LocusQA.isQuasiAffine_locus Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre
  haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _)
      ⟨_root_.GlobalTheory.Desc.BaseInj.app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb,
       _root_.GlobalTheory.Desc.lift_app_surjective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb⟩
    have h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 h1
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact openImm_of_isIso_appTop _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalOfSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.PrincSubring

theorem isPrincipal_of_subring : ∀ (h : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsSymmetricPair h A₁ P₁ → Out.RelAmple A₁ (diagPull A₁ P₁) → IsGrpPullback A A₁ (spMap R₁.subtype) φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsPrincipal A P → IsPrincipal A₁ P₁ := by
  intro h R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hS hamp hpb hsq hiso hpr
  haveI : IsAbelianScheme A₁ := hS.1
  haveI : IsCommMonObj A₁ := IsAbelianScheme.comm
  obtain ⟨hG, hL, hLa, hrig, hsym⟩ := _root_.GlobalTheory.EighthPowerBundle.powLB_props h A₁ P₁ hS hamp
  have hf : KerAlong A₁ P₁ (spMap R₁.subtype) := _root_.GlobalTheory.PrincSubring.kerAlong_of_pull _ A P A₁ P₁ φ φ₂ hS.2.2.1 hpb hsq hiso hpr.2
  have hfT := (_root_.GlobalTheory.PrincSubring.kerAlong_iff_trivAlong h A₁ P₁ hS hamp _).1 hf
  have hK : Out.KTriv (Out.powObj A₁ 8) (powLB A₁ P₁) := by
    refine GlobalTheory.KTrivSpread.kTriv_of_primes GlobalTheory.abelianSchemeLaws_all.1.globalFns R₁ _ hG _ hL hLa fun p => ?_
    rcases _root_.GlobalTheory.PrimeReach.prime_contraction_or_dvr R R₁ p with hp | ⟨Q, k, _, i, j, V, _, _, _, ρ, e, h1, h2, hp⟩
    · exact ⟨R, inferInstance, R₁.subtype, hp, hfT⟩
    · refine ⟨V, inferInstance, ρ, hp, ?_⟩
      refine _root_.GlobalTheory.KTrivDvrSpread.trivAlong_of_generic _ _ hG hL hLa hrig hsym V (spMap ρ) ?_
      have t1 := hfT.comp (spMap (algebraMap R Q.asIdeal.ResidueField))
      have e1 : spMap (algebraMap R Q.asIdeal.ResidueField) ≫ spMap R₁.subtype = spMap j ≫ spMap i := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h1]
      rw [e1] at t1
      have t2 := (_root_.GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective _ _ (spMap i) (spMap j) hL t1).comp (spMap e)
      have e2 : spMap e ≫ spMap i = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h2]
      rwa [e2] at t2
  have hT : GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A₁ 8) (powLB A₁ P₁) (𝟙 _) :=
    fun T a ha x hx => GlobalTheory.UU.kTriv_iff_forall.1 hK T x hx
  exact ⟨hamp, fun T x hx => (_root_.GlobalTheory.PrincSubring.kerAlong_iff_trivAlong h A₁ P₁ hS hamp (𝟙 _)).2 hT T T.hom (Category.comp_id _) x hx⟩

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isPullback_of_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  intro X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr
  let ψ' : ∀ j, P j ⟶ pullback g π := fun j =>
    pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)
  have hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j := fun j => pullback.lift_fst _ _ _
  have hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j := fun j => pullback.lift_snd _ _ _
  have sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j) := fun j =>
    (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j)
      (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip
  haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)
  have hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcov (pullback.fst g π z)
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm
    exact ⟨j, t, ht⟩
  let c : X ⟶ pullback g π := pullback.lift β f w
  have hcf : c ≫ pullback.fst g π = β := pullback.lift_fst _ _ _
  have hce : ∀ j, e j ≫ c = ψ' j := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, hcf, hβ, hψ'f]
    · rw [Category.assoc, pullback.lift_snd, hf, hψ's]
  have loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j) := fun j => by
    haveI := he j
    refine (IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c
      (by rw [hce, Category.id_comp]) ?_).flip
    ext x
    change c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)
    constructor
    · rintro ⟨y, hy⟩
      apply hr j x
      refine ⟨p j y, ?_⟩
      rw [← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩
  have key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j)) := fun j => by
    rw [← (loc j).isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]
    exact MorphismProperty.isomorphisms.infer_property _
  have hiso : (MorphismProperty.isomorphisms Scheme) c :=
    IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j
  haveI : IsIso c := hiso
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformised
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPer

theorem isReg_fderiv_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  intro A _ g L u hA U b w
  have hs := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := (GlobalTheory.TorusTransfer.tangent_bijective u hs).2 w
  obtain ⟨d, -, hdv⟩ := GlobalTheory.KS.exists_locDer_of_isDiff A u w v hv hd
  exact ⟨d U b, fun z hz => (hdv U b z hz).symm⟩

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfect
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_adicCompletion_tensor_of_mvPolynomial :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ)
      (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K]
      [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K],
      (∀ a : Λ, algebraMap (Localization.AtPrime P) K
        (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  intro Λ _ _ _ _ n P _ K _ _ _ hinj
  let S₀ := MvPolynomial (Fin n) Λ
  let R := Localization.AtPrime P
  let B := AdicCompletion (maximalIdeal R) R
  haveI : IsRegularLocalRing R := inferInstance
  haveI : IsRegularLocalRing B := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_isRegularLocalRing B
  letI : Algebra S₀ K := ((algebraMap R K).comp (algebraMap S₀ R)).toAlgebra
  haveI : IsScalarTower S₀ R K := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType S₀ R := Algebra.EssFiniteType.of_isLocalization R P.primeCompl
  haveI : Algebra.EssFiniteType S₀ K := Algebra.EssFiniteType.comp S₀ R K
  have hC : ∀ a : Λ, algebraMap S₀ K (MvPolynomial.C a) = 0 → a = 0 := by
    intro a ha
    apply hinj a
    rw [IsScalarTower.algebraMap_apply Λ S₀ R a]
    exact ha
  have hD : ∀ s : Fin n, ∃ D : Derivation ℤ B B, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := fun s =>
    _root_.GlobalTheory.derivation_extend_completion_localization_atPrime S₀ P ((MvPolynomial.pderiv s).restrictScalars ℤ)
  have hD' : ∀ s : Fin n, ∃ D : @Derivation ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := by
    intro s
    obtain ⟨D, hD⟩ := hD s
    exact ⟨@Derivation.mk ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _ D.toLinearMap
      D.map_one_eq_zero' D.leibniz', hD⟩
  have h := _root_.GlobalTheory.regularFibre_of_liftedPartialDerivations Λ (Fin n) B K hC hD'
  let e : B ⊗[R] K ≃ₐ[R] B ⊗[S₀] K := IsLocalization.algebraTensorEquiv P.primeCompl R B K
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end GlobalTheory
end

