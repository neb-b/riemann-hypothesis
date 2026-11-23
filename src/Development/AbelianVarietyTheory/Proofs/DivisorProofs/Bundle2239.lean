module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CubeSymDescent

theorem of_push : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  intro S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ
  let φs : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left]
  let εs : Fin 2 → ℤ := ![1, -1]
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let A := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
    (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
    (LB.pullGen L.L φs εs s (b * d).left)
  have vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J *
        val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
      (LB.pullGen L.L φs εs s (b * d).left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left
    have m3 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left) V.left
    refine m1.trans ?_
    rw [m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]
    rfl
  let B := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
    (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
    (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left)
  have vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J *
        val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left) V.left
    have m3 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left
    have m4 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left) V.left
    refine m1.trans ?_
    rw [m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ,
      val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, MonObj.comp_mul]
    rfl
  have hcorr : LB.Gen.Corr L.L _ _ _ _ A B := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_
    let P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
      lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
    have hP : (cubeMapOf h).F3 = P.left := rfl
    have ha : P ≫ a = pushHom h (G3 G') (x3 G' 0) := by simp [P, a, x3]; rfl
    have hb : P ≫ b = pushHom h (G3 G') (x3 G' 1) := by simp [P, b, x3]; rfl
    have hd : P ≫ d = pushHom h (G3 G') (x3 G' 2) := by simp [P, d, x3]; rfl
    rw [hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]
    have e := hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)
    simp only [map_inv, map_mul] at e ⊢
    exact e
  have e := val_corr hJ hcorr (lift x (lift y u)).left
  have ha : lift x (lift y u) ≫ a = x := by simp [a, x3]
  have hb : lift x (lift y u) ≫ b = y := by simp [b, x3]
  have hd : lift x (lift y u) ≫ d = u := by simp [d, x3]
  rw [vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd] at e
  exact e

end GlobalTheory.CubeSymDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
namespace PushCub
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β)

theorem push_one {T : Over S'} : pushHom h T 1 = toUnit _ ≫ η[G] := by
  rw [map_one, Hom.one_def]

theorem face0 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 0 =
    lift (pushHom h (G2 G') 1) (lift (pushHom h (G2 G') (fst G' G')) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face1 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 1 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') 1) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face2 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 2 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') (snd G' G')) (pushHom h (G2 G') 1)) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem pushPt_lift_cubeTriplePoint_of_isGrpPullback (i : Fin 3) : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫ x3 G i =
    pushHom h (G3 G') (x3 G' i) := by
  fin_cases i <;> simp [x3] <;> rfl

theorem pushPt_lift_cubeQuadruplePoint_of_isGrpPullback (i : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ x4 G i = pushHom h (G4 G') (x4 G' i) := by
  fin_cases i <;> simp [x4] <;> rfl

theorem padd_push (i j : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ padd G (x4 G i) (x4 G j) = pushHom h (G4 G') (x4 G' i * x4 G' j) := by
  rw [map_mul, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h i, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h j]
  exact MonObj.comp_mul _ _ _

theorem cubeMapOf_thirdFace_eq_pushPt_lift : (cubeMapOf h).F3 =
    (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left := rfl

theorem sw01 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 1) (lift (x3 G 0) (x3 G 2)) =
    lift (pushHom h (G3 G') (x3 G' 1)) (lift (pushHom h (G3 G') (x3 G' 0)) (pushHom h (G3 G') (x3 G' 2))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem sw12 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 0) (lift (x3 G 2) (x3 G 1)) =
    lift (pushHom h (G3 G') (x3 G' 0)) (lift (pushHom h (G3 G') (x3 G' 2)) (pushHom h (G3 G') (x3 G' 1))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem coc1 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0 * x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc2 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (x4 G 1) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

theorem coc3 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1 * x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc4 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 1) (lift (x4 G 2) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

end PushCub
end GlobalTheory.Mum

namespace GlobalTheory.Mum

open PushCub in
theorem cubicalStr_of_push_val : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  intro S S' G G' _ _ _ _ f β h L t ht i2 c2 i3 c3 i4 c4 hup
  have hv : ∀ {T : Over S'} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (V : Over.mk (T.hom ≫ f) ⟶ G3 G)
      (a b d : T ⟶ G'), V = lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d)) →
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t V.left z J =
        GlobalTheory.CubTransport.thV t z J (pushHom h T a) (pushHom h T b) (pushHom h T d) := by
    rintro T z J V a b d rfl; rfl
  refine ⟨{ t := t, isGen := ht, face := fun i => ?_, cubeSymmetric_swap_first := ?_, cubeSymmetric_swap_last := ?_, cocycle := ?_ }, rfl⟩
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i2 c2 fun z J hJ => ?_
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [← Over.comp_left]
    have C := hup (G2 G') z J hJ
    fin_cases i
    · exact (hv _ 1 (fst G' G') (snd G' G') (face0 h)).trans (C.face _ _)
    · exact (hv _ (fst G' G') 1 (snd G' G') (face1 h)).trans (C.face₂ _ _)
    · exact (hv _ (fst G' G') (snd G' G') 1 (face2 h)).trans (C.face₃ _ _)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s01 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 1) (x3 G' 0) (x3 G' 2) (sw01 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s12 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 0) (x3 G' 2) (x3 G' 1) (sw12 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i4 c4 fun z J hJ => ?_
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).symm)
    simp only [← Over.comp_left]
    have C := hup (G4 G') z J hJ
    exact (congrArg₂ (· * ·) (hv _ _ _ _ (coc1 h)) (hv _ _ _ _ (coc2 h))).trans ((C.coc _ _ _ _).trans
      (congrArg₂ (· * ·) (hv _ _ _ _ (coc3 h)) (hv _ _ _ _ (coc4 h))).symm)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLatticeSlopeSqGoodCoverLeCore
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

noncomputable section

namespace GlobalTheory.CoreRing


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem slope_sq_latOver_sub_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  intro D T j Y e o a n S hT hj hY hDom hS hG hG₂
  obtain ⟨hLc, hNc⟩ := _root_.GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj
  obtain ⟨hLd, hGal, hPull⟩ := GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW
  letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra
  obtain ⟨π, hπP, hπli, hπN, hπlat, -, hπD⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle (T.U j)
    (coreDict T.toCore j) Y.d Y.U Y.dict hLc hLd hY.lev.1 hGal a n hDom hDom.2
  have hTC : IsTotallyComplex T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

  have hSc : ∀ f ∈ S, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) := fun f hf => by
    rw [cuspW_wtZ]; exact hS hf

  have hPf : ∀ f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), Y.Pull (f : T.R j) (π f : Rul Y.d.Xo₂ Y.d.c₂) := fun f =>
    (hPull a n _ (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (by rw [← cuspW_wtZ]; exact f.2)) _).2 (hπP f)

  have p0 : Y.Pull (0 : T.R j) (0 : Rul Y.d.Xo₂ Y.d.c₂) := by
    intro k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero]
  have pAdd : ∀ r₁ r₂ : Rul Y.d.Xo₂ Y.d.c₂, Y.Pull (0 : T.R j) r₁ → Y.Pull (0 : T.R j) r₂ →
      Y.Pull (0 : T.R j) (r₁ + r₂) := by
    intro r₁ r₂ hr₁ hr₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hr₂ k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_add] at e1 e2 ⊢
    rw [e1, e2, add_zero]
  have pSmul : ∀ (c : Y.d.c₂.F) (r : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull (0 : T.R j) r → Y.Pull (0 : T.R j) (c • r) := by
    intro c r hr k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_smul] at e1 ⊢
    rw [e1, mul_zero]
  have pSub : ∀ (f : T.R j) (g₁ g₂ : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull f g₁ → Y.Pull f g₂ → Y.Pull (0 : T.R j) (g₁ - g₂) := by
    intro f g₁ g₂ hg₁ hg₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hg₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hg₂ k hA hk y₂ y' y h1 h2 h3 h4
    have e3 : evR Y.d.Xo₂ Y.d.c₂ (g₁ - g₂) y₂ = evR Y.d.Xo₂ Y.d.c₂ g₁ y₂ - evR Y.d.Xo₂ Y.d.c₂ g₂ y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) g₁ g₂
    rw [e3, e1, e2, sub_self]
    simp only [evR, evalAt_zero]
  have pSmul2 : ∀ (c : Y.d.c₂.F) (h : Rul Y.d.Xo₂ Y.d.c₂) (x : Y.V (wtZ a n)),
      Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) →
        Y.Pull (0 : T.R j) (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro c h x hp k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hp k hA hk y₂ y' y h1 h2 h3 h4
    have es1 : evR Y.d.Xo₂ Y.d.c₂ (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ h y₂ - evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) h (x : Rul Y.d.Xo₂ Y.d.c₂)
    have es2 : evR Y.d.Xo₂ Y.d.c₂ (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ - evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) _ _
    have es3 : evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ = algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ h y₂ := by
      simp only [evR, evalAt_smul]
    have es4 : evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ =
        algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      (map_smul ((evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂).comp (Y.V (wtZ a n)).subtype) c x).trans (Algebra.smul_def c _)
    rw [es2, es3, es4, ← mul_sub, ← es1, e1]
    simp only [evR, evalAt_zero, mul_zero]
  set C : Submodule T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) :=
    (Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype with hC
  have hCspan : C = Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S) := by
    rw [hC, ← Submodule.comap_map_eq_of_injective (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).injective_subtype
      (Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S)), Submodule.map_span,
      Set.image_preimage_eq_of_subset]
    intro f hf
    exact ⟨⟨f, hSc f hf⟩, rfl⟩
  have hCQ : ∀ x ∈ C, π x ∈
      (Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g}).comap (Y.V (wtZ a n)).subtype := by
    rw [hCspan]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨(y : T.R j), hy, hPf y⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [π.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  have key : ∀ h ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g},
      ∃ x : Y.V (wtZ a n), x ∈ Submodule.span Y.d.c₂.F (π '' (C : Set (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)))) ∧
        Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨f, hfS, hpf⟩ := hh
      refine ⟨π ⟨f, hSc f hfS⟩, Submodule.subset_span ⟨⟨f, hSc f hfS⟩, Submodule.subset_span hfS, rfl⟩, ?_⟩
      exact pSub f _ _ hpf (hPf _)
    | zero => exact ⟨0, zero_mem _, by simpa using p0⟩
    | add h₁ h₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, hx₁, p₁⟩ := ih₁
      obtain ⟨x₂, hx₂, p₂⟩ := ih₂
      refine ⟨x₁ + x₂, add_mem hx₁ hx₂, ?_⟩
      have : h₁ + h₂ - ((x₁ + x₂ : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) =
          (h₁ - (x₁ : Rul Y.d.Xo₂ Y.d.c₂)) + (h₂ - (x₂ : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [Submodule.coe_add]; abel
      rw [this]
      exact pAdd _ _ p₁ p₂
    | smul c h _ ih =>
      obtain ⟨x, hx, p⟩ := ih
      exact ⟨c • x, Submodule.smul_mem _ _ hx, pSmul2 c h x p⟩
  have hu := _root_.GlobalTheory.CoverPull.cusp_pullback_existsUnique D T j Y e o hT hj hY hY.unit hY.modelW a n hDom 0 (zero_mem _)
  have hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 Y.d.c₂.F), ∀ g ∈ Y.latOver (wtZ a n) S,
      δ • g ∈ Submodule.span (𝓞 Y.d.c₂.F) (π '' ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
        Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _)) := by
    intro δ hδ g hg
    have hgl := (Submodule.mem_inf.1 hg).1
    have hgP := (Submodule.mem_inf.1 hg).2
    obtain ⟨x, hx, px⟩ := key _ hgP
    have hgx : ((g : Rul Y.d.Xo₂ Y.d.c₂) - (x : Rul Y.d.Xo₂ Y.d.c₂)) = 0 :=
      hu.unique ⟨sub_mem g.2 x.2, px⟩ ⟨zero_mem _, p0⟩
    have hgx' : g = x := Subtype.ext (sub_eq_zero.1 hgx)
    have h1 := hπD C δ hδ g hgl (hgx' ▸ hx)
    have hset : {f | f ∈ C ∧ f ∈ GlobalTheory.AllWt.latW (T.U j) (wtZ a n)} =
        ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
          Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact And.comm
    rw [hset] at h1
    exact h1
  refine GlobalTheory.SlopeDifferent.slope_sq_sub_le_of_different_smul (K := T.Q.c.F) (K' := Y.d.c₂.F) _ _ π _ _ hG.1 hG₂.1
    ?_ hπli ?_ ?_ ?_ hDiff
  · intro σ f
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  · have hle : Y.latOver (wtZ a n) S ≤ GlobalTheory.AllWt.latW Y.U (wtZ a n) := inf_le_left
    haveI := isNoetherian_of_fg_of_noetherian _ hG₂.2.1
    have h1 := (IsNoetherian.noetherian ((Y.latOver (wtZ a n) S).comap (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype)).map
      (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1
  · intro σ' x
    exact (hπN σ' x).trans (hNc _ _ x)
  · intro x hx
    obtain ⟨hxl, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨(hπlat x).2 hxl, ?_⟩
    exact hCQ x hxC

end GlobalTheory.CoreRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    _root_.GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := _root_.GlobalTheory.liftSemi_pullTot1_bijective R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := _root_.GlobalTheory.TotTwoBaseChange.main R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationPreData_laws_of_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  first | exact @GlobalTheory.UTau0.rlaws_transfer | exact GlobalTheory.UTau0.rlaws_transfer | (intros; apply GlobalTheory.UTau0.rlaws_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepFixesIntegralUnipotentInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_integralUnipotent_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.NabFix.nab_fix | exact GlobalTheory.NabFix.nab_fix | (intros; apply GlobalTheory.NabFix.nab_fix <;> assumption)
end

