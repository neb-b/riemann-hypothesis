module

public import Mathlib
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.GtBaseChangeSharp
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.CubicalPullBaseChange
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self glue_unit)
open GlobalTheory.GtCubeCompare (gw PM maps_iff_pm)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubePullLawChecks

section General

variable {X Y : Scheme.{0}} {A B C : LB X}

end General

theorem rigPullIsGen : RigPullIsGenSt.{0} := by
  intro S S' G' G _ _ _ _ F e he L r _ hr
  exact Out.LBxP.isGen_pullAlong L F e (fun _ : PUnit => eSec G) (fun _ => 1)
    (fun _ => eSec G') (fun _ => he) r hr

end GlobalTheory.CubePullLawChecks

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldRestrictionTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}

def toT (g : GtPtF D F) : GtPt D (TF (R := R) F) := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩

theorem isZero_toT (g : GtPtF D F) : (toT g).IsZero ↔ g.IsZero := Iff.rfl

theorem maps_eq {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {g' : GtPtF D F}
    (H : GtPt.IsPullF F x g g') (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F g'.b χ k = x ≫ DegPre.gtφT D T g.b χ k := by
  have e := (GlobalTheory.TorusCoord.comp_eq_of_left g.b g'.b x (𝟙 _) (H.1.symm.trans (Category.id_comp _).symm)).1 χ k
  exact ((e.trans (Category.id_comp _)).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq g'.b χ) k).symm).symm

theorem isPullF_iff (σ : TF (R := R) F ⟶ T) (g : GtPt D T) (g' : GtPtF D F) :
    GtPt.IsPullF F σ.left g g' ↔ g'.b = σ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) σ.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
     fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
      ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)

theorem ext_valF {g g' : GtPtF D F} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (g'.s χ) (𝟙 _) y J) : g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (corr_of_val D.P.isLB (hs χ))
  rfl

theorem isPullF_unique {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {a a' : GtPtF D F}
    (H : GtPt.IsPullF F x g a) (H' : GtPt.IsPullF F x g a') : a = a' :=
  ext_valF (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (val_corr hJ (H.2 χ) (𝟙 _)).trans (val_corr hJ (H'.2 χ) (𝟙 _)).symm

theorem exists_isPullF (σ : TF (R := R) F ⟶ T) (ξ : GtPt D T) : ∃ g, GtPt.IsPullF F σ.left ξ g := by
  have e := GlobalTheory.TorusCoord.comp_eq_of_left ξ.b (σ ≫ ξ.b) σ.left (𝟙 _) (Category.id_comp _).symm
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (ξ.s χ) σ.left) (𝟙 _) y J = val (ξ.s χ) σ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g, hb, hv⟩ := exists_gt (σ ≫ ξ.b) (fun χ => LB.pullGen D.P.L _ _ (ξ.s χ) σ.left)
    (fun χ => DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _)
    (fun χ U _ f => Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e.1 χ k).trans ((Category.id_comp _).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq (σ ≫ ξ.b) χ) k).symm)))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ ξ.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ, ← GlobalTheory.TorusCoord.val_s_mul ξ σ.left χ χ' y J hJ, e.2 χ χ',
        ← val_cubAt hJ]
      exact congrArg (_ * ·) (val_pull hJ _ _ _))
  exact ⟨g, (isPullF_iff σ ξ g).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩⟩

theorem formEq_zero (χ : D.X) : FormEq (K' := PEmpty) (DegPre.gtφT D T (DegPre.zeroT D T) χ) DegPre.gtε
    PEmpty.elim PEmpty.elim := fun U _ h => by
  rw [Fin.prod_univ_four]
  show h (cP D T χ * 1).left ^ (-1 : ℤ) * h (cP D T χ).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  rw [_root_.mul_one]; simp

theorem isZero_restrict {σ : TF (R := R) F ⟶ T} {g : GtPt D T} {g' : GtPtF D F} (H : GtPt.IsPullF F σ.left g g')
    (h : g.IsZero) : g'.IsZero := by
  obtain ⟨hb, hv⟩ := (isPullF_iff σ g g').1 H
  refine (isZero_iff g').2 ⟨?_, fun χ y J hJ => (hv χ y J hJ).trans ((val_corr hJ (h.2 χ) _).trans (val_one _))⟩
  rw [hb, h.1]; exact MonObj.comp_one σ

theorem isAdd_restrict {σ : TF (R := R) F ⟶ T} {a b c : GtPt D T} {a' b' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hb : GtPt.IsPullF F σ.left b b') (Hc : GtPt.IsPullF F σ.left c c')
    (h : a.IsAdd b c) : a'.IsAdd b' c' := by
  obtain ⟨ab, av⟩ := (isPullF_iff σ _ _).1 Ha
  obtain ⟨bb, bv⟩ := (isPullF_iff σ _ _).1 Hb
  obtain ⟨cb, cv⟩ := (isPullF_iff σ _ _).1 Hc
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [cb, ab, bb, h.1]; exact MonObj.comp_mul _ _ _
  · have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) σ.left).trans (val_mul hJ _ _ _))
    have c : σ ≫ DegPre.cT D T χ = cP D _ χ := by rw [cP, comp_toUnit_assoc]
    rw [c, ← ab, ← bb] at e
    rw [av χ y J hJ, bv χ y J hJ, cv χ y J hJ]
    exact e

theorem isNsmul_restrict {σ : TF (R := R) F ⟶ T} {k : ℕ} {a c : GtPt D T} {a' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hc : GtPt.IsPullF F σ.left c c') (h : GtPt.IsNsmul k a c) :
    GtPtF.IsNsmul k a' c' := by
  obtain ⟨u, u0, us, rfl⟩ := h
  choose v hv using fun i => exists_isPullF σ (u i)
  exact ⟨v, isZero_restrict (hv _) u0, fun i => isAdd_restrict (hv _) Ha (hv _) (us i), isPullF_unique (hv _) Hc⟩

variable {W : (Spec (CommRingCat.of R)).Opens} {ψW : PsiOn D W} {S : Over W.toScheme}

end GlobalTheory.FieldRestrictionTest
end
end

