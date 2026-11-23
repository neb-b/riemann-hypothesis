module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TautTransport

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem base_sq : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  intro R V _ _ _ _ f F₀ _ _ F _ _ j hj
  have e₁ : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) := by
    rw [← spMap_comp_spMap']; rfl
  have e₂ : (TF (R := V) F).hom = spMap ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) := by
    rw [← spMap_comp_spMap']; rfl
  rw [e₁, e₂, spMap_comp_spMap', spMap_comp_spMap']
  congr 1
  exact RingHom.ext fun r => hj r

theorem val_tr : ∀ {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀), letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra; ∀ (g₁ : GtPtF D₀ F), g₁.b.left = spMap j ≫ g₀.b.left → (∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) → ∀ (χ : D₀.X) (z : Sp F) J, Good D₀.P.L z J → val (g₁.s χ) (𝟙 _) z J = Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (g₀.s χ) (𝟙 _) (spMap j z) (fun ψ => J (spMap j ≫ ψ))) := by
  intro R _ _ D₀ F₀ F _ _ _ j g₀ g₁ _ hs χ z J hJ
  refine (val_corr hJ (hs χ) (𝟙 (Sp F))).trans ((val_pull hJ (g₀.s χ) (spMap j) (𝟙 (Sp F))).trans ?_)
  have e := (GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap (g₀.s χ) (spMap j) (𝟙 (Sp F₀)) hJ).symm
  rw [Category.comp_id] at e
  rw [Category.id_comp]
  exact e

theorem lamVal_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J₁ J₀ J', Good T.M.L z J₁ → Good D₀.toPre.P.L z J₀ → Good D.P.L z J' → lamVal w' p z J₁ J' = lamVal w (p ≫ sqOf (pull_grp hD)) z J₁ J₀ * ∏ I, gw hD.w (p ≫ lamφ D.P.A I) z (J₀ ((p ≫ lamφ D.P.A I) ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (J' (p ≫ lamφ D.P.A I)) ^ lamε I := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ Z p z J₁ J₀ J' hJ₁ hJ₀ hJ'
  obtain ⟨-, sq₀, gen₀, -⟩ := id h₀
  obtain ⟨-, sq₁, gen₁, -⟩ := id h₁
  obtain ⟨w'', gen'', hval⟩ := _root_.GlobalTheory.TautPull.lamIso_comp_exists (pull_grp hD) (β₂ := ββ) T.M.isLB D₀.toPre.P.isLB D.P.isLB w hD.w gen₀ hD.w_gen
  have hββ : ββ' = sqOf (pull_grp hD) ≫ ββ := GlobalTheory.LamRigid.square_over_hom_ext
    (by rw [sq₁.1, Category.assoc (sqOf _), sq₀.1, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).1]; simp only [Category.assoc])
    (by rw [sq₁.2, Category.assoc (sqOf _), sq₀.2, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).2]; simp only [Category.assoc])
  subst hββ
  refine (_root_.GlobalTheory.TautUniq.lamVal_eq_of_rig T.M.isLB D.P.isLB D.P.isAb w' w'' gen₁ gen'' ?_ ?_ Z p z J₁ J' hJ₁ hJ').trans (hval Z p z J₁ J₀ J' hJ₁ hJ₀ hJ')
  · intro T' z' K K' hK hK'
    exact (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n V D (f.comp ω) (fun i => f (s i)) (hD.xe.trans e) _ _ w' hB h₁ T' 1 z' K K' hK hK').1
  · intro T' z' K K' hK hK'
    obtain ⟨K₀, hK₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := T'.left) z'
    rw [hval _ _ z' K K₀ K' hK hK₀ hK', lift_sqOf]
    have o : pushPt (pull_grp hD).1.w (1 : T' ⟶ D.P.A) = 1 := map_one (pushHom (pull_grp hD) T')
    rw [o, (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n R D₀.toPre ω s e β ββ w D₀.tau_bimult h₀ (Over.mk (T'.hom ≫ spMap f)) 1 z' K K₀ hK hK₀).1, _root_.one_mul]
    rw [prod_lam (1 : T' ⟶ D.P.A) 1 (fun q => gw hD.w q z' (K₀ (q ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (K' q)), _root_.mul_one]
    simp only [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem ag {G : Type*} [CommGroup G] (A B C D v w L τ k Λ : G) (hΛ : Λ = A * B⁻¹ * C⁻¹ * D)
    (hv : w = A⁻¹ * B * C * D⁻¹ * v) (h : w = k * (L * τ)) : v = k * (L * Λ * τ) := by
  subst hΛ
  rw [hv] at h
  rw [← mul_right_inj (A⁻¹ * B * C * D⁻¹), h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tautPt_tr : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', Function.Injective f → D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ (a : Fin T.r → ℤ) (g₀ : GtPtF D₀.toPre F₀) (g : GtPtF D F), TautPt T ω s ε n D₀.toPre e β ββ w F₀ a g₀ → Tr f hD j g₀ g → TautPt T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' F a g := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hf hB h₀ h₁ F₀ _ _ F _ _ j hj a g₀ g hg₀ htr
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  obtain ⟨g₁, ⟨hb₁, hs₁⟩, hpull⟩ := htr
  obtain ⟨hpt₀, hv₀⟩ := hg₀
  have bsq := base_sq f F₀ F j hj
  have hπ := hpull.1
  refine ⟨?_, fun χ => ?_⟩
  · calc g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β = g₁.b.left ≫ β := by
          rw [← hπ]; simp only [Category.assoc]
      _ = spMap j ≫ g₀.b.left ≫ β := by rw [hb₁, Category.assoc]
      _ = spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω ≫ (T.c₀ a).left := by rw [hpt₀]
      _ = _ := by
          rw [← Category.assoc, bsq, Category.assoc, ← Category.assoc (spMap f), spMap_comp_spMap']
  · obtain ⟨k₀, hk₀, hv⟩ := hv₀ (hD.xe χ)
    refine ⟨Units.map j.toMonoidHom k₀, ?_, fun z J₁ J' hJ₁ hJ' => ?_⟩
    · show j (k₀ : F₀) = _
      rw [hk₀, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [map_zpow₀, hj]; rfl
    · obtain ⟨J₀, hJ₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := Sp F) z
      have pv := GlobalTheory.ArcPull.pullGt_val hD hpull χ (𝟙 _) hJ₀ hJ'
      have vt := val_tr j g₀ g₁ hb₁ hs₁ (hD.xe χ) z J₀ hJ₀
      have hv' := hv (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ)) (fun ψ => hJ₁ (spMap j ≫ ψ))
        (fun ψ => hJ₀ (spMap j ≫ ψ))
      have lp := lamVal_pull T ε n R V J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ _
        (lift (DegPre.cF D F χ) g.b).left z J₁ J₀ J' hJ₁ hJ₀ hJ'
      have hpq : spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left =
          (lift (DegPre.cF D F χ) g.b).left ≫ sqOf (pull_grp hD) := by
        apply GlobalTheory.LamRigid.square_over_hom_ext
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).1, ← Category.assoc _ (fst D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
          show spMap j ≫ (TF (R := R) F₀).hom ≫ (D₀.toPre.c (hD.xe χ)).left = ((TF (R := V) F).hom ≫ (D.c χ).left) ≫ _
          rw [Category.assoc, hD.c_pr χ, ← Category.assoc, ← Category.assoc, bsq]
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).2, ← Category.assoc _ (snd D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hb₁, ← hπ]
      have hsp : spMap (RingHom.id F) = 𝟙 (Sp F) := by
        simp [spMap]
      have hgm : gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn (Units.map j.toMonoidHom k₀)) := by
        rw [Category.comp_id, GlobalTheory.ArcSpecialise.gm_unitOn_spMap j k₀ z]
        have := GlobalTheory.ArcSpecialise.gm_unitOn_spMap (RingHom.id F) (Units.map j.toMonoidHom k₀) z
        rw [hsp] at this
        exact this.symm
      have m := congrArg (Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom) hv'
      have lc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (lamVal w (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ))) = lamVal w (spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left) z J₁ J₀ :=
        (GlobalTheory.HalfBC.lamVal_comp w (spMap j) _ z J₁ J₀ hJ₁ hJ₀).symm
      have tc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) ((TF (R := R) F₀).hom ≫ spMap ω) (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ))) = val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) (spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω) z J₁ :=
        GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap _ (spMap j) _ hJ₁
      have gc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (gm (𝟙 (TF (R := R) F₀).left) (spMap j z) ⊤ (unitOn k₀)) = gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) :=
        (GlobalTheory.ConstFam.gm_comp_stalkMap (spMap j) (𝟙 _) z ⊤ trivial _).symm
      rw [← vt, map_mul, map_mul, lc, tc, gc, hpq, hgm] at m
      have tm : spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω = (TF (R := V) F).hom ≫ spMap (f.comp ω) := by
        rw [← Category.assoc, bsq, Category.assoc, spMap_comp_spMap']
      rw [tm] at m
      have hΛ := prod_lam (DegPre.cF D F χ) g.b (fun q => GlobalTheory.ArcPull.om hD.w z J₀ J' q)
      rw [lp]
      simp only [Category.id_comp] at pv
      exact ag _ _ _ _ _ _ _ _ _ _ hΛ pv m

end GlobalTheory.TautTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointZeroAndPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem appTop_spec_inv {R S : CommRingCat} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) = (Scheme.ΓSpecIso S).inv.hom (f.hom a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem tautologicalChart_baseGenerator_zero_right {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (a : Fin T.r → ℤ)
    (z J) (hJ : Good T.M.L z J) : val (T.τ₀ a 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [T.c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [add_zero, f, _root_.mul_one] at h
  exact (T.τ₀_symm a 0 z J hJ).trans (mul_eq_left.1 h.symm)

theorem base_eq {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] {T : TautBase o W}
    {ω : W →+* V} {D : DegPre V} {β : D.P.A.left ⟶ T.B.left} (hpb : IsGrpPullback D.P.A T.B (spMap ω) β)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {x : D.X} {a : Fin T.r → ℤ}
    (hc : (D.c x).left ≫ β = spMap ω ≫ (T.c₀ a).left) (g : GtPtF D F)
    (hg : g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left) : g.b = DVR.cP D (TF (R := V) F) x := by
  have ht : (toUnit (TF (R := V) F)).left = (TF (R := V) F).hom := by
    simpa using Over.w (toUnit (TF (R := V) F))
  ext1
  apply hpb.1.hom_ext
  · rw [hg, DVR.cP, Over.comp_left, Category.assoc, hc, ← Category.assoc, ht, Category.assoc]
  · rw [Over.w g.b, Over.w (DVR.cP D (TF (R := V) F) x)]

end GlobalTheory.TInj

theorem GlobalTheory.TInj.tautPt_zero_iota : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (g : GtPtF D F), (TautPt T ω s ε n D e β ββ w F 0 g → g.IsZero) ∧ ∀ y : D.X, TautPt T ω s ε n D e β ββ w F ((n : ℤ) • e y) g → GtPtF.IsIota y g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ g
  have hF' := hF
  obtain ⟨hpb, -, -, hc, hτ⟩ := hF
  refine ⟨fun h => ?_, fun y h => ?_⟩
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = 1 := by
      have := GlobalTheory.TInj.base_eq hpb (x := 0) (a := 0) (by rw [hc 0, map_zero, smul_zero]) g hb
      rwa [cPoint_zero] at this
    refine (isZero_iff g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    rw [hval z I₀ J' hJ hJ']
    have k1 : k = 1 := Units.ext (by rw [hk]; simp)
    have l1 := (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) z I₀ J' hJ hJ').2
    have t1 : val (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) z I₀ = 1 := by
      apply Units.ext
      have v := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) (𝟙 _) hJ
      rw [Category.comp_id] at v
      have t0 := GlobalTheory.TInj.tautologicalChart_baseGenerator_zero_right T ((n : ℤ) • e χ) _ _ (GlobalTheory.LevelExpansion.good_comp ((TF (R := V) F).hom ≫ spMap ω) hJ)
      rw [v]
      erw [t0]
      rw [Units.val_one, map_one, Units.val_one]
    rw [hb', l1, t1, k1]
    simp [unitOn]
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = DVR.cP D (TF (R := V) F) y := GlobalTheory.TInj.base_eq hpb (hc y) g hb
    refine (isIota_iff y g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    obtain ⟨k₀, hk₀, hval₀⟩ := hτ χ y
    have e₀ := hval₀ (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ)) (fun ψ => J' (jFK (R := V) F ≫ ψ))
      (GlobalTheory.LevelExpansion.good_comp _ hJ) (GlobalTheory.LevelExpansion.good_comp _ hJ')
    rw [hval z I₀ J' hJ hJ', Category.id_comp, GlobalTheory.DegCompare.val_tau_symm _ hJ' y χ]
    have v := GlobalTheory.LevelExpansion.val_comp (D.tau χ y) (jFK (R := V) F) (𝟙 _) hJ'
    rw [Category.comp_id] at v
    have hl : (lift (DegPre.cF D F χ) g.b).left =
        jFK (R := V) F ≫ (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left := by
      rw [hb']
      have : lift (DegPre.cF D F χ) (DVR.cP D (TF (R := V) F) y) =
          (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫
            lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y) := by
        rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      rw [this, Over.comp_left]; rfl
    have hL := GlobalTheory.HalfBC.lamVal_comp w (jFK (R := V) F)
      (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left z I₀ J' hJ hJ'
    have vt : (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) ((TF (R := V) F).hom ≫ spMap ω) z I₀).val =
        (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y))
          ((TK V).hom ≫ spMap ω) (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ))).val := by
      have := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) (jFK (R := V) F) ((TK V).hom ≫ spMap ω) hJ
      rw [← Category.assoc] at this
      exact this
    have hkk : (algebraMap (FractionRing V) F) (k₀ : FractionRing V) = (k : F) := by
      rw [hk, hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, map_zsmul, smul_eq_mul]
    have hg : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) =
        Units.map (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom.toMonoidHom
          (gm (𝟙 (TK V).left) (jFK (R := V) F z) ⊤ (unitOn k₀)) := by
      rw [← GlobalTheory.ConstFam.gm_comp_stalkMap _ _ z ⊤ trivial, Category.comp_id]
      have := gm_comp_top (𝟙 (TF (R := V) F).left) (jFK (R := V) F) z (unitOn k₀) (unitOn k) (by
        simp only [unitOn, Units.coe_map, MonoidHom.coe_coe]
        exact (GlobalTheory.TInj.appTop_spec_inv (CommRingCat.ofHom (algebraMap (FractionRing V) F)) (k₀ : FractionRing V)).trans
          (congrArg _ hkk))
      rw [Category.id_comp] at this
      exact this.symm
    apply Units.ext
    rw [v, e₀]
    simp only [Units.val_mul, map_mul]
    rw [hg, hl, hL, vt]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiPosTendstoZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hψ hW hQ
  obtain ⟨hN, hI, -, -⟩ := hR
  have hk0 : ∀ a b, ∃ k, Q.TauCoord a b k ∧
      (a = b → a ≠ 0 → ∃ s ∈ maximalIdeal R, (k : FractionRing R) = algebraMap R _ s) := by
    intro a b
    by_cases h : a = b ∧ a ≠ 0
    · obtain ⟨rfl, ha⟩ := h
      obtain ⟨s, hs, k, hk, hc⟩ := hQ a ha
      exact ⟨k, hc, fun _ _ => ⟨s, hs, hk⟩⟩
    · obtain ⟨k, hk⟩ := _root_.GlobalTheory.Mum.TensPol.exists_tauCoord R Q a b
      exact ⟨k, hk, fun e ne => (h ⟨e, ne⟩).elim⟩
  choose k hk hkp using hk0
  obtain ⟨hs, ha⟩ := _root_.GlobalTheory.Mum.TensPolRel.tauCoord_rel R Q k hk
  obtain ⟨ga', a', h'⟩ := GlobalTheory.exists_psiScal R D'
  obtain ⟨hp, ht⟩ := _root_.GlobalTheory.Mum.TensPolScal.scalars_tens R Q.X k hs ha (fun y hy => hkp y y rfl hy) W hW (fun z => a' (xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods R Q D' W pr xe w hψ k hk ga' a' h' (xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (xe χ) (fun h0 => hχ (xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_embed_integral {V W K : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Field K]
    [IsAlgClosed K] (g : V →+* W) (hg : g.IsIntegral) (hgi : Function.Injective g) (j : V →+* K)
    (hj : Function.Injective j) : ∃ j' : W →+* K, j'.comp g = j ∧ Function.Injective j' := by
  letI := g.toAlgebra
  letI := j.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨hg⟩
  haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hgi
  haveI : Module.IsTorsionFree V K := Module.isTorsionFree_iff_algebraMap_injective.2 hj
  let f : W →ₐ[V] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hc : f.toRingHom.comp (algebraMap V W) = j := RingHom.ext fun a => f.commutes a
  refine ⟨f.toRingHom, hc, ?_⟩
  have hk : (RingHom.ker f.toRingHom).comap (algebraMap V W) = ⊥ := by
    rw [RingHom.comap_ker, hc]
    exact (RingHom.injective_iff_ker_eq_bot j).1 hj
  exact (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hk)

theorem prim_descend {V W K K' : Type} [CommRing V] [CommRing W] [Field K] [Field K'] (g : V →+* W)
    (hg : g.IsIntegral) (i : V →+* K) (k : K →+* K') (i' : W →+* K') (h : i'.comp g = k.comp i) {J : Type}
    (c : J → K) (hp : Prim i' (fun a => k (c a))) : Prim i c := by
  have up : ∀ x : K', i'.IsIntegralElem x → (k.comp i).IsIntegralElem x := by
    intro x hx
    letI := g.toAlgebra
    letI := i'.toAlgebra
    letI := (k.comp i).toAlgebra
    haveI : Algebra.IsIntegral V W := ⟨hg⟩
    haveI : IsScalarTower V W K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun h a).symm
    exact isIntegral_trans (R := V) (A := W) x hx
  have down : ∀ y : K, (k.comp i).IsIntegralElem (k y) → i.IsIntegralElem y := by
    rintro y ⟨p, hm, he⟩
    refine ⟨p, hm, k.injective ?_⟩
    rw [map_zero, Polynomial.hom_eval₂]
    exact he
  refine ⟨fun a => down _ (up _ (hp.1 a)), ?_⟩
  obtain ⟨a, ha, hinv⟩ := hp.2
  refine ⟨a, fun e => ha (by simp [e]), down _ ?_⟩
  rw [map_inv₀]
  exact up _ hinv

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

theorem thList_move {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {T : Over S} (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    (h₁ : Over.mk x₁ ⟶ T) (h₂ : Over.mk x₂ ⟶ T) (hl : h₁.left = h₂.left) {N : ℕ} (pt : Fin N → (Over.mk x₁ ⟶ G))
    (c : Fin N → K) (hT : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ s) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ s) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext hl
  exact ⟨pt, hT⟩

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem prim_of_polFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S), PolFib t.G t.PP.L g (jK V ≫ χ) → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t g V _ _ _ hV χ hpf σ hσ m N hm hm3 hmu K _ i pt c hi hT
  obtain ⟨hd, hc, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  haveI := hd
  haveI := h0
  obtain ⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H (Sp V), Nonempty (SABMap t₁ t χ) := by
    obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, m', -⟩ := sabPull Out.CubePf.cubePull χ t
    exact ⟨_, ⟨m'⟩⟩
  obtain ⟨W, _, _, _, _, gW, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hc t₁.G t₁.semi
  obtain ⟨t₂, m₂, hS⟩ : ∃ (t₂ : SAB H (Sp W)) (_ : SABMap t₂ t₁ (spMap gW)),
      ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t₂.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m', -⟩ := sabPull Out.CubePf.cubePull (spMap gW) t₁
    exact ⟨_, m', Ex, hEx⟩
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
  have hp0 : GlobalTheory.LN.PolAt t (jK V ≫ χ) := polAt_of_polFib t g _ hpf
  have hp1 := GlobalTheory.DatUniq.polAt_pull m₁ hp0 (jK V) (𝟙 _) (Category.id_comp _)
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp gW) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  let gam : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg' : ∀ r, gam (algebraMap _ _ r) = algebraMap W _ (gW r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value gam
  have hgam : spMap gam ≫ jK V = jK W ≫ spMap gW := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg'))
  have hp2 := GlobalTheory.DatUniq.polAt_pull m₂ hp1 (jK W) (spMap gam) hgam
  have hW : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hcW, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t₂ hp2 hS
  have hσ' := nz_pull S t.G t.PP.L t.PP.isLB t.semi V W χ σ gW hσ
  have hmuW : IsUnit (m : W) := by simpa using hmu.map gW
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨i', hi'c, hi'⟩ := exists_embed_integral gW hgi hginj (k.comp i) (k.injective.comp hi)
  obtain ⟨pt₁, -, hT₁⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K (AlgebraicClosure K) k
    (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c hT
  let a₁ : Over.mk (spMap k ≫ spMap i ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (spMap k) rfl
  let a₂ : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let b₁ : Over.mk (spMap i' ≫ spMap gW ≫ χ) ⟶ Over.mk (spMap gW ≫ χ) := Over.homMk (spMap i') rfl
  let b₂ : Over.mk (spMap gW ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap gW) rfl
  have e₁ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) k = VVRank.pullS t.G _ (a₁ ≫ a₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have e₂ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ gW) i' = VVRank.pullS t.G _ (b₁ ≫ b₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have hx : spMap i' ≫ spMap gW = spMap k ≫ spMap i := by
    rw [spMap_comp_eq', spMap_comp_eq', hi'c]
  rw [e₁] at hT₁
  obtain ⟨pt₂, hT₂⟩ := thList_move t.G t.PP.L t.PP.rig m σ (by rw [← Category.assoc, ← hx, Category.assoc])
    (a₁ ≫ a₂) (b₁ ≫ b₂) (by simp [a₁, a₂, b₁, b₂, hx]) pt₁ _ hT₁
  rw [← e₂] at hT₂
  exact prim_descend gW hgi i k i' hi'c c
    (_root_.GlobalTheory.UMin.PrimTrait.main E H S t W hW (spMap gW ≫ χ) t₂ ⟨n⟩ ⟨U⟩ _ hσ' m N hm hm3 hmuW _ i' pt₂ _ hi' hT₂)

end GlobalTheory.UMin
end
end

