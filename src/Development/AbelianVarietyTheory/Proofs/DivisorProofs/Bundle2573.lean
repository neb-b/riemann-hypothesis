module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem GlobalTheory.Mum.Desc.lab_onto_of_labExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  intro R _ _ _ D A N hN lab F _ _ _ em lab' hext hon x
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Mum.qkPt_algClosure_bijective R D F em N hN
  have cancel : ∀ y y' : TFK (R := R) (Kb R) ⟶ A.A, baseEm em ≫ y = baseEm em ≫ y' → y = y' := by
    intro y y' h
    apply Over.OverMorphism.ext
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    exact spec_map_field_cancel em.toRingHom y.left y'.left (congrArg CommaMorphism.left h)
  have hlab : ∀ p p', QkExt em.toRingHom p p' → lab' p' = baseEm em ≫ lab p := by
    intro p p' hp
    apply Over.OverMorphism.ext
    exact hext p p' hp
  constructor
  · intro hx
    have hx' : (baseEm em ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    obtain ⟨p', hp'⟩ := (hon _).1 hx'
    obtain ⟨p, hp, -⟩ := h2 p'
    refine ⟨p, cancel _ _ ?_⟩
    rw [← hlab p p' hp, hp']
  · rintro ⟨p, rfl⟩
    obtain ⟨p', hp', -⟩ := h1 p
    have h3 := (hon (lab' p')).2 ⟨p', rfl⟩
    rw [hlab p p' hp'] at h3
    apply cancel
    rw [MonObj.comp_pow, h3, MonObj.comp_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEqui
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsPt_exists_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  intro R _ _ _ J hJ D A G _ _ U hG F _ _ _ k hk
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.exists_tors_closed R J hJ D A G hG U F k hk
  refine ⟨fun p => ⟨f p, (hf.1 p (f p)).2 rfl, ?_⟩, fun p p' x h h' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · exact (hf.2.2.1 p p').1 (((hf.1 p x).1 h).symm.trans ((hf.1 p' x).1 h'))

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem phiRel_famExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  intro R _ _ _ I hI D F _ _ _ em N hN p w p' w' hw hw' hp s s₁ H
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨hy, hb, hs⟩ := hp
  have hb' : p'.g.b = baseMap (R := R) (Kb R) F ≫ p.g.b := Over.OverMorphism.ext hb
  have hb2 : (baseMap (R := R) (Kb R) F).left ≫ p.g.b.left = p'.g.b.left := hb.symm
  have h0 : (baseMap (R := R) (Kb R) F).left ≫ (DegPre.zeroF D.toPre (Kb R)).left = (DegPre.zeroF D.toPre F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (baseMap (R := R) (Kb R) F))
  have j1 : (baseMap (R := R) (Kb R) F).left ≫ jFK (R := R) (Kb R) = jFK (R := R) F := specMap_jFK (R := R) (Kb R) F
  have j2 : (baseMap (R := R) (Kb R) F).left ≫ (TF (R := R) (Kb R)).hom = (TF (R := R) F).hom := Over.w _
  obtain ⟨w'', hw'', hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p'.g.b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) (pullGen_isGen _ _ _ _ hw.1 _)
  have hX : GlobalTheory.UT.TXFrame N p' w'' := by
    refine ⟨hw'', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w 2)
          (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.toPre.P.L _ _ ν p.g.b.left)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_pull hJ, Category.id_comp]
          exact (map_pow _ _ _).trans (hw.2.1 ν hν y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_pull hJ, hb2] at e
      rw [hv _ _ z J hJ, val_pull hJ, val_corr hJ (hs p'.y), val_pull hJ, hy, Category.id_comp, Category.id_comp]
      exact (map_pow _ _ _).symm.trans e
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _
          (LB.mulGen D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w N) (LB.pullGen D.toPre.P.L _ _ κ p.g.b.left))
          (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (D.toPre.psi p.y) (jFK (R := R) (Kb R)))
            (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
              (TF (R := R) (Kb R)).hom)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
            Category.id_comp]
          exact (congrArg₂ (· * ·) (map_pow _ _ _) rfl).trans (hw.2.2 κ hκ y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb2, j1, j2] at e
      rw [hv _ _ z J hJ, val_pull hJ, Category.id_comp, hy]
      exact (congrArg₂ (· * ·) (map_pow _ _ _).symm rfl).trans e
  have Cw : LB.Gen.Corr D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) :=
    corr_of_val D.toPre.P.isLB fun y J hJ =>
      ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p').2 w'' w' hX hw' y J hJ).symm.trans (hv _ _ y J hJ)
  rw [phiRel_iff hG p w hw.1] at H
  refine (phiRel_iff hG p' w' hw'.1 _ _).2 ?_
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D.toPre F p'.g.b ≫ famMap D.toPre (Kb R) F =
      famMap D.toPre (Kb R) F ≫ DegPre.trPt D.toPre (Kb R) p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D.toPre (Kb R) F)).trans (tr_pr D.toPre F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D.toPre (Kb R) _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D.toPre (Kb R) F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) (Kb R) F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D.toPre (Kb R) N α p.g.b (ρ ≫ famMap D.toPre (Kb R) F) z J = uVal D.toPre F N α p'.g.b ρ z J := by
    have : famMap D.toPre (Kb R) F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D.toPre (Kb R) F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, val_corr hJ Cw, val_pull hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsion_isLev : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  intro X g n B _ ζ sX c hζ S A _ y α hα F _ _ t x hx
  let β : B →+* F := (Spec.preimage ((t ≫ y) ≫ sX)).hom
  obtain ⟨-, hs, -⟩ := c.geom F (t ≫ y) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hx₁ : pushHom hα (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨a, ha⟩ := hs _ hx₁
  have hu : (toUnit (Over.mk (t ≫ y))).left = t ≫ y := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (t ≫ y) ≫ (c.lev a).left = x.left ≫ α := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  exact ⟨a, by rw [← e, Category.assoc]⟩

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem qkPt_g_eq_of_equiv : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  intro V _ _ D hB F _ _ k hk p p' hy ⟨z, hz, h, hi, ha⟩
  letI := GlobalTheory.TorusExt.gtGroup D F
  have hkz : k • z = 0 := by
    rw [hy] at hz
    exact left_eq_add.mp hz
  have z0 : z = 0 := by
    have : ((k : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hkz
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst z0
  have h0 : h = 0 := by
    obtain ⟨w, hw, g, hg, hadd⟩ := qk_equiv_refl hB p
    have hw0 : w = 0 := by
      have hkw : k • w = 0 := left_eq_add.mp hw
      have hwz : (k : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hkw
      rcases smul_eq_zero.mp hwz with hk0 | hw0
      · omega
      · exact hw0
    subst w
    have he : h = g := GlobalTheory.TorusExt.isIota_unique hi hg
    have heq := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd
    have hg0 : g = 0 := by
      have : p.g + g = p.g + 0 := by simpa using heq.symm
      exact add_left_cancel this
    exact he.trans hg0
  rw [(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ha, h0, add_zero]

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointWithTermsLabelClassZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.TermsLabel

theorem yy_zero_of_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro g n F W Z i X₁ z₁ act x₀ V _ _ _ ev X _ m t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, sec, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero]
  have hiota0 : ∀ (h : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V))), h.IsZero → h.IsIota 0 := by
    open GlobalTheory.TorusExt in
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th 𝔪.D.toPre (T := TF (R := V) (AlgebraicClosure (FractionRing V))) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (𝔪.D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub 𝔪.D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) (AlgebraicClosure (FractionRing V)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) :=
    ⟨0, gb, _, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 rfl,
      hiota0 _ ((GlobalTheory.TorusExt.isZero_iff_eq _).2 hkgb)⟩
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.T.exists_generic_frame_liesOver_of_y_eq_zero V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.Poinc.Sep.TermsLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ χ hχ hpt a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hK : KerPowSt := hL.1.kerPow
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p, x, hpy, hpg, hpx, hxo⟩ := hpt (torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ))
    ((isTor_iff _ _).2 (isTorusPtF_torusPt χ))
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  obtain ⟨p₁, hext, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p
  set χ₁ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ with hχ₁
  have hp₁g : p₁.g = torusPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (Additive.ofMul χ₁) := by
    have hg := (eq_gtExt_iff (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p.g p₁.g).2 hext.2
    rw [hg, hpg]
    exact gtExt_torusPt _ hf χ
  have hp₁y : p₁.y = 0 := hext.1.trans hpy
  have hτ₁ : IsTor χ₁ p₁.g := by rw [hp₁g]; exact (isTor_iff _ _).2 (isTorusPtF_torusPt χ₁)
  have W₁ := weilQkIs_tor hG p₁ p' hp₁y hτ₁
  have hx₁ := (qkToAkU_iff_of_algebra hG hK 𝔪.U hk hext x).1 hpx
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk p₁ p' _ x' hx₁ hp'x (χ₁ (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    (fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x) x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [hχ₁, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [Units.val_one, one_smul]
    refine (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective ?_
    have hc : (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (eStd X₁.S.g _ τ a).val =
        algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ a).val)) := by
      simp only [pow_mul, map_pow]
    rw [e']
    exact congrArg (fun z => algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK z)) hc
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [Over.comp_left, Category.assoc, hxo]
    rfl
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  first | exact @GlobalTheory.Mum.TraitValue.value | exact GlobalTheory.Mum.TraitValue.value | (intros; apply GlobalTheory.Mum.TraitValue.value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G) (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1])) (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])), φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 → LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left)) (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | exact GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | (intros; apply GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs <;> assumption)
end

