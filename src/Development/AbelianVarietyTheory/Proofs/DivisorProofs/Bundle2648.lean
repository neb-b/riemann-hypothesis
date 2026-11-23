module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.IsoLin

variable {S : Scheme.{0}}

theorem transl_mul' {G : Over S} [GrpObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl (x * y) = Hecke.transl x ≫ Hecke.transl y := by
  simp only [Hecke.transl, comp_mul, Category.comp_id, Category.id_comp]
  rw [← Category.assoc _ (toUnit G) y, toUnit_unique (_ ≫ toUnit G) (toUnit G), _root_.mul_assoc]

theorem transl_comm {G : Over S} [GrpObj G] [IsCommMonObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl x ≫ Hecke.transl y = Hecke.transl y ≫ Hecke.transl x := by
  rw [← transl_mul', ← transl_mul', _root_.mul_comm]

theorem lift_mul_lift' {A : Over S} [GrpObj A] (a b c d : 𝟙_ (Over S) ⟶ A) :
    (lift (a * c) (b * d) : 𝟙_ (Over S) ⟶ G2 A) = lift a b * lift c d := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem surj_appTop {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (fst A A).left.appTop.hom ∧ Function.Surjective (snd A A).left.appTop.hom := by
  have h2 := (GlobalTheory.globalFns_holds S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2
  have w1 : (G2 A).hom = (fst A A).left ≫ A.hom := (Over.w (fst A A)).symm
  have w2 : (G2 A).hom = (snd A A).left ≫ A.hom := (Over.w (snd A A)).symm
  refine ⟨?_, ?_⟩
  · rw [w1, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2
  · rw [w2, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2

theorem rig_lbPow {X Y : Scheme.{0}} (P : LB X) (hP : P.IsLB) (m : ℕ) (f : Y ⟶ X)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : ((Hecke.lbPow P m).pull f).Gen, t.IsGen := by
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1))).2 h
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB _ hQ (fun _ : PUnit => f) (fun _ => 1))).1 ?_
  have e : GlobalTheory.CechPic.cls _ hQ = (m : ℤ) • GlobalTheory.CechPic.cls P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (fun _ : Fin m => 𝟙 X) (fun _ => 1) hQ).trans ?_
    simp [GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.cls_pull hQ f, e, map_zsmul,
    ← GlobalTheory.CechPic.cls_pull hP f (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1)), h0, smul_zero]

end GlobalTheory.IsoLin

namespace GlobalTheory.IsoLin

theorem exists_linearisation_isotropic : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  intro S A _ _ hA P hP hr1 hr2 m H hH1 hH2 hW
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have q1 := rig_lbPow P hP m _ hr1
  have q2 := rig_lbPow P hP m _ hr2
  obtain ⟨sf, ss⟩ := surj_appTop hA
  have hm1 : ∀ a c : H, (lift ((a * c : H) : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A) = lift (a : 𝟙_ (Over S) ⟶ A) 1 * lift (c : 𝟙_ (Over S) ⟶ A) 1 := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  have hm2 : ∀ a c : H, (lift 1 ((a * c : H) : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) = lift 1 (a : 𝟙_ (Over S) ⟶ A) * lift 1 (c : 𝟙_ (Over S) ⟶ A) := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  obtain ⟨v₁, hv₁, cv₁⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (fst A A).left
    (lift (𝟙 A) (1 : A ⟶ A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left]) sf
    (Hecke.lbPow P m) hQ q2 H (fun a => (Hecke.transl (lift (a : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => _root_.GlobalTheory.TranslFst.iso_transl_fst S A hA _ hQ q1 q2 a (hH1 a a.2))
  obtain ⟨v₂, hv₂, cv₂⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (snd A A).left
    (lift (1 : A ⟶ A) (𝟙 A)).left (by rw [← Over.comp_left, lift_snd, Over.id_left]) ss
    (Hecke.lbPow P m) hQ q1 H (fun a => (Hecke.transl (lift 1 (a : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => _root_.GlobalTheory.TranslInv.translSnd S A hA _ hQ q1 q2 a (hH2 a a.2))
  exact GlobalTheory.T.exists_linearization_prod (G2 A).left (Hecke.lbPow P m) hQ H H _ _
    (fun p => (Hecke.transl (lift (p.1 : 𝟙_ (Over S) ⟶ A) (p.2 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun p => by
      show _ = (Hecke.transl _ ≫ Hecke.transl _).left
      rw [← transl_mul', ← lift_mul_lift', _root_.mul_one, _root_.one_mul])
    (fun a b => by rw [← Over.comp_left, ← Over.comp_left, transl_comm])
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    v₁ v₂ hv₁ hv₂ cv₁ cv₂
    (fun a b => GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ hQ _ _ (v₁ a) (v₂ b) (hv₁ a) (hv₂ b) (hW a a.2 b b.2))

end GlobalTheory.IsoLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

theorem GlobalTheory.HomMum.exists_gen_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), IsNrm u → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ u hu hadd
  obtain ⟨W, hW, h₁, h₂⟩ := _root_.GlobalTheory.Mum.Two.GlueLevel.exists_iso_level U₁ U₂ e
  obtain ⟨v, hv, hm⟩ := _root_.GlobalTheory.HomMum.exists_gen_mul_level U₁ U₂ e hf hg W hW h₁ h₂ u hu.1 hadd
  exact _root_.GlobalTheory.HomMum.exists_gen_thick_two U₁ U₂ e hf hg v hv (_root_.GlobalTheory.HomMum.gen_invariant_of_mul U₁ U₂ e hf hg v hv hm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedGeneratorOfFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwNorm

open GlobalTheory.TwFac

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_normalised (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a]
    (hh : ∀ y, D.c (h y) = D.c y ≫ a) (n j : ℤ) (mu β' : D.X)
    (g : ∀ y : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c y).left) (fun _ => -1)))
    (hg : ∀ y, (g y).IsGen)
    (w : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j))) (hw : w.IsGen) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) J, Good D.P.L z J →
        val u (r ≫ eSec D.P.A) z J = val (g mu) r z J ^ n * val (g (h mu)) r z J ^ j * val D.rig r z J ^ (n + j) := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (g mu) (hg mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (g (h mu)) (hg _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rig D.rig_gen (n + j)
  have i₀ : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _
  have a₁ : ∀ χ, DVR.cP D (𝟙_ _) χ = D.c χ := fun χ => by rw [DVR.cP, i₀, Category.id_comp]
  have a₂ : η[D.P.A] = 1 := by rw [Hom.one_def, i₀, Category.id_comp]
  have z₃ : η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu) = D.c mu := by
    refine (MonObj.comp_mul _ (𝟙 _) (DVR.cP D _ mu)).trans ?_
    rw [DVR.comp_cP, Category.comp_id, a₂, _root_.one_mul, a₁]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (toUnit D.P.A).left (eSec D.P.A)
    (congrArg (fun q => q.left) (toUnit_unique (η[D.P.A] ≫ toUnit _) (𝟙 _))) (fun U _ f => by
      have q₁ := prod_t D a β' n j η[D.P.A] f
      have q₂ := prod_t D a 0 n j (η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)) f
      have b₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      conv_rhs at q₁ => rw [a₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, ← hh, cPoint_zero, _root_.mul_one]
      simp only [Over.comp_left, Category.assoc] at q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      have a₃ : eSec D.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left := congrArg (fun q => q.left) a₂
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) h₃)
  have hc := corr_of_val D.P.isLB (t := LB.pullGen D.P.L _ _ u (eSec D.P.A))
    (t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃) fun y J hJ => by
      rw [val_pull hJ, Category.id_comp]; exact vu y J hJ
  refine ⟨u, hu, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc r).trans ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) (v₃ _ _ _ _))

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (x : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau x 0) (𝟙 _) z J = 1 := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero x), mul_inv_cancel, _root_.one_mul,
    GlobalTheory.PsiInPow.val_psi_zero D hB hJ, inv_inv, mul_inv_cancel]

def germK (K : Type) [Field K] (z : Sp K) : K →+* (Sp K).presheaf.stalk z :=
  ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem gs_sec {K : Type} [Field K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) (z : Sp K) (c : K) :
    gs e z ⊤ (scal p c) = germK K z c := by
  refine (gs_pull e p z ⊤ trivial _).trans ?_
  rw [he, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_generic (z : Sp (FractionRing R)) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = germK (FractionRing R) z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Sp (FractionRing R)).presheaf.germ ⊤ z trivial).hom nat.symm

theorem const_eq {S : Type} [CommRing S] {u u₀ p t k k' G : Sˣ} {c r : S} {m : ℤ} (e₁ : u.val = c * u₀.val)
    (e₂ : u = p * t * k ^ m) (ht : t = 1) (hk : k = k') (e₃ : p.val = r * G.val) (e₄ : u₀ = G * k' ^ m) : c = r := by
  subst ht hk e₂
  refine (Units.mul_left_inj u₀).1 ?_
  rw [← e₁, e₄, _root_.mul_one, Units.val_mul, Units.val_mul, e₃, _root_.mul_assoc]

theorem exists_gen_fac : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ hR D a a' h h' hE N _ r g hg hr ν
  have ha : IsMonHom a := hE.1
  have hh : ∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a := hE.2.2.2.1
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hR D a a' h h' hE N (-1) ν 0 (shift h h' N (-1) ν) (zero_add _).symm
  obtain ⟨u₀, hu₀, v₀⟩ := exists_normalised D.toPre a h hh N (-1) ν _ g hg w hw
  refine ⟨u₀, hu₀, fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := (fac_exists_unique_const R hR D a h ha hh N (-1) ν 0 _ u₀ hu₀).2.2 u hu.1
  suffices e : c = algebraMap R (FractionRing R) (r ν) by subst e; exact hc
  obtain ⟨z⟩ : Nonempty (Sp (FractionRing R)) := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun ψ : Sp (FractionRing R) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  have j₁ : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : (DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (toUnit (TK R)).left ≫ eSec D.toPre.P.A := by
    refine (congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) (FractionRing R))) (toUnit _ ≫ η[D.toPre.P.A]))).trans ?_
    show (jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left) ≫ eSec D.toPre.P.A = _
    rw [j₁, Category.id_comp]
  have e₁ := hc _ (DegPre.zF D.toPre (FractionRing R)).left z J hJ
  have e₂ := hu.2 z J hJ
  have e₃ := hr ν z J hJ
  have e₄ := v₀ _ (toUnit (TK R)).left z J hJ
  have e₅ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (toUnit (TK R)).left z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val D.toPre.rig q z J) (Category.id_comp _))
  rw [j₁, zpow_natCast, zpow_neg_one] at e₂
  rw [zpow_natCast, zpow_neg_one] at e₄
  have e₆ := gs_sec _ _ (congrArg (fun q => q.left) z₁) z c
  have e₇ := gs_generic z (r ν)
  exact (germK (FractionRing R) z).injective (e₆.symm.trans ((const_eq e₁ e₂ (val_tau_zero D.toPre D.tau_bimult ν hJ) e₅ e₃
    ((congrArg (fun q => val u₀ q z J) z₂).trans e₄)).trans e₇))

end GlobalTheory.TwNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionLineBundlePowFiniteInt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowNowhereZero

theorem tensSec (T : Scheme.{0}) [IsAffine T] (A B : LB T) (hA : A.IsLB) (hB : B.IsLB) :
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B)) :=
  _root_.GlobalTheory.SecTensor.tensorSecEquiv T A B hA hB

variable {T : Scheme.{0}}

def tp (L : LB T) (k : ℕ) : LB T :=
  Nat.rec (LB.triv T) (fun _ M => CechPic.tens L M) k

theorem isLB_tp {L : LB T} (hL : L.IsLB) : ∀ k, (tp L k).IsLB
  | 0 => LB.isLB_triv T
  | k + 1 => CechPic.isLB_tens hL (isLB_tp hL k)

theorem cls_tp {L : LB T} (hL : L.IsLB) : ∀ k, CechPic.cls (tp L k) (isLB_tp hL k) = k • CechPic.cls L hL
  | 0 => by simp only [zero_smul]; rfl
  | k + 1 => by
    rw [succ_nsmul']
    change CechPic.cls (CechPic.tens L (tp L k)) (CechPic.isLB_tens hL (isLB_tp hL k)) = _
    rw [CechPic.cls_tens hL (isLB_tp hL k), cls_tp hL k]

theorem mk_tp [IsAffine T] {L : LB T} (hL : L.IsLB) : ∀ k,
    @CommRing.Pic.mk Γ(T, ⊤) (LB.Sec (tp L k)) _ _ _ (LB.invertible_sec_top (isLB_tp hL k)) =
      (@CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L) _ _ _ (LB.invertible_sec_top hL)) ^ k
  | 0 => by
    have := LB.invertible_sec_top (isLB_tp hL 0)
    rw [pow_zero, CommRing.Pic.mk_eq_one_iff_free, ← LB.exists_isGen_iff_free_top (isLB_tp hL 0),
      ← CechPic.cls_eq_zero_iff (isLB_tp hL 0)]
    rfl
  | k + 1 => by
    have := LB.invertible_sec_top hL
    have := LB.invertible_sec_top (isLB_tp hL k)
    have : Module.Invertible Γ(T, ⊤) (LB.Sec (CechPic.tens L (tp L k))) :=
      LB.invertible_sec_top (CechPic.isLB_tens hL (isLB_tp hL k))
    rw [pow_succ', ← mk_tp hL k, ← CommRing.Pic.mk_tensor]
    exact (CommRing.Pic.mk_eq_mk_iff.2 (tensSec T L (tp L k) hL (isLB_tp hL k))).symm

theorem main : ∀ (T : Scheme.{0}) [IsAffine T] [AlgebraicGeometry.IsReduced T], Module.Finite ℤ Γ(T, ⊤) →
    ∀ L : LB T, L.IsLB → ∃ (n : ℕ) (s : (lbPow L n).Sec), 1 ≤ n ∧ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ := by
  intro T _ _ hfin L hL
  have := LB.invertible_sec_top hL
  obtain ⟨n, hn, hpow⟩ := (_root_.GlobalTheory.PicReducedTors.pic_isOfFinOrder Γ(T, ⊤) (CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L))).exists_pow_eq_one
  have hk := isLB_tp hL n
  have := LB.invertible_sec_top hk
  have h1 : CechPic.cls (tp L n) hk = 0 := by
    rw [CechPic.cls_eq_zero_iff hk, LB.exists_isGen_iff_free_top hk, ← CommRing.Pic.mk_eq_one_iff_free, mk_tp hL n,
      hpow]
  have hP : (lbPow L n).IsLB := LB.isLB_linComb hL _ _
  have h2 : CechPic.cls (lbPow L n) hP = 0 := by rw [CechPic.cls_lbPow hL n hP, ← cls_tp hL n, h1]
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hP).1 h2
  refine ⟨n, DVR.genSec t ht, hn, top_unique fun x _ => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hP.cover.ge (Opens.mem_top x))
  refine Opens.mem_iSup.2 ⟨i, ?_⟩
  change x ∈ T.basicOpen ((t.s i : Γ(T, (lbPow L n).U i)))
  rw [Scheme.basicOpen_of_isUnit _ (t.s i).isUnit]
  exact hi

end GlobalTheory.PowNowhereZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ θ₀
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.Mum.exists_intFam_mul R hR D m hm F₁
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_multiplicationPullback_genericSection_cover R hR D C m hm θ₀
  exact ⟨G, S, _root_.GlobalTheory.Mum.mulFam_exists_ne_zero R hR D m hm F₁ G hG,
    fun W _ _ _ T a b ha h => _root_.GlobalTheory.Mum.exp_mulPull_trait R hR D C m hm F₁ G θ₀ S hG hS W T a b ha h⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValReduction

theorem reduction_points : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u
  obtain ⟨e, he⟩ := GlobalTheory.ValPts.points_generic_mulEquiv U Ω S G hA.proper u
  let Vk : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G) :=
    MonoidHom.mk' (Vk ≫ ·) fun x y => MonObj.comp_mul Vk x y
  have hφ : ∀ P, (φ P).left = spMap h ≫ P.left := fun P => rfl
  have hes : ∀ (P : Over.mk u ⟶ G) y, y.left = spMap (algebraMap U Ω) ≫ P.left → e.symm y = P := by
    intro P y hy
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hy.trans (he P).symm)
  have hey : ∀ y, y.left = spMap (algebraMap U Ω) ≫ (e.symm y).left := fun y => by
    rw [← he]; simp
  refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro P y y₀ hy hy₀
    apply Over.OverMorphism.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hes P y hy, hφ, hy₀]
  · intro f y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : e.symm (y ≫ f) = e.symm y ≫ f := hes _ _ (by
      rw [Over.comp_left, hey y, Category.assoc, Over.comp_left])
    rw [this]
    exact (Category.assoc Vk (e.symm y) f).symm
  · intro n hn
    refine ⟨fun y (hy : y ^ n = 1) => (show _ ^ n = 1 by rw [← map_pow, hy, map_one]), ?_, ?_⟩
    · intro y (hy : y ^ n = 1) y' (hy' : y' ^ n = 1) hyy
      have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
      obtain ⟨Q, -, hQ⟩ := _root_.GlobalTheory.TorsionLiftVal.torsion_lift_unique U Ω k h S G hA u n hn
        ((φ.comp e.symm.toMonoidHom) y) (by rw [← map_pow, hy, map_one])
      have h1 := hQ (e.symm y) ⟨hP, rfl⟩
      have h2 := hQ (e.symm y') ⟨hP', by rw [hyy]; rfl⟩
      exact e.symm.injective (h1.trans h2.symm)
    · intro y₀ (hy₀ : y₀ ^ n = 1)
      obtain ⟨P, ⟨hP, hPy⟩, -⟩ := _root_.GlobalTheory.TorsionLiftVal.torsion_lift_unique U Ω k h S G hA u n hn y₀ hy₀
      refine ⟨e P, (show e P ^ n = 1 by rw [← map_pow, hP, map_one]), ?_⟩
      apply Over.OverMorphism.ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hφ, hPy]
  · intro Lb hLb n hn y y' c hy hy' H
    have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
    have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    exact GlobalTheory.WeilSpecialise.weilIs_specialise U Ω S G hA Lb hLb u n hn (e.symm y) (e.symm y') c hP hP' y y'
      (hey y) (hey y') H k h _ _ rfl rfl

end GlobalTheory.ValReduction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinementTautologicalChartFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.taut_refine : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  intro o _ ζ g n φ hn C hCN
  obtain ⟨hmono, -, hcone, hdef, ht0⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ hn C
  have hsymm : ∀ i y z, ((n : ℤ) • C.δ i) y z = ((n : ℤ) • C.δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, mem_balForms_int.1 (hcone.mem i) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • C.δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hcone.nonneg i y)
  have hdef' : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • C.δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    refine ⟨i, ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hn) hi
  obtain ⟨R', _, _, _, ρ, -, D, e, hCN', hinj, hfin, hloc, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun i => (n : ℤ) • C.δ i) hCN hmono C.bd ht0 hsymm hnn hdef'
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, D, e, hCN', hinj, hfin, hloc, href⟩
end

