module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0114
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTests
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S H : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {AH BH : Over H} [GrpObj AH] [GrpObj BH]

def IsSol (π : H ⟶ S) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH) {T : Scheme.{0}} (t : T ⟶ S)
    (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (h : T ⟶ H) : Prop :=
  h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
    IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

def IsRestr {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    {A'' B'' : Over U} [GrpObj A''] [GrpObj B''] (Φ'' : A'' ⟶ B'') (ρA : A''.left ⟶ A'.left)
    (ρB : B''.left ⟶ B'.left) : Prop :=
  IsGrpPullback A'' A' g ρA ∧ IsGrpPullback B'' B' g ρB ∧ Φ''.left ≫ ρB = ρA ≫ Φ'.left

variable {π : H ⟶ S} {φA : AH.left ⟶ A.left} {φB : BH.left ⟶ B.left} {Φ : AH ⟶ BH}

theorem isRestr_pullback {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B') :
    IsRestr g Φ' ((Over.pullback g).map Φ') (pullback.fst A'.hom g) (pullback.fst B'.hom g) :=
  ⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩

theorem IsSol.restr {T U : Scheme.{0}} {t : T ⟶ S} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {h : T ⟶ H}
    (hs : IsSol π φA φB Φ t A' B' φA' φB' Φ' h) {g : U ⟶ T} {A'' B'' : Over U} [GrpObj A''] [GrpObj B'']
    {Φ'' : A'' ⟶ B''} {ρA : A''.left ⟶ A'.left} {ρB : B''.left ⟶ B'.left} (hr : IsRestr g Φ' Φ'' ρA ρB) :
    IsSol π φA φB Φ (g ≫ t) A'' B'' (ρA ≫ φA') (ρB ≫ φB') Φ'' (g ≫ h) := by
  obtain ⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs
  obtain ⟨rA, rB, rΦ⟩ := hr
  refine ⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA],
    by rw [Category.assoc, eB], ?_⟩
  rw [← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]

theorem IsRestr.factor {T U W : Scheme.{0}} {f : U ⟶ T} {k : W ⟶ U} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα] {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left}
    {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {AW BW : Over W} [GrpObj AW] [GrpObj BW]
    {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left} (hW : IsRestr (k ≫ f) Φ' ΦW ρAW ρBW) :
    ∃ (σA : AW.left ⟶ Aα.left) (σB : BW.left ⟶ Bα.left), IsRestr k Φα ΦW σA σB ∧ σA ≫ ρAα = ρAW ∧
      σB ≫ ρBα = ρBW := by
  obtain ⟨aα, bα, cα⟩ := hα
  obtain ⟨aW, bW, cW⟩ := hW
  have wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f := by rw [aW.1.w, Category.assoc]
  have wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f := by rw [bW.1.w, Category.assoc]
  refine ⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm)
    (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩,
    aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩
  apply bα.1.hom_ext
  · rw [Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]
  · rw [Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]

theorem IsSol.pull {T U W : Scheme.{0}} {t : T ⟶ S} {f : U ⟶ T} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα]
    {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left} {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {hα' : U ⟶ H}
    (hs : IsSol π φA φB Φ (f ≫ t) Aα Bα (ρAα ≫ φA') (ρBα ≫ φB') Φα hα') (k : W ⟶ U) {g : W ⟶ T} (hg : g = k ≫ f)
    {AW BW : Over W} [GrpObj AW] [GrpObj BW] {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left}
    (hW : IsRestr g Φ' ΦW ρAW ρBW) : IsSol π φA φB Φ (g ≫ t) AW BW (ρAW ≫ φA') (ρBW ≫ φB') ΦW (k ≫ hα') := by
  subst hg
  obtain ⟨σA, σB, hr, eA, eB⟩ := hα.factor hW
  have := hs.restr hr
  rw [← eA, ← eB]
  simp only [Category.assoc] at this ⊢
  exact this

theorem isSol_of_local (pbA : IsGrpPullback AH A π φA) (pbB : IsGrpPullback BH B π φB) {T : Scheme.{0}} {t : T ⟶ S}
    {A' B' : Over T} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'}
    (hA : IsGrpPullback A' A t φA') (hB : IsGrpPullback B' B t φB') {h : T ⟶ H} (hh : h ≫ π = t) {Idx : Type}
    {U : Idx → Scheme.{0}} (f : ∀ i, U i ⟶ T) (Aα Bα : ∀ i, Over (U i)) [∀ i, GrpObj (Aα i)] [∀ i, GrpObj (Bα i)]
    (Φα : ∀ i, Aα i ⟶ Bα i) (ρA : ∀ i, (Aα i).left ⟶ A'.left) (ρB : ∀ i, (Bα i).left ⟶ B'.left)
    (hr : ∀ i, IsRestr (f i) Φ' (Φα i) (ρA i) (ρB i))
    (hs : ∀ i, IsSol π φA φB Φ (f i ≫ t) (Aα i) (Bα i) (ρA i ≫ φA') (ρB i ≫ φB') (Φα i) (f i ≫ h))
    (hepi : ∀ (u v : A'.left ⟶ BH.left), (∀ i, ρA i ≫ u = ρA i ≫ v) → u = v) :
    IsSol π φA φB Φ t A' B' φA' φB' Φ' h := by
  have wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π := by rw [hA.1.w, Category.assoc, hh]
  have wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π := by rw [hB.1.w, Category.assoc, hh]
  refine ⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB,
    pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA),
    pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB),
    pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩
  obtain ⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs i
  obtain ⟨rA, rB, rΦ⟩ := hr i
  have hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA := pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst])
    (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])
  have hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB := pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst])
    (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])
  rw [← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]

theorem lbIso_restr {XA XB A'l B'l A''l B''l : Scheme.{0}} {L : LB XA} {M : LB XB} (hL : L.IsLB) (hM : M.IsLB)
    {φA' : A'l ⟶ XA} {φB' : B'l ⟶ XB} {Φl : A'l ⟶ B'l} {ρA : A''l ⟶ A'l} {ρB : B''l ⟶ B'l} {Φ''l : A''l ⟶ B''l}
    (e : Φ''l ≫ ρB = ρA ≫ Φl) (iso : LBIso (L.pull φA') ((M.pull φB').pull Φl)) :
    LBIso (L.pull (ρA ≫ φA')) ((M.pull (ρB ≫ φB')).pull Φ''l) := by
  have hN := pull_isLB hM φB'
  have i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso
  have i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl
  have i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l
  exact LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1
    (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)

theorem rep_of_affine : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso
  have key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t)
      ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB')
      ((Over.pullback f).map Φ') k := fun R _ f =>
    haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ')
      ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance
      (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)
  let 𝒜 := T.affineOpenCover
  let 𝒰 := 𝒜.openCover
  have hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A')
      ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB')
      ((Over.pullback (𝒰.f i)).map Φ') k := fun i => key (𝒜.X i) (𝒰.f i)
  choose k hk hku using hloc
  have hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    intro i j
    let 𝒲 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun l => ?_
    let g : Sp (𝒲.X l) ⟶ T := (𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i
    have hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hu := key (𝒲.X l) g
    rw [← Category.assoc, ← Category.assoc]
    exact hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ'))
      (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))
  let hg := 𝒰.glueMorphisms k hagree
  have hι : ∀ i, 𝒰.f i ≫ hg = k i := 𝒰.ι_glueMorphisms k hagree
  have hh : hg ≫ π = t := 𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1
  have hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg :=
    isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A')
      (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ')
      (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i))
      (fun i => isRestr_pullback _ Φ') (fun i => by rw [hι]; exact hk i)
      (fun u v h => Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁ A'.hom 𝒰) u v h)
  refine ⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩
  rw [hι]
  exact hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))

end GlobalTheory.EndLoc.HomFixGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.AmpleTwistLB

theorem ample_pow_div : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  intro W S _ _ f A hA N M hN hM hcls hV
  have : CompactSpace S := hA.compactSpace
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow A n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hA.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨K, hK, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hAK := isLB_lbPow hA.isLB K
  have hG : ((lbPow A K).pull f).IsLB := LB.isLB_pull hAK f
  have hGgen : IsGenerated ((lbPow A K).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hMK := isLB_lbPow hM K
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hMK hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB ((M.pull (f ⁻¹ᵁ V z).ι).pull (W.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB (M.pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hM _) (GenSpread.lbIso_pull_pull hM _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hM _) hK).2 h₂).of_lbIso (LB.isLB_pull hMK _)
      (lbIso_lbPow_pull hM _ K).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hAf : (A.pull f).IsLB := LB.isLB_pull hA.isLB f
  have hD : (LB.div (lbPow (A.pull f) (c + k)) N).IsLB := LB.isLB_div (isLB_lbPow hAf (c + k)) hN
  refine (isAmpleLB_pow_iff hD hK).1 ?_
  have hT := AbLaw.isLB_tw hMK hG (c : ℤ)
  have hGk := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = K • CechPic.cls _ hAf := by
    rw [CechPic.cls_pull hAK f, CechPic.cls_lbPow hA.isLB, map_nsmul, ← CechPic.cls_pull hA.isLB f]
  have eT : CechPic.cls _ hT = CechPic.cls _ hMK + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hMK (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD K) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk, CechPic.cls_div (isLB_lbPow hD K) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hM, eG, CechPic.cls_div (isLB_lbPow hAf (c + k)) hN hD,
    CechPic.cls_lbPow hAf, hcls]
  module

end GlobalTheory.AmpleTwistLB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKTypeOfMap
section
namespace GlobalTheory.KTypeUnderMaps

open Formalism.MainNotions.S

theorem isKTypeOf_map {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (L : H →ₗ[ℂ] H)
    (hL : ∀ k ∈ Formalism.REAL.Kset ε, ∀ (w : H), σ k (L w) = L (σ k w))
    {v : H} (hv : v ∈ S) (hLv : L v ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (Submodule.map L S) := by
  obtain ⟨hfd, hst, hirr, ⟨u, huS, hu0, huw⟩, hdom⟩ := hS
  have hpull : ∀ T : Submodule ℂ H, IsKStableOn ε σ T →
      S ⊓ T.comap L = ⊥ ∨ S ⊓ T.comap L = S := by
    intro T hT
    refine hirr _ inf_le_left ?_
    intro g hg x hx
    refine ⟨hst g hg x hx.1, ?_⟩
    have h2 : L x ∈ T := hx.2
    change L (σ g x) ∈ T
    rw [← hL g hg]
    exact hT g hg _ h2
  have hinj : ∀ x ∈ S, L x = 0 → x = 0 := by
    intro x hx hx0
    have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
      intro g _ y hy
      rw [Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    rcases hpull ⊥ hbot with h | h
    · have : x ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := ⟨hx, by simpa using hx0⟩
      rw [h] at this
      simpa using this
    · have : v ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := by rw [h]; exact hv
      exact absurd (by simpa using this.2) hLv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    infer_instance
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, (hL g hg x).symm⟩
  · intro T hTle hT
    rcases hpull T hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hTle hy
      have : x ∈ S ⊓ T.comap L := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hTle ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ S ⊓ T.comap L := by rw [h]; exact hx
      exact this.2
  · refine ⟨L u, ⟨u, huS, rfl⟩, fun h => hu0 (hinj u huS h), ?_⟩
    intro θ hθ
    rw [hL _ hθ, huw θ hθ, map_smul]
  · rintro μ _ ⟨x, hx, rfl⟩ hx0 hw
    refine hdom μ x hx (fun h => hx0 (by rw [h, map_zero])) ?_
    intro θ hθ
    rw [← sub_eq_zero]
    refine hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) ?_
    rw [map_sub, map_smul, ← hL _ hθ, hw θ hθ, sub_self]

end GlobalTheory.KTypeUnderMaps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem exists_denom (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (h : {w | ¬ IntAt w (B w)}.Finite) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ w, IntAt w ((d : K) • B w) := by
  haveI : Finite {w | ¬ IntAt w (B w)} := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : {w | ¬ IntAt w (B w)} × ι × ι => B p.1.1 p.2.1 p.2.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun w i j => ?_⟩
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one (b : 𝓞 K)) (hw i j)
  · obtain ⟨r, hr⟩ := hb (⟨w, hw⟩, i, j)
    have : ((b : 𝓞 K) : K) • B w i j = algebraMap (𝓞 K) K r := by
      rw [hr]; simp [Algebra.smul_def]
    rw [Matrix.smul_apply, this]
    exact w.valuation_le_one r


omit [DecidableEq ι] in
theorem mulVec_le (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K} (hM : IntAt w M) {x : ι → K}
    (hx : ∀ j, w.valuation K (x j) ≤ 1) (i : ι) : w.valuation K ((M *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i j) (hx j)

theorem isLattice_locLat (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (hA : IsAdelic A) : Submodule.IsFullLattice K (locLat A) := by
  obtain ⟨hdet, hfin⟩ := hA
  obtain ⟨d, hd0, hd⟩ := exists_denom A (hfin.subset fun w hw h => hw h.1)
  obtain ⟨e, he0, he⟩ := exists_denom (fun w => (A w)⁻¹) (hfin.subset fun w hw h => hw h.2)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  have heK : (e : K) ≠ 0 := by simpa using he0
  have hLat : Submodule.IsLattice K (locLat A) := by
    constructor
    · let f : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → K) := (e : K)⁻¹ • (Algebra.linearMap (𝓞 K) K).compLeft ι
      have hf : (LinearMap.range f).FG := by
        rw [← Submodule.map_top]
        exact Submodule.FG.map _ Module.Finite.fg_top
      refine hf.of_le fun x hx => ?_
      have hint : ∀ i, (e : K) * x i ∈ (algebraMap (𝓞 K) K).range := fun i =>
        HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => by
          have h1 := mulVec_le w (he w) (hx w) i
          rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec,
            Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet w)), Matrix.one_mulVec] at h1
          exact h1
      choose y hy using hint
      refine ⟨y, funext fun i => ?_⟩
      change (e : K)⁻¹ * algebraMap (𝓞 K) K (y i) = x i
      rw [hy, inv_mul_cancel_left₀ heK]
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine { toIsLattice := hLat, span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change Pi.basisFun K ι i ∈ Submodule.span K (locLat A : Set (ι → K))
  have hm : (d : K) • Pi.basisFun K ι i ∈ locLat A := by
    intro w j
    have h := mulVec_le w (hd w) (x := Pi.basisFun K ι i) (by
      intro k
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp) j
    simpa only [Matrix.smul_mulVec, Matrix.mulVec_smul] using h
  have hm' := (Submodule.span K (locLat A : Set (ι → K))).smul_mem (d : K)⁻¹
    (Submodule.subset_span hm)
  simpa only [smul_smul, inv_mul_cancel₀ hdK, one_smul] using hm'

end GlobalTheory.LocMatLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKCompEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenFibre

theorem jK_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V)
    (hemb : ∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W →
      emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) :
    jK V ≫ ξ = spMap emb ≫ M.pt := by
  obtain ⟨W, hW, hξ, -⟩ := GlobalTheory.Points.exists_isAffineOpen_le ξ (GlobalTheory.Points.le_preimage_top ξ)
  have hz : ξ (IsLocalRing.closedPoint V) ∈ W := hξ (x := IsLocalRing.closedPoint V) trivial
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨_, hz⟩
  refine GlobalTheory.Points.ext_of_valR hW (GlobalTheory.Points.le_preimage_comp (V := ⊤) (jK V) ξ hξ le_rfl)
    (GlobalTheory.Points.le_preimage_comp (V := ⊤) (spMap emb) M.pt hpt le_rfl) fun f => ?_
  calc valR (jK V ≫ ξ) W f = algebraMap V (FractionRing V) (valR ξ W f) :=
        GlobalTheory.Points.valR_spMap_comp (algebraMap V (FractionRing V)) ξ W hξ f
    _ = emb (valF M.pt W f) := (hemb W f hz).symm
    _ = valR (spMap emb ≫ M.pt) W f := (GlobalTheory.Points.valR_spMap_comp emb M.pt W hpt f).symm

theorem genFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∀ [IsCommMonObj ((Over.pullback ξ).obj Zh.G)] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (IsLocalRing.maximalIdeal V) D A ((Over.pullback ξ).obj Zh.G)), LBIso U.LG.L (Zh.L.L.pull (pullback.fst Zh.G.hom ξ)) → ∀ (emb : Ω →+* FractionRing V), (∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W → emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) → ∃ φ : A.A.left ⟶ ρ.P.A.left, IsGrpPullback A.A ρ.P.A (spMap (emb.comp (algebraMap S.R Ω))) φ ∧ LBIso A.L (ρ.P.L.pull φ) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO V _ _ _ ξ _ _ D A U hLG emb hemb
  have e₁ := jK_comp_eq M ξ emb hemb
  have hpt : Set.range M.pt ⊆ (U₀ : Set M.Z) := fun _ ⟨w, hw⟩ => hw ▸ M.top_le_preimage_pt hO.ne (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hpt)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ Zh.u₀ = spMap S.R.val.toRingHom := Zh.u₀_gen x hx
  let y : Sp (FractionRing V) ⟶ U₀.toScheme := spMap emb ≫ x
  have e₂ : (𝟙 _ ≫ jK V) ≫ ξ = y ≫ U₀.ι := by
    rw [Category.id_comp, e₁, Category.assoc, hx]
  have e₃ : 𝟙 _ ≫ y ≫ Zh.u₀ = spMap (emb.comp (algebraMap S.R Ω)) := by
    rw [Category.id_comp, Category.assoc, hxu]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  have hA := ((isGrpPullback_of_iso U.gen.symm).comp
    (isGrpPullback_pullback ((Over.pullback ξ).obj Zh.G) (jK V))).comp (isGrpPullback_pullback Zh.G ξ)
  have hB := (isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp Zh.cart
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (hA.congr e₂ rfl) hB
  haveI := he
  have hC := (isGrpPullback_of_iso e).comp ((isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp
    (isGrpPullback_pullback ρ.P.A Zh.u₀))
  refine ⟨_, hC.congr e₃ rfl, ?_⟩
  have H1 := U.ext
  have H2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLG (pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V)) rfl
  have H3 := LBIso.trans (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB Zh.L.isLB _) H1 H2
  have H4 : LBIso (A.L.pull (𝟙 _)) (Zh.L.L.pull (U.gen.inv.left ≫
      pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫ pullback.fst Zh.G.hom ξ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp U.gen.inv.left
      (by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]) rfl H3
  have H5 := LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl) (chartPullId _) H4
  have H6 : LBIso (Zh.L.L.pull (U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫
      pullback.fst Zh.G.hom ξ)) (ρ.P.L.pull (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y ≫
      pullback.fst ρ.P.A.hom Zh.u₀)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y)
      (a := Zh.φ) (b := pullback.fst ρ.P.A.hom Zh.u₀) (by rw [Category.assoc, hφ, Category.assoc]; rfl)
      (Category.assoc _ _ _).symm ⟨Zh.w, Zh.w_gen⟩
  exact LBIso.trans A.isLB (pull_isLB Zh.L.isLB _) (pull_isLB ρ.P.isLB _) H5 H6

end GlobalTheory.GenFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasisStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannian_volume_lie_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → IsOrth X x → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm X.Gm (e i *ᵥ u) w + herm X.Gm u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie X.Ψ e := by
  first | exact @GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | exact GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | (intros; apply GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie <;> assumption)
end

