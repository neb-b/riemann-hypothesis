module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairs
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacTriv

theorem one_suppSplit {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_suppInert {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_intG {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.IntG D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro i j
  simp only [inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨one_mem _, one_mem _⟩
  · exact ⟨zero_mem _, zero_mem _⟩

theorem vacuum_const_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hW hInp t0 ht0 hev hodd hχS hχT f₀ hf₀ hline hmul hsplit hinert
  subst hS
  subst hT
  have hnz : ∀ x y, W.Om x y e0 ≠ 0 := _root_.GlobalTheory.NormExact.om_normalising_ne_zero cc δ t0 e0 W hset.crv hodd
  have huniq : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T) (c c' : ℂ),
      Reads ψ θ rfl rfl cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r (c' • W.Om x y e0) (om (g, h) f₀) → c = c' :=
    fun x y g h c c' h1 h2 => _root_.GlobalTheory.NormExact.reads_smul_const_unique ψ θ S T rfl rfl cc δ r hset _ _ c c' (hnz x y) h1 h2
  have hone : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T),
      Reads ψ θ rfl rfl cc δ r (W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r ((1 : ℂ) • W.Om x y e0) (om (g, h) f₀) := fun x y g h hr => by rwa [one_smul]
  have p1S : IsFinPt S (1 : GA D S) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) := _root_.GlobalTheory.BotFormula.isFinPt_one S rfl
  have p1T : IsFinPt T (1 : GA D T) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) := _root_.GlobalTheory.BotFormula.isFinPt_one T rfl
  have exS : ∀ x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank, ∃ g, IsFinPt S g x :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one S hset.gS x rfl
  have exT : ∀ y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank, ∃ h, IsFinPt T h y :=
    fun y => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one T hset.gT y rfl
  choose gx hgx using exS
  choose hy hhy using exT
  have gx1 : gx 1 = 1 := _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt S _ _ 1 (hgx 1) p1S
  have hy1 : hy 1 = 1 := _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt T _ _ 1 (hhy 1) p1T
  have gxm : ∀ x₁ x₂, gx x₁ * gx x₂ = gx (x₁ * x₂) :=
    fun x₁ x₂ => _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt S _ _ _ (_root_.GlobalTheory.FinPtMul.isFinPt_mul S _ _ _ _ (hgx x₁) (hgx x₂)) (hgx (x₁ * x₂))
  have hym : ∀ y₁ y₂, hy y₁ * hy y₂ = hy (y₁ * y₂) :=
    fun y₁ y₂ => _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt T _ _ _ (_root_.GlobalTheory.FinPtMul.isFinPt_mul T _ _ _ _ (hhy y₁) (hhy y₂)) (hhy (y₁ * y₂))
  choose cS hcS using fun x => hline x 1 (gx x) 1 (hgx x) p1T
  choose cT hcT using fun y => hline 1 y 1 (hy y) p1S (hhy y)

  have cS1 : cS 1 = 1 := by
    have h1 := hcS 1
    rw [gx1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cSm : ∀ x₁ x₂, cS (x₁ * x₂) = cS x₁ * cS x₂ := by
    intro x₁ x₂
    have h1 := hmul x₁ 1 (gx x₁) 1 x₂ 1 (gx x₂) 1 (cS x₁) (cS x₂) (hgx _) p1T (hgx _) p1T (hcS x₁) (hcS x₂)
    rw [mul_one, mul_one, gxm] at h1
    exact huniq _ _ _ _ _ _ (hcS (x₁ * x₂)) h1
  have cT1 : cT 1 = 1 := by
    have h1 := hcT 1
    rw [hy1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cTm : ∀ y₁ y₂, cT (y₁ * y₂) = cT y₁ * cT y₂ := by
    intro y₁ y₂
    have h1 := hmul 1 y₁ 1 (hy y₁) 1 y₂ 1 (hy y₂) (cT y₁) (cT y₂) p1S (hhy _) p1S (hhy _) (hcT y₁) (hcT y₂)
    rw [mul_one, mul_one, hym] at h1
    exact huniq _ _ _ _ _ _ (hcT (y₁ * y₂)) h1
  let νS : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank →* ℂ := { toFun := cS, map_one' := cS1, map_mul' := cSm }
  let νT : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank →* ℂ := { toFun := cT, map_one' := cT1, map_mul' := cTm }
  have tS : ∀ x, cS x = 1 := by
    intro x
    have := _root_.GlobalTheory.InertSuppChar.char_eq_one S hset.gS νS.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hsplit k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppSplit)))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hinert k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppInert)
          hki (by simpa using one_intG))))) x
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  have tT : ∀ y, cT y = 1 := by
    intro y
    have := _root_.GlobalTheory.InertSuppChar.char_eq_one T hset.gT νT.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hsplit 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppSplit) hk))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hinert 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppInert) hk
          (by simpa using one_intG) hki)))) y
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  intro x y g h hg hh
  have eg : g = gx x := _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt S _ _ x hg (hgx x)
  have eh : h = hy y := _root_.GlobalTheory.FinPtUnique.eq_of_isFinPt T _ _ y hh (hhy y)
  subst eg eh
  have h1 := hmul x 1 (gx x) 1 1 y 1 (hy y) (cS x) (cT y) (hgx x) p1T p1S (hhy y) (hcS x) (hcT y)
  rw [tS, tT] at h1
  simp only [mul_one, one_mul, one_smul] at h1
  exact h1

end GlobalTheory.VacTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Desc.OpenChart

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x ∧
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨hx, ?_, ?_⟩
  · rw [hψ]
    exact GlobalTheory.TorRef.isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

theorem nonempty_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  intro E _ _ _ H Dw l Xo c S j _ A _ hA x hx
  obtain ⟨x', rfl⟩ := hx
  haveI : Smooth Xo.s := by haveI := Xo.smooth; exact SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI hreg : IsRegularLocalRing ((Xo.XF c).presheaf.stalk x') :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  obtain ⟨hcen, hEt, hres⟩ := completedStalk_chart (Xo.XF c) x'
  obtain ⟨ιF⟩ := GlobalTheory.GenFan.exists_ringHom_stalk c.F (Xo.XF c)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  set St := (Xo.XF c).presheaf.stalk x'
  set R := AdicCompletion (maximalIdeal St) St
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion St
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  let g : Sp R ⟶ Xo.XF c := GlobalTheory.fromSpecCompletedStalk (Xo.XF c) x'
  have hcz : CharZero R := (RingHom.charZero_iff ((algebraMap St R).comp ιF).injective).1 inferInstance
  have hb : Function.Bijective (j.stalkMap (g (closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨{
    R := R
    complete := inferInstance
    charZero := hcz
    ξ := g ≫ j
    centre := by
      show j (g (closedPoint R)) = j x'
      rw [hcen]
    etc := GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ j R g hEt
    unr := by
      apply RingHom.FormallyUnramified.of_surjective
      rw [Scheme.stalkClosedPointTo_comp]
      exact hres.comp hb.2
    G := (Over.pullback g).obj A
    semi := IsSemiAbelian.pullback (f := g) A hA
    y := jK R ≫ g
    hy := Category.assoc _ _ _
    α := pullback.fst ((Over.pullback g).obj A).hom (jK R) ≫ pullback.fst A.hom g
    gen := IsGrpPullback.comp (isGrpPullback_pullback _ (jK R)) (isGrpPullback_pullback A g) }⟩

end GlobalTheory.Desc.OpenChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftAction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

theorem DivOrder.mul_comm_of_eq_int {O : Type} [Ring O] {x y : O} {c : ℤ}
    (htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a))
    (hxy : x * y = (c : O))
    (hy : ∀ y : O, y ≠ 0 → ∃ w : O, ∃ c' : ℤ, c' ≠ 0 ∧ y * w = (c' : O)) :
    y * x = (c : O) := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [mul_zero] at hxy
    rw [zero_mul, hxy]
  obtain ⟨w, c', hc', hyw⟩ := hy y hy0
  have h1 : (c : O) * w = (c' : O) * x := by
    have : x * (y * w) = (x * y) * w := (_root_.mul_assoc _ _ _).symm
    rw [hyw, hxy, ← Int.cast_comm] at this
    exact this.symm
  have h2 : (c' : O) * (y * x) = (c' : O) * (c : O) := by
    calc (c' : O) * (y * x) = y * ((c' : O) * x) := (Int.cast_commute c' y).left_comm x
      _ = y * ((c : O) * w) := by rw [h1]
      _ = (c : O) * (y * w) := ((Int.cast_commute c y).left_comm w).symm
      _ = (c' : O) * (c : O) := by rw [hyw, Int.cast_comm]
  have h3 : c' • (y * x) = c' • (c : O) := by
    simpa [zsmul_eq_mul] using h2
  exact htf c' hc' h3

theorem DivOrder.exists_zsmul_eq_tmul (O : Type) [Ring O] (z : ℚ ⊗[ℤ] O) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : O, n • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨(q.den : ℤ), by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [zsmul_eq_mul, zsmul_eq_mul, _root_.mul_one]
    push_cast
    exact Rat.den_mul_eq_num q
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, hn₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, n₂ • x₁ + n₁ • x₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, e₁, mul_comm, mul_smul, e₂, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem DivOrder.isUnit_of_ne_zero (O : Type) [Ring O] [Module.Free ℤ O]
    (hdiv : ∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O))
    (z : ℚ ⊗[ℤ] O) (hz : z ≠ 0) : IsUnit z := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a) := by
    intro n hn a b hab
    apply hinj
    have h' : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] a) = (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] b) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_smul]
      exact congrArg _ hab
    exact smul_right_injective _ (by exact_mod_cast hn : (n : ℚ) ≠ 0) h'
  obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, ← Int.cast_smul_eq_zsmul ℚ] at e
    exact hz ((smul_eq_zero.mp e).resolve_left (by exact_mod_cast hn))
  obtain ⟨y, c, hc, hxy⟩ := hdiv x hx
  have hyx : y * x = (c : O) := DivOrder.mul_comm_of_eq_int htf hxy hdiv
  set jj : O →ₐ[ℤ] ℚ ⊗[ℤ] O := Algebra.TensorProduct.includeRight with hjj
  have hjx : IsUnit (jj x) := by
    rw [isUnit_iff_exists]
    refine ⟨algebraMap ℚ _ ((c : ℚ)⁻¹) * jj y, ?_, ?_⟩
    · rw [Algebra.left_comm, ← map_mul, hxy, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
    · rw [_root_.mul_assoc, ← map_mul, hyx, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
  have hz' : z = algebraMap ℚ _ ((n : ℚ)⁻¹) * jj x := by
    have : jj x = (1 : ℚ) ⊗ₜ[ℤ] x := rfl
    rw [← Algebra.smul_def, this, ← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [hz']
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hn))).map _).mul hjx

theorem potModel_of_intDivOrder_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hsm O _ _ _ act hmon h1 hmul hadd hdiv hg
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have hspan : Submodule.span ℚ (Set.range
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
    have hz : z = ((n : ℚ)⁻¹) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      rw [← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hrank : Module.finrank ℚ (ℚ ⊗[ℤ] O) = Module.finrank ℤ O := Module.finrank_baseChange
  exact _root_.GlobalTheory.potModel_of_divAlg_leftAction V K A g hA hsm O act hmon h1 hmul hadd (ℚ ⊗[ℤ] O)
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom
    (DivOrder.isUnit_of_ne_zero O hdiv) hinj hspan (hrank ▸ hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrimExt

theorem refl_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_of_range_subset {X Y Y' : Scheme.{0}} (e : Y ⟶ X) [IsOpenImmersion e] (f : Y' ⟶ X)
    (hf : Set.range f.base ⊆ Set.range e.base) (L M : LB X) (h : LBIso (L.pull e) (M.pull e)) :
    LBIso (L.pull f) (M.pull f) := by
  have hc : f = IsOpenImmersion.lift e f hf ≫ e := (IsOpenImmersion.lift_fac e f hf).symm
  exact LBIso.chartPull (chartPullSame L _ _ _ _ fun _ => hc) (chartPullSame M _ _ _ _ fun _ => hc) h

theorem prim_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (tF : SAB H S') (G : Over S) [GrpObj G] [IsCommMonObj G] (j : S' ⟶ S) (e : tF.G.left ⟶ G.left)
    (he : IsGrpPullback tF.G G j e) (act : OAct (𝓞 E) G)
    (hact : ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) (PP : RigLB G)
    (hw : LBIso tF.PP.L (PP.L.pull e)) :
    LBIso (PP.L.pull e) ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) := by
  have hP : (PP.L.pull e).IsLB := pull_isLB PP.isLB e
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  let U := pushPt he.1.w (𝟙 tF.G)
  have hU : U.left = e := by simp [U, pushPt]
  have hc : ∀ I : ULift.{0} (Finset (Fin 2)),
      (psum tF.G ![𝟙 tF.G, tF.act.act H.w0] I.down).left ≫ e = e ≫ (psum G ![𝟙 G, act.act H.w0] I.down).left :=
    fun I => (psum_push he ![𝟙 tF.G, tF.act.act H.w0] ![𝟙 G, act.act H.w0] U (fun i => by
      fin_cases i
      · apply Over.OverMorphism.ext
        simp [U, pushPt]
      · apply Over.OverMorphism.ext
        simp [U, pushPt, hact]) I.down).trans (by rw [hU])
  have h4 : LBIso (cubeLB tF.G ![𝟙 tF.G, tF.act.act H.w0] (PP.L.pull e))
      ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) :=
    LBIso.chartPull (chartPullLinComb PP.L e _ _ _ e hc) (chartPullPull _ e) (refl_of_isLB hC)
  refine LBIso.trans hP tF.PP.isLB (pull_isLB hC e) hw.symm ?_
  refine LBIso.trans tF.PP.isLB (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (pull_isLB hC e) tF.prim ?_
  exact LBIso.trans (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (GlobalTheory.SabPullCompare.cubeLB_isLB _ hP)
    (pull_isLB hC e) (GlobalTheory.SabPullCompare.lbIso_cubeLB _ hw) h4

theorem lbIso_prim_ext : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hUP _ tF _ G _ _ e hG he _ act hact PP cub cm hF _ hlin
  obtain ⟨-, -, -, -, ⟨⟨hS, -⟩, hproj, -, hdense, -⟩, -⟩ := hUP
  have : IsLocallyNoetherian S := by
    obtain ⟨N', im, _, h⟩ := hproj
    have : LocallyOfFiniteType (π ≫ zs) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := by haveI := hS; exact GlobalTheory.IsNormalScheme.pred S
  have hw : LBIso tF.PP.L (PP.L.pull e) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact hF ▸ ⟨w, hw⟩
  have : IsOpenImmersion e := MorphismProperty.of_isPullback he.1.flip inferInstance
  have hr : Set.range e.base = G.hom.base ⁻¹' Set.range j.base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show (e ≫ G.hom) y ∈ Set.range j
      rw [he.1.w]
      exact ⟨_, rfl⟩
    · intro hx
      have hx' : x ∈ Set.range (pullback.fst G.hom j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      obtain ⟨z, rfl⟩ := hx'
      refine ⟨he.1.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he.1.isoPullback_inv_fst]
  haveI := act.hom H.w0
  haveI := hG.smooth
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  let V : S.Opens := j.opensRange
  haveI : IsDominant V.ι := ⟨by
    show Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    simpa [V] using hdense⟩
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  have hsec : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  have hrig : CechPic.pull (eSec G) (CechPic.cls PP.L PP.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  refine (CechPic.cls_eq_iff PP.isLB hC).1 (GlobalTheory.ZH.EndoExtend.pic_ext V.ι hS' G (eSec G) hsec ?_ ?_)
  · rw [hrig, GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ PP.isLB]
    have hp := GlobalTheory.ZH.EndoExtend.pull_cubeCls G ![𝟙 G, act.act H.w0]
      (fun _ : Fin 2 => (η[G] : 𝟙_ (Over S) ⟶ G)) η[G]
      (fun i => by
        fin_cases i
        · simp
        · simp [IsMonHom.one_hom]) (CechPic.cls PP.L PP.isLB)
    exact (GlobalTheory.ZH.EndoExtend.cubeCls_one G _ hrig).symm.trans hp.symm
  · refine (CechPic.cls_eq_iff (pull_isLB PP.isLB _) (pull_isLB hC _)).2 ?_
    refine lbIso_pull_of_range_subset e _ ?_ _ _ (prim_pull tF G j e he act hact PP hw)
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    rfl

end GlobalTheory.PrimExt
end
end

