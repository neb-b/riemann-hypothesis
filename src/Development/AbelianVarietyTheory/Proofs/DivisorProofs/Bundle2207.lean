module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCoc

theorem alg {X U : Type} [AddCommGroup X] [CommGroup U] (F t P : X → X → U) (C : X → X → X → U) (ψ : X → U) (r : U)
    (hF : ∀ a b, P a b * F a b = t a b) (hP : ∀ a b, P a b = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹)
    (ht : ∀ a b, t a b = t b a) (hadd : ∀ a a' b, t (a + a') b * C a a' b = t a b * t a' b)
    (hC : ∀ a b c, C a b c = C b c a) :
    (∀ a b, F a b = F b a) ∧ ∀ a b c, F (a + b) c * F a b = F a (b + c) * F b c := by
  constructor
  · intro a b
    have comm : ψ (b + a) = ψ (a + b) := by rw [add_comm]
    have e₁ := congrArg Additive.ofMul (hF a b)
    have e₂ := congrArg Additive.ofMul (hF b a)
    have e₃ := congrArg Additive.ofMul (ht a b)
    have e₄ := congrArg Additive.ofMul (hP a b)
    have e₅ := congrArg Additive.ofMul (hP b a)
    have e₆ := congrArg Additive.ofMul comm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ e₆ ⊢
    linear_combination (norm := abel) e₁ - e₂ + e₃ - e₄ + e₅ + e₆
  · intro a b c
    have p₁ := hP (a + b) c
    rw [add_assoc] at p₁
    have e₁ := congrArg Additive.ofMul (hadd a b c)
    have e₂ := congrArg Additive.ofMul (hadd b c a)
    have s₁ := congrArg Additive.ofMul (ht a (b + c))
    have s₂ := congrArg Additive.ofMul (ht a b)
    have s₃ := congrArg Additive.ofMul (ht a c)
    have c₁ := congrArg Additive.ofMul (hC a b c)
    have f₁ := congrArg Additive.ofMul (hF (a + b) c)
    have f₂ := congrArg Additive.ofMul (hF a b)
    have f₃ := congrArg Additive.ofMul (hF a (b + c))
    have f₄ := congrArg Additive.ofMul (hF b c)
    have q₁ := congrArg Additive.ofMul p₁
    have q₂ := congrArg Additive.ofMul (hP a b)
    have q₃ := congrArg Additive.ofMul (hP a (b + c))
    have q₄ := congrArg Additive.ofMul (hP b c)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ s₁ s₂ s₃ c₁ f₁ f₂ f₃ f₄ q₁ q₂ q₃ q₄ ⊢
    linear_combination (norm := abel) e₁ - s₁ - e₂ + s₂ + s₃ - c₁ + f₁ + f₂ - f₃ - f₄ - q₁ - q₂ + q₃ + q₄

theorem exists_genPtMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

end GlobalTheory.PolDeg.SymCoc

namespace GlobalTheory.PolDeg


open GlobalTheory.PolDeg.SymCoc in
theorem half_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  intro R _ _ R' _ _ Q ρ D e f hρ hH
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₀, h₄, h₅⟩ := hH
  obtain ⟨κ, hκ⟩ : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := exists_genPtMap ρ hρ
  let z : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  let x : D.X → (TK R' ⟶ D.P.A) := fun a => toUnit (TK R') ≫ D.c a
  have hx : ∀ a a', x (a + a') = x a * x a' := fun a a' => by
    show toUnit (TK R') ≫ D.c (a + a') = _
    rw [D.c_add]
    exact MonObj.comp_mul _ _ _
  let ψ : D.X → ((TK R').left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J'
  let r : ((TK R').left.presheaf.stalk z)ˣ := val D.rigK (𝟙 _) z J'
  have hP : ∀ a b, val (D.tau a b) (𝟙 _) z J' = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hJ', val_mul hJ', val_mul hJ', val_inv, val_inv, val_inv]
  let laws := fun a a' b => GlobalTheory.LamRigid.lam_iso_laws (Sp R) (Sp R') Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub
    (spMap ρ) β β₂ w h₁ D.P.isAb h₂ h₃ h₀ (TK R') (x a) (x a') (x b) z J J' hJ hJ'
  let κo : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  let X : D.X → (TK R ⟶ Q.B) := fun a => toUnit (TK R) ≫ Q.c (e a)
  let y : D.X → (Over.mk ((TK R').hom ≫ spMap ρ) ⟶ Q.B) := fun a => κo ≫ X a
  have hy : ∀ a, (y a).left = (x a).left ≫ β := fun a => by
    simp only [y, X, x, κo, Over.comp_left, Over.homMk_left, Rosenlicht.toUnit_left, Over.mk_hom, Category.assoc]
    rw [h₄ a, ← Category.assoc κ, hκ, Category.assoc]
  have hq : ∀ a a' b, val (Q.tau (e (a + a')) (e b)) κ z J *
      @id ((TK R').left.presheaf.stalk z)ˣ (cubV Q.cub (T := Over.mk ((TK R').hom ≫ spMap ρ)) z J (y a) (y a') (y b)) =
      val (Q.tau (e a) (e b)) κ z J * val (Q.tau (e a') (e b)) κ z J := by
    intro a a' b
    have hc : LB.Gen.Corr Q.M.L _ _ _ _
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e a) (e b)) (Q.tau (e a') (e b))) :=
      corr_of_val Q.M.isLB fun y' J₀ hJ₀ => by
        have t₁ := Q.tau_add (e a) (e a') (e b) y' J₀ hJ₀
        rw [← map_add e a a'] at t₁
        refine (val_mul hJ₀ _ _ _).trans (Eq.trans ?_ (t₁.trans (val_mul hJ₀ _ _ _).symm))
        exact congrArg _ ((val_pull hJ₀ _ _ _).trans
          (congrArg (fun p => val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t p y' J₀) (Category.id_comp _)))
    calc _ = val (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left)) κ z J := by
          refine Eq.trans ?_ (val_mul hJ _ _ _).symm
          exact congrArg _ (val_cub Q.cub κo hJ (X a) (X a') (X b)).symm
      _ = _ := val_corr hJ hc κ
      _ = _ := val_mul hJ _ _ _
  have hqs : ∀ a b, val (Q.tau (e a) (e b)) κ z J = val (Q.tau (e b) (e a)) κ z J := fun a b =>
    val_corr hJ (corr_of_val Q.M.isLB fun y' J₀ hJ₀ => Q.tau_symm (e a) (e b) y' J₀ hJ₀) κ
  have hcub := isCub_cubV D.cub hJ'
  obtain ⟨hs, hc⟩ := alg (fun a b => gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)))
    (fun a b => lamVal w (lift (x a) (x b)).left z J J' * val (Q.tau (e a) (e b)) κ z J)
    (fun a b => val (D.tau a b) (𝟙 _) z J') (fun a a' b => cubV D.cub z J' (x a) (x a') (x b)) ψ r
    (fun a b => h₅ κ hκ a b z J J' hJ hJ') hP
    (fun a b => by
      beta_reduce
      rw [(laws a a b).1, hqs a b])
    (fun a a' b => by
      have e₁ := (laws a a' b).2 (y a) (y a') (y b) (hy a) (hy a') (hy b)
      rw [← hx] at e₁
      have e₂ := hq a a' b
      beta_reduce
      apply Additive.ofMul.injective
      have e₁' := congrArg Additive.ofMul e₁
      have e₂' := congrArg Additive.ofMul e₂
      simp only [ofMul_mul, id] at e₁' e₂' ⊢
      linear_combination (norm := abel) e₁' + e₂')
    (fun a b c => (hcub.s01 _ _ _).trans (hcub.s12 _ _ _))
  have inj : ∀ u v : (FractionRing R')ˣ, gm (𝟙 (TK R').left) z ⊤ (unitOn u) = gm (𝟙 (TK R').left) z ⊤ (unitOn v) →
      u = v := fun u v h =>
    ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (GlobalTheory.ArcData.unit_ext_field (𝟙 (Sp (FractionRing R'))) z fun _ => h)
  have hm : ∀ u v : (FractionRing R')ˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v =>
    map_mul (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))).inv.hom.toMonoidHom) u v
  refine ⟨fun a b => inj _ _ (hs a b), fun a b c => inj _ _ ?_⟩
  rw [hm, hm, map_mul, map_mul]
  exact hc a b c

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChange
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

end GlobalTheory.PolPartPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImage
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  intro k _ X Y _ _ p s _ E' E hO y hy f hf
  obtain ⟨a, rfl⟩ := hf
  refine (hO _).2 (hy _ ⟨s.stalkMap y a, ?_⟩)
  exact (GlobalTheory.functionFieldMap_algebraMap s y a).symm

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem prime_eq_of_natCast_eq_zero {K : Type*} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : K) = 0) (h2 : (q : K) = 0) : p = q := by
  have a := ringChar.dvd h1
  have b := ringChar.dvd h2
  have hne : ringChar K ≠ 1 := CharP.ringChar_ne_one
  have e1 := (hp.eq_one_or_self_of_dvd _ a).resolve_left hne
  have e2 := (hq.eq_one_or_self_of_dvd _ b).resolve_left hne
  rw [← e1, ← e2]

theorem natCast_residueField_cPt {X : Scheme.{0}} {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ((p : ℕ) : X.residueField (y (cPt p))) = 0 := by
  let φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of (OO p)) y).hom
  have hinj := (IsLocalRing.ResidueField.map φ).injective
  refine hinj ((map_natCast _ p).trans ?_)
  exact (natCast_residueField_OO (p := p)).trans (map_zero _).symm

theorem eq_zero_of_val_cen_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z) (b : Ω), b ∈ M.O (y₀ (cPt p)) → (∀ y : Sp (OO p) ⟶ M.Z, M.Cen U (y₀ (cPt p)) y → M.val (gPt p ≫ y) b = 0) → b = 0 := by
  intro o Ω _ _ _ hb M hN U hU p _ y₀ b hb0 hv
  by_contra hne
  obtain ⟨V, f, hzV, hf⟩ := hb0
  have hD : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : f = 0 := (basicOpen_eq_bot_iff f).1 (SetLike.coe_injective h)
    apply hne
    rw [← hf, ← M.res_apply V ⟨_, hzV⟩, h0, map_zero]
  have hW : ((U ⊓ M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf hU hD
  have := hb.ded
  have := hb.ft
  have := hb.char
  have : CharZero o := (RingHom.charZero_iff hb.inj).2 hb.char
  let π : M.Z ⟶ Spec (.of ℤ) := M.s ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom o))
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    refine Flat.SpecMap_iff.2 ?_
    have : FaithfulSMul ℤ o := inferInstance
    exact (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat π := inferInstance
  have := M.lft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := ℤ) (B := o)).2 hb.ft
  have : LocallyOfFiniteType π := inferInstance
  have hz : IsClosed ({y₀ (cPt p)} : Set M.Z) := isClosed_singleton_cPt y₀
  obtain ⟨p', hp', y, hy, hyW⟩ := GlobalTheory.padicAlgCl_integral_points.1 M.Z π (y₀ (cPt p)) hz _ hW
  have e : p = p' := prime_eq_of_natCast_eq_zero (Fact.out) hp'.out (natCast_residueField_cPt y₀)
    (hy ▸ natCast_residueField_cPt y)
  subst e
  have h0 := hv y ⟨hy, hyW.trans (fun _ h => h.1)⟩
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hξ : (gPt p ≫ y) w ∈ M.Z.basicOpen f := (hyW ⟨w, rfl⟩).2
  have hξV : (gPt p ≫ y) w ∈ V := M.Z.basicOpen_le f hξ
  subst hf
  exact (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w) ⟨_, RatModel.valF_mem_O hξV f⟩).2
    ((RatModel.isUnit_valF_iff hξV f).2 hξ) h0

end GlobalTheory.Poinc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOfRingOnEqNonunitsAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Poinc

theorem prime_eq_nonunits_at_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ P : Ideal (M.ringOn (U : Set M.Z)), P.IsPrime →
      ∃ z ∈ U, ∀ a : M.ringOn (U : Set M.Z), a ∈ P ↔ ((a : Ω) = 0 ∨ (a : Ω)⁻¹ ∉ M.O z) := by
  intro o Ω _ _ _ M U hU hne P hP
  let e := M.sectionsEquiv U hne
  let P' : Ideal Γ(M.Z, U) := P.comap (e : Γ(M.Z, U) →+* M.ringOn (U : Set M.Z))
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  let x : Spec Γ(M.Z, U) := (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hz : hU.fromSpec x ∈ U := by
    have h := hU.range_fromSpec
    exact h.subset ⟨x, rfl⟩
  refine ⟨hU.fromSpec x, hz, fun a => ?_⟩
  obtain ⟨f, rfl⟩ := e.surjective a
  have key : hU.fromSpec x ∈ M.Z.basicOpen f ↔ f ∉ P' := by
    have h := hU.fromSpec_preimage_basicOpen f
    have h2 : x ∈ hU.fromSpec ⁻¹ᵁ M.Z.basicOpen f ↔ hU.fromSpec x ∈ M.Z.basicOpen f := Iff.rfl
    rw [← h2, h]
    exact PrimeSpectrum.mem_basicOpen f (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hu := isUnit_valF_iff hz f
  rw [isUnit_O_iff] at hu
  have hmem : e f ∈ P ↔ f ∈ P' := Iff.rfl
  rw [hmem, coe_sectionsEquiv, ← not_iff_not, ← key, ← hu]
  simp only [not_or, not_not]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer.PmapTwo

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft_left (W : Over S) {G B : Over S} (p : G ⟶ B) :
    IsPullback (W ◁ p).left (snd W G).left (snd W B).left p.left := by
  have h1 : IsPullback (fst W B).left (snd W B).left W.hom B.hom := IsPullback.of_hasPullback W.hom B.hom
  have h2 : IsPullback (fst W G).left (snd W G).left W.hom G.hom := IsPullback.of_hasPullback W.hom G.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight_left {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (p ▷ W).left (fst G W).left (fst B W).left p.left := by
  have h1 : IsPullback (snd B W).left (fst B W).left W.hom B.hom :=
    (IsPullback.of_hasPullback B.hom W.hom).flip
  have h2 : IsPullback (snd G W).left (fst G W).left W.hom G.hom := (IsPullback.of_hasPullback G.hom W.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem prodMapPairTimesIdentity_eq_comp_whiskers {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    pmap2 q T = (q ▷ (A ⊗ T)) ≫ (A' ◁ (q ▷ T)) := by
  ext <;> simp [pmap2, pmap]

end GlobalTheory.CharKer.PmapTwo


open GlobalTheory.CharKer.PmapTwo in
theorem GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom :
    ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left →
      Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  intro S A A' T q h1 h2 h3
  have hR := (isPullback_whiskerRight_left q (A ⊗ T)).flip
  have hL := (isPullback_whiskerLeft_left A' (q ▷ T)).flip
  have hR' := (isPullback_whiskerRight_left q T).flip
  have a1 : Flat (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h1
  have a2 : Surjective (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h2
  have a3 : IsAffineHom (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h3
  have b1 : Flat (q ▷ T).left := MorphismProperty.of_isPullback hR' h1
  have b2 : Surjective (q ▷ T).left := MorphismProperty.of_isPullback hR' h2
  have b3 : IsAffineHom (q ▷ T).left := MorphismProperty.of_isPullback hR' h3
  have c1 : Flat (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b1
  have c2 : Surjective (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b2
  have c3 : IsAffineHom (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b3
  rw [prodMapPairTimesIdentity_eq_comp_whiskers, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.PsiEvenCoordUnit

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem alg' {G : Type} [CommGroup G] (a b c x y : G) (h : b * y * c = a * x) : y = a * b⁻¹ * c⁻¹ * x := by
  rw [mul_right_comm (a * b⁻¹), mul_right_comm a, ← h, mul_right_comm (b * y), mul_right_comm b, mul_inv_cancel,
    _root_.one_mul, mul_inv_cancel_right]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  intro R _ _ _ D hE y x x' hx hx'
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, val D.sym (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact xK_eq D y
    rw [this]
    refine val_int ξ hJc D.sym (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A,
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨j, h, i1, rfl⟩ := hx
  obtain ⟨j', h', i1', rfl⟩ := hx'
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc y j i1 (h trivial)
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc (-y) j' i1' (h' trivial)
  have e1 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.psi y).s j) = kU (genVal (D.psi y) j h) :=
    Units.ext (gm_genVal ξ (D.psi y) j h)
  have e2 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j') ((D.psi (-y)).s j') = kU (genVal (D.psi (-y)) j' h') :=
    Units.ext (gm_genVal ξ (D.psi (-y)) j' h')
  have f : cU c2 * kU (genVal (D.psi (-y)) j' h') * cU w = cU c1 * kU (genVal (D.psi y) j h) :=
    (congrArg₂ (· * ·) (g2.trans (congrArg (cU c2 * ·) e2)) hw).symm.trans
      (e.trans (g1.trans (congrArg (cU c1 * ·) e1)))
  refine ⟨c1 * c2⁻¹ * w⁻¹, ?_⟩
  have k3 : genVal (D.psi (-y)) j' h' = Units.map (algebraMap R (FractionRing R)).toMonoidHom (c1 * c2⁻¹ * w⁻¹) *
      genVal (D.psi y) j h := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [map_mul]
    change kU _ = cU (c1 * c2⁻¹ * w⁻¹) * kU _
    rw [map_mul, map_mul, map_inv, map_inv]
    exact alg' _ _ _ _ _ f
  exact congrArg Units.val k3

end GlobalTheory.PsiEvenCoordUnit
end
end

