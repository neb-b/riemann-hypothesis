module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_isGt_specialFibre (hB : GtBaseChangeSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) :
    ∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := by
  obtain ⟨E₀, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V (IsLocalRing.maximalIdeal V) D 0 G ⟨g⟩
  have hle : IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ RingHom.ker (IsLocalRing.residue V) := by
    rw [zero_add, pow_one, IsLocalRing.ker_residue]
  let c : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) fun a ha => (RingHom.mem_ker).1 (hle ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hB _ _ (spMap c) E₀ _ hE
  have hc : spMap c ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap (IsLocalRing.residue V) := by
    rw [show thick V (IsLocalRing.maximalIdeal V) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have gp := ((isGrpPullback_pullback (thickObj V (IsLocalRing.maximalIdeal V) 0 G) (spMap c)).comp
    (isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) 0))).congr hc rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso gp (isGrpPullback_pullback G (spMap (IsLocalRing.residue V)))
  exact ⟨E₁, isGt_of_iso e hE₁⟩

theorem utest_dim_and_split : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hsm : SmoothOfRelativeDimension S.g u.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 (ρ.g_eq ▸ ρ.P.smoothDim)
  have hg : u.A.g = S.g :=
    H1.dim_unique u.A.A.hom u.A.smoothDim hsm (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))
  refine ⟨hg, ?_, ?_, ?_, exists_isGt_specialFibre hL.2.2.1.gtBaseChange _ _ (u.U.gt 0)⟩
  · have h := GlobalTheory.UT.dim_eq_rank_add_dim hL u.V _ hA u.D u.A u.G u.semi u.U
    rw [← hg, add_comm]
    exact h.symm
  · have := u.semi.smooth
    have := u.semi.geomConnected
    refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic u.V u.G S.g ?_
    have w : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd u.G.hom (jK u.V) := Over.w u.U.gen.hom
    have : IsIso u.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.U.gen.hom))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩) hsm
  · rw [ρ.N_eq]
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    exact Nat.pow_le_pow_left h₁ 2

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaGeom
open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

theorem val_powFrame {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (x : T ⟶ A) (e) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) : val (powFrame A L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem val_rigT {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
    (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J (fun _ => J (r ≫ T.hom ≫ eSec A))
    (fun _ => by rw [Category.assoc])]
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem sv_sum {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    ThetaAct.sv (∑ i, c i • v i) r z J = ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) * ThetaAct.sv (v i) r z J := by
  let F : SecM A L k T →+ Z.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v r z J) fun a b => ThetaAct.sv_add a b r z hJ
  exact (map_sum F _ _).trans (Finset.sum_congr rfl fun i _ => ThetaAct.sv_smul _ _ _ _ hJ)

theorem comb_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (t : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T)) :
    (∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (t l).f j) ↔ SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (t l) := by
  have e : ∀ j, (∑ l, c l • SecM.ofSec A (t l)).1 j = ∑ l, liftFun A _ (c l) * (t l).f j := fun j => by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem genThrough_pow {x : T ⟶ A} {x₀ : T₀ ⟶ G} {e e₀}
    (H : GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => 1) e e₀ τ) (k : ℤ) :
    GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => k)
      (powFrame A L₁ x e k) (powFrame G L₀ x₀ e₀ k) τ := fun Z r z J J' hJ hJ' => by
  rw [val_powFrame, val_powFrame, H Z r z J J' hJ hJ', Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, mul_zpow]

theorem secRel_comb {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤)) {t : I → LB.Sec (LPow A L₁ k T)}
    {t₀ : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (t₀ l)) {σ σ₀}
    (e : SecM.ofSec A σ = ∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l))
    (e₀ : SecM.ofSec G σ₀ = ∑ l, c l • SecM.ofSec G (t₀ l)) : SecRel hp τ hτ w σ σ₀ := fun Z r z J J' hJ hJ' => by
  have a := (congrArg (fun q => ThetaAct.sv q r z J') e).trans (sv_sum _ _ r z hJ')
  have a₀ := (congrArg (fun q => ThetaAct.sv q (r ≫ psi hp τ hτ) z J) e₀).trans (sv_sum _ _ _ z hJ)
  refine a₀.trans (Eq.trans ?_ (congrArg (_ * ·) a).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial _).symm (h l Z r z J J' hJ hJ')

include hτ in
theorem norm_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {n : ℕ} {rig rig₀}
    (hr : GenThrough w (fun _ : PUnit => eSec A) (fun _ : PUnit => eSec G) (fun _ => 1) rig rig₀ f)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ n).left] ![a, -1])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![a, -1])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ (snd T A ^ n).left) ^ (-1 : ℤ)) * val α r z J')
    (H₀ : LB.Gen.Corr L₀ _ _ _ _ (LB.pullGen L₀ _ _ α₀ (ptSecT G 1).left)
      (LB.mulGen L₀ _ _ _ _ (rigT G L₀ rig₀ T₀ a) (rigT G L₀ rig₀ T₀ (-1)))) :
    LB.Gen.Corr L₁ _ _ _ _ (LB.pullGen L₁ _ _ α (ptSecT A 1).left) (rigT A L₁ rig T (a - 1)) := by
  refine corr_of_val hL₁ fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := val_corr hJ H₀ (𝟙 _ ≫ τ)
  have e₁ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ptSecT_snd]; rfl
  have e₂ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A ^ n).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl
  rw [val_pull hJ, val_mul hJ, val_rigT _ _ _ hJ, val_rigT _ _ _ hJ, Category.assoc,
    ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc, H _ _ _ _ _ hJ hJ', e₁, e₂, Category.assoc (𝟙 _) τ, hτ,
    ← Category.assoc (𝟙 _) T.hom f] at q
  have q₂ := hr _ (𝟙 _ ≫ T.hom) y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at q₂
  rw [val_pull hJ', val_rigT _ _ _ hJ']
  erw [q₂] at q
  apply Additive.ofMul.injective
  replace q := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_zpow] at q ⊢
  linear_combination (norm := module) q

end GlobalTheory.ThetaGeom
namespace GlobalTheory.ZH
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaGeom

theorem spMap_appTop_fn {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (a : R) :
    (spMap y).appTop.hom (fn a) = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (y a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem valAt_of_isValueAt {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x}
    {c : F} (h : IsValueAt A.A A.L k t x (powFrame A.A A.L x e k) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)) :
    ValAt t x e c := fun z J hJ => by
  have q := sv_of_isValueAt h (𝟙 _) z hJ
  rw [Category.id_comp] at q
  exact q

theorem utest_geom_nonempty : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), Nonempty u.Geom := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x, hx, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨rig, fr, hrig, vrig, hfr⟩ := GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso o Ω S ρ p y₀ u x hx w hw
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans (congrArg spMap u.fac.symm) ?_)
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, x (n • a) = x a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := hadd 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => by
    rw [hpow, ← pow_mul]
    exact (hfr a).1.1
  choose U hU hU' using fun a => symLift_move hp τ hτ hw hL₀ hL₁ (hx (S.r • a)).symm (hN a) (ρ.U_sym a)
  obtain ⟨r₀, hr₀, -⟩ := thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  obtain ⟨r₁, hr₁, -⟩ := thetaGrp_acts_linearly hL.globalFns _ u.A S.N (TFK (R := u.V) (PadicAlgCl p))
  refine ⟨⟨x, hx, hadd, fun z hz => ?_, GlobalTheory.T.weilPairing_labelledTorsion_uniformTest hL o Ω S ρ p y₀ u x hx, rig, hrig, fr, fun a => (hfr a).1, th,
    fun a z J hJ => ?_, s, fun a i => valAt_of_isValueAt ?_, α, hα,
    norm_move hp τ hτ hL₀ hL₁ vrig vα ρ.α_norm,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero,
    U, hU, fun a i σ => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hsurj z hz
    exact ⟨a, rfl, fun b hb => hinj hb⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (hfr a).2 hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (genThrough_pow τ (hfr a).2 S.N) (hs i) (ρ.ev_val i a)
    rw [spMap_appTop_fn] at h
    exact h
  · have a₀ : IsActOf ρ.P.A ρ.P.L S.N (ρ.U a) (ρ.s i) (SecM.toSec _ (r₀ (ρ.U a) (SecM.ofSec _ (ρ.s i)))) :=
      (hr₀ _ _ _).2 rfl
    let c : S.J → Γ((baseOver (Sp S.R)).left, ⊤) := fun l => fn (algebraMap o S.R (S.ρ a l i))
    have hc : (fun l => τ.appTop.hom (c l)) = fun l => (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom
        (y₀ (algebraMap o S.R (S.ρ a l i))) := funext fun l => spMap_appTop_fn y₀ _
    have a₁ := hU' a _ _ _ (SecM.toSec _ (∑ l, τ.appTop.hom (c l) • SecM.ofSec _ (s l))) (hs i)
      (secRel_comb hp τ hτ c hs rfl ((comb_iff _ _ _).1 (ρ.U_act a i _ a₀))) a₀
    have a₂ := (hr₁ _ _ _).1 a₁
    have a₃ := comb_iff (fun l => τ.appTop.hom (c l)) s σ
    refine (hr₁ _ _ _).trans (Iff.trans ⟨fun h => a₃.2 (h.symm.trans a₂), fun h => a₂.trans (a₃.1 h).symm⟩ ?_)
    exact forall_congr' fun j => Eq.congr_right (Finset.sum_congr rfl fun l _ => by rw [congrFun hc l])

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericSplit

theorem split_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] (C : Charts G.left) {d : ℕ} (c : Fin d → C.Cl)
    {K K' : Type} [Field K] [Field K'] {H : Over (Sp K)} [GrpObj H] {H' : Over (Sp K')} [GrpObj H']
    {t : Sp K ⟶ S} {t' : Sp K' ⟶ S} (f : Sp K' ⟶ Sp K) (hf : f ≫ t = t') {φ : H.left ⟶ G.left}
    {ψ : H'.left ⟶ G.left} [IsAffineHom φ] [IsAffineHom ψ] (hφ : IsGrpPullback H G t φ)
    (hψ : IsGrpPullback H' G t' ψ) (h : Charts.Split (C.pull φ) c) : Charts.Split (C.pull ψ) c := by
  subst hf
  have w : ψ ≫ G.hom = (H'.hom ≫ f) ≫ t := by rw [hψ.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : H'.left ⟶ H.left, l ≫ φ = ψ ∧ l ≫ H.hom = H'.hom ≫ f :=
    ⟨hφ.1.lift _ _ w, hφ.1.lift_fst _ _ w, hφ.1.lift_snd _ _ w⟩
  subst h₁
  have hl : IsGrpPullback H' H f l := hφ.cancel hψ h₂
  have : IsAffineHom l := MorphismProperty.of_isPullback (P := @IsAffineHom) hl.1.flip inferInstance
  exact SplitPull.pull_pull_and_split_pull.2 K K' H H' f l hl (C.pull φ) d c h

theorem mem_basicOpen_of_mem {X : Scheme.{0}} (C : Charts X) (a a' : {i // C.wt i = C.c₀}) (j : C.I) (x : X)
    (ha : x ∈ C.W a) (h : x ∈ X.basicOpen (C.r a' j)) : x ∈ X.basicOpen (C.r a j) := by
  have hx : x ∈ C.W a ⊓ C.W a' := ⟨ha, X.basicOpen_le _ h⟩
  have e : ∀ (V : X.Opens) (k : C.W a ⊓ C.W a' ≤ V) (u : Γ(X, V)),
      X.basicOpen (resG X k u) = (C.W a ⊓ C.W a') ⊓ X.basicOpen u := fun V k u => X.basicOpen_res u (homOfLE k).op
  have h₁ : x ∈ X.basicOpen (resG X (inf_le_left : C.W a ⊓ C.W a' ≤ C.W a) (C.r a j)) := by
    rw [C.trans a a' j, Scheme.basicOpen_mul, e, e, ← C.inter]
    exact ⟨⟨hx, hx⟩, hx, h⟩
  rw [e] at h₁
  exact h₁.2

theorem exists_open {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (C : Charts G.left) {d : ℕ}
    (c : Fin d → C.Cl) (Sg : Set (Sp R)) (hd : Dense Sg) (hs : C.SplitOn c Sg) :
    ∃ (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) (b : R), b ≠ 0 ∧ (∀ n, C.wt (j n) = c n) ∧
      ∀ x : PrimeSpectrum R, b ∉ x.asIdeal →
        eSec G x ∈ C.W a ∧ ∀ n, eSec G x ∈ G.left.basicOpen (C.r a (j n)) := by
  let e : Sp R ⟶ G.left := eSec G
  obtain ⟨a, ha⟩ : ∃ a, e (⊥ : PrimeSpectrum R) ∈ C.W a :=
    TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ _))
  obtain ⟨x, hxa, hx⟩ := hd.inter_open_nonempty _ (e ⁻¹ᵁ C.W a).isOpen ⟨_, ha⟩
  obtain ⟨K, _, t, _, ht, -, i, hT⟩ := hs x hx
  have hp := isGrpPullback_pullback G t
  have he : (eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t = t ≫ e :=
    eSec_comp_of_isGrpPullback hp
  let y : Sp K := (⊥ : PrimeSpectrum K)
  have hy : t y = x := ht.le ⟨y, rfl⟩
  have hj : ∀ n, ∃ j, C.wt j = c n ∧ e x ∈ G.left.basicOpen (C.r a j) := by
    intro n
    obtain ⟨a', j, hj, hm⟩ := hT.bpf n (eSec ((Over.pullback t).obj G) y)
    refine ⟨j, hj, mem_basicOpen_of_mem C a a' j _ hxa ?_⟩
    have hm' : eSec ((Over.pullback t).obj G) y ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a' j) := by
      rw [Scheme.preimage_basicOpen]
      exact hm
    have h2 : ((eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t) y ∈
      G.left.basicOpen (C.r a' j) := hm'
    rw [he] at h2
    rw [← hy]
    exact h2
  choose j hj hjx using hj
  let U : Set (PrimeSpectrum R) := (e ⁻¹ᵁ C.W a : Set (Sp R)) ∩ ⋂ n, (e ⁻¹ᵁ G.left.basicOpen (C.r a (j n)) : Set (Sp R))
  have hU : IsOpen U := (e ⁻¹ᵁ C.W a).isOpen.inter (isOpen_iInter_of_finite fun n => (e ⁻¹ᵁ _).isOpen)
  have hxU : x ∈ U := ⟨hxa, Set.mem_iInter.2 hjx⟩
  obtain ⟨_, ⟨b, rfl⟩, hb, hbU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  refine ⟨a, j, b, ?_, hj, fun z hz => ⟨(hbU hz).1, fun n => Set.mem_iInter.1 (hbU hz).2 n⟩⟩
  rintro rfl
  exact hb (Ideal.zero_mem _)

theorem split_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hd hs
  obtain ⟨a, j, b, hb, hj, hU⟩ := exists_open G C c Sg hd hs
  let R' := Localization.Away b
  have hle : Submonoid.powers b ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hb
  haveI : IsDomain R' := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers b) R' inferInstance
  let u : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  haveI : IsOpenImmersion u := IsOpenImmersion.of_isLocalization b
  have hu : Set.range u = (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) := PrimeSpectrum.localization_away_comap_range R' b
  let G' : Over (Sp R') := (Over.pullback u).obj G
  let π : G'.left ⟶ G.left := pullback.fst G.hom u
  have hp : IsGrpPullback G' G u π := isGrpPullback_pullback G u
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.1.flip inferInstance
  haveI : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom u))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd G.hom u))
  haveI : QuasiCompact G'.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom u))
  have hd' : Dense (u ⁻¹' Sg) := hd.preimage u.isOpenEmbedding.isOpenMap
  have hs' : (C.pull π).SplitOn c (u ⁻¹' Sg) := by
    intro x hx
    obtain ⟨K, _, t, _, ht, hsp⟩ := hs _ hx
    have hr : Set.range t ⊆ Set.range u := by
      rw [ht]
      rintro _ rfl
      exact ⟨x, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' ≫ u = t := ⟨_, IsOpenImmersion.lift_fac u t hr⟩
    haveI : IsAffineHom (pullback.fst G'.hom t') :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
    refine ⟨K, inferInstance, t', this, ?_, ?_⟩
    · have h1 : ∀ y, t' y = x := fun y => u.isOpenEmbedding.injective (by
        have : t y = u x := ht.le ⟨y, rfl⟩
        rw [← this, ← ht']; rfl)
      ext z
      exact ⟨fun ⟨y, hy⟩ => hy ▸ h1 y, fun hz => ⟨(⊥ : PrimeSpectrum K), (h1 _).trans hz.symm⟩⟩
    · exact split_transport C c (𝟙 _) (by rw [Category.id_comp, ht']) (isGrpPullback_pullback G t)
        ((isGrpPullback_pullback G' t').comp hp) hsp
  have he : ∀ x : Sp R', π (eSec G' x) = eSec G (u x) := fun x =>
    congrArg (fun q => q x) (eSec_comp_of_isGrpPullback hp)
  have hb' : ∀ x : Sp R', b ∉ (u x).asIdeal := fun x => hu.le ⟨x, rfl⟩
  have hB : (C.pull π).Based c a j := by
    refine ⟨fun x _ => ?_, fun n => ⟨hj n, fun x _ => ?_⟩⟩
    · change π (eSec G' x) ∈ C.W a
      rw [he]
      exact (hU _ (hb' x)).1
    · change eSec G' x ∈ G'.left.basicOpen ((π.app (C.W a)).hom (C.r a (j n)))
      rw [← Scheme.preimage_basicOpen]
      change π (eSec G' x) ∈ G.left.basicOpen (C.r a (j n))
      rw [he]
      exact (hU _ (hb' x)).2 n
  haveI : IsAffineHom (pullback.fst G'.hom (Out.jK R')) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have h := GlobalTheory.T.split_generic_of_based_weightedCharts R' G' (C.pull π) d c _ hd' hs' a j hB
  have hun : IsUnit (algebraMap R (FractionRing R) b) :=
    IsLocalization.map_units (FractionRing R) (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors R)
  let g : R' →+* FractionRing R := IsLocalization.Away.lift b hun
  have hg : Function.Injective g := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective R' hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  let g' : FractionRing R' →+* FractionRing R := IsFractionRing.lift hg
  refine split_transport C c (spMap g') ?_ ((isGrpPullback_pullback G' (Out.jK R')).comp hp)
    (isGrpPullback_pullback G (Out.jK R)) h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change g' (algebraMap R' _ (algebraMap R R' x)) = algebraMap R _ x
  rw [IsFractionRing.lift_algebraMap]
  exact IsLocalization.Away.lift_eq b hun x

end GlobalTheory.ZJ.GenericSplit
end
end

