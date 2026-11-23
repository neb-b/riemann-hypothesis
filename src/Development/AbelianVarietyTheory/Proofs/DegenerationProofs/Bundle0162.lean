module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitTerm
open TWM TWO

theorem exists_torsion_isUnit (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) {I : Type} [Fintype I] {φ : I → ((Over.mk t ⊗ P.A).left ⟶ P.A.left)}
    {ε : I → ℤ} (σ : LB.Sec (LB.LinComb P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ P.A) (j : ℕ), x ^ l ^ j = 1 ∧
      ∀ z J, Good P.L z J → IsUnit (sval σ (lift (𝟙 (Over.mk t)) x).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hσ
  have hsm := P.isAb.smooth
  let p : (Over.mk t ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk t) P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst t P.A.hom))
  have : IsReduced (Over.mk t ⊗ P.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  obtain ⟨P', g, hg, -, hmul, -⟩ := hL.polBaseChange _ _ t P
  let e : P'.A.left ≅ (Over.mk t ⊗ P.A).left := hg.flip.isoPullback
  let W := (Over.mk t ⊗ P.A).left.basicOpen (σ.f j)
  have hW : (W : Set (Over.mk t ⊗ P.A).left).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
    hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  obtain ⟨y, hy⟩ := hW
  obtain ⟨_, hq, hq'⟩ := (PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred K P' l hl
    hK).inter_open_nonempty (e.hom ⁻¹ᵁ W) (e.hom ⁻¹ᵁ W).isOpen ⟨e.inv y, by
      show e.hom (e.inv y) ∈ W
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; exact hy⟩
  obtain ⟨x, ⟨m, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hq'
  let Φ : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ t) ⟶ P.A) :=
    MonoidHom.mk' (fun x => toBase hg.w x) (hmul _)
  let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  have er : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left = x.left ≫ e.hom := by
    refine pullback.hom_ext ?_ ?_
    · refine (congrArg (fun q => q.left) (lift_fst (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_fst).trans (Over.w x))).symm
    · refine (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact (Category.id_comp _).trans
        ((Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_snd)).symm
  refine ⟨ρ ≫ Φ x, m, by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one], fun z J hJ => ?_⟩
  obtain rfl : z = q := H1.SquareUnits.spec_pt_eq z q
  have hz : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left z ∈ W := by rw [er]; exact hq
  exact H1.SectionArithmetic.isUnit_sval σ _ z hJ j hz

theorem exists_sec_lin {Y : Scheme.{0}} {M : LB Y} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j :=
  ⟨⟨fun j => ∑ i, (SecOps.secScale (b i) (t i)).f j, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, (SecOps.secScale _ _).compat, Finset.mul_sum]⟩, fun _ => rfl⟩

theorem exists_torsion_sum (hL : Laws) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} {m : ℕ}
    (b : Fin m → D.SecB k α) {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (hb : IsSecBasis (T := Over.mk t) (A := D.P.A) _
      (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left))
    (a : Fin m → K) (ha : ∃ i, a i ≠ 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ D.P.A) (j : ℕ), x ^ l ^ j = 1 ∧ ∀ (z : Spec (CommRingCat.of K)) J, Good D.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) * sval (Z := Spec (CommRingCat.of K)) (b i) x.left z J) := by
  obtain ⟨σ, hσ⟩ := exists_sec_lin
    (fun i => (fst (Over.mk t) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)))
    (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left)
  obtain ⟨x, j, hx, hu⟩ := exists_torsion_isUnit hL D.P t σ (fun h => by
    obtain ⟨i, hi⟩ := ha
    have e := (hb σ).unique (y₁ := fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) (y₂ := 0) hσ
      (fun j => (h j).trans (Finset.sum_eq_zero fun i _ => by
        rw [Pi.zero_apply, map_zero, map_zero, MulZeroClass.zero_mul]).symm)
    exact hi ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      ((congrFun e i).trans (map_zero _).symm))) hl hK
  refine ⟨x, j, hx, fun z J hJ => ?_⟩
  have q := hu z J hJ
  rw [SectionScalarValuation.sval_lin _ _ hσ _ z hJ] at q
  refine (congrArg IsUnit (Finset.sum_congr rfl fun i _ => ?_)).mp q
  rw [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, IntegralCoord.gs_appTop, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd]
  rfl

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem genV_torsion {N : ℕ} (hN : N ≠ 0) (g : GtPtF D.toPre F)
    (hg : letI := TorusExt.gtGroup D.toPre F; N • g = 0) (χ : D.toPre.X) : GenV hϖ hv (g.s χ) 0 := by
  letI := TorusExt.gtGroup D.toPre F
  choose l hl hu using fun g : GtPtF D.toPre F => CoefVal.exists_gtV (hϖ := hϖ) (hv := hv) g
  let L : GtPtF D.toPre F →+ (D.toPre.X →+ ℚ) := AddMonoidHom.mk' l fun g g' =>
    (hu (g + g') (l g + l g') (CoefVal.gtV_add ((TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hl g) (hl g'))).symm
  have e : N • l g = 0 := by
    show N • L g = 0
    rw [← map_nsmul, hg, map_zero]
  have e' : l g χ = 0 := by
    have := DFunLike.congr_fun e χ
    simpa [hN] using this
  rw [← e']
  exact hl g χ

theorem exists_value_unit {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α) (a : Fin m → Ov v)
    (x : TO hϖ hv ⟶ D.toPre.P.A)
    (hu : ∀ (z : Spec (CommRingCat.of (ResidueField (Ov v)))) J, Good D.toPre.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField (Ov v)))).inv.hom (residue _ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left) z J)) :
    ∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)), G₀.IsGen ∧
      ∃ c : F, v c = 0 ∧ ∀ (z : (TF (R := V) F).left) J, Good D.toPre.P.L z J →
        ∑ i, GlobalTheory.UT.cst F z (a i) * sval (b i) (ιS hϖ hv ≫ x).left z J =
          GlobalTheory.UT.cst F z c * (val G₀ (ιS hϖ hv).left z J).val := by
  have hL := D.toPre.P.isLB
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local (V := Ov v) D.toPre.P.L hL
    (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)
  choose y hy using fun i => TwistUnit.exists_ratio_local (R := Ov v) hL (H1.SectionArithmetic.pullSec (b i) x.left) G₀ hG₀
  have key : ∀ {E : Type} [CommRing E] (φ : Ov v →+* E) (z : Spec (CommRingCat.of E)) J, Good D.toPre.P.L z J →
      ∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (φ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom φ) ≫ x.left) z J =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)))) *
        (val G₀ (Spec.map (CommRingCat.ofHom φ)) z J).val := fun φ z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, SectionScalarValuation.gs_sum _ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial (y i)
    rw [Category.id_comp] at e
    have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap (CommRingCat.ofHom φ) (y i)))
    have q := (H1.SectionArithmetic.sval_pullSec (b i) x.left _ z hJ).symm.trans (hy i _ (Spec.map (CommRingCat.ofHom φ)) z J hJ)
    rw [map_mul, map_mul, gs_mul _ z ⊤ trivial, _root_.mul_assoc]
    exact congrArg (_ * ·) (q.trans (congrArg (· * _) e'))
  have hc : IsUnit (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)) := by
    let z₀ : Spec (CommRingCat.of (ResidueField (Ov v))) := closedPoint _
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z₀
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit (key (residue _) z₀ J hJ)).mp (hu z₀ J hJ))
    refine isUnit_of_map_unit (residue _) _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁
  exact ⟨G₀, hG₀, _, v_unit v hc.unit, fun z J hJ => key (algebraMap (Ov v) F) z J hJ⟩

theorem exists_coord {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α)
    (hb : IsSecBasis (T := TO hϖ hv) (A := D.toPre.P.A) _ (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α)
      (DegPre.famε k) (b i) (snd (TO hϖ hv) D.toPre.P.A).left))
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} (hs : VGe D F v k α s 0) :
    ∃ a : Fin m → Ov v, (∀ q : ℚ, (∀ i, (q : WithTop ℚ) ≤ v (a i)) → VGe D F v k α s q) ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (a i)) * sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, c, σ, σF, hσ, hc, hsum⟩ := hs
  let c₀ : Fin n → Γ(Spec (CommRingCat.of (Ov v)), ⊤) := fun l =>
    (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom ⟨c l, hc l⟩
  have ec : ∀ l, ιr (v := v) (c₀ l) = c l := fun l =>
    congrArg (algebraMap (Ov v) F) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Ov v))) ⟨c l, hc l⟩)
  obtain ⟨t, ht⟩ := exists_sec_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (c₀ l))
    (fun l => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (σ l) (snd (TO hϖ hv) D.toPre.P.A).left)
  obtain ⟨r, hr, -⟩ := hb t
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (ιr (v := v) (r i))) *
        sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    have e₁ := SectionScalarValuation.sval_lin _ _ ht (ρ ≫ (jO hϖ hv).left) z hJ
    have e₂ := SectionScalarValuation.sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) _ hr
      (ρ ≫ (jO hϖ hv).left) z hJ
    simp only [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, gs_jO, ec, Category.assoc, jO_snd] at e₁ e₂
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) σF (fun j => hsum j) ρ z hJ, ← e₂, e₁]
    exact Finset.sum_congr rfl fun l _ => by rw [SectionScalarValuation.secScal_sval (hσ l) ρ z hJ]
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (r i), fun q hq => ?_, key⟩
  have hF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  choose bF hbF using fun i => exists_sec hL hF (pullSec D.toPre.P.L _ _ (b i) (DegPre.prB D.toPre F).left)
  have hb' := fun i y J hJ => (hbF i _ (𝟙 _) y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)
  refine ⟨m, _, b, bF, fun i => SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hb' i y J hJ).symm, hq,
    IntegralCoord.lin_of_sval hL (fun i => gF D.toPre F (ιr (v := v) (r i))) bF fun y J hJ => ?_⟩
  rw [key _ _ y J hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (_ * ·) (hb' i y J hJ).symm

end

theorem exists_eq_zero {n : ℕ} (c : Fin n → WithTop ℚ) (h₀ : ∀ i, 0 ≤ c i)
    (h : ∀ q : ℚ, 0 < q → ¬ ∀ i, (q : WithTop ℚ) ≤ c i) : ∃ i, c i = 0 := by
  by_contra hc
  have h₁ : (0 : WithTop ℚ) < Finset.univ.inf c := (Finset.lt_inf_iff (WithTop.coe_lt_top 0)).2 fun i _ =>
    lt_of_le_of_ne (h₀ i) fun e => hc ⟨i, e.symm⟩
  obtain ⟨q, hq, hq'⟩ := WithTop.lt_iff_exists_coe_btwn.1 h₁
  exact h q (WithTop.coe_lt_coe.1 hq) fun i => hq'.le.trans (Finset.inf_le (Finset.mem_univ i))

theorem exists_torsion_coef_val_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k n hk hn hnV s α hs hs'
  have hM := D.toPre.P.isLB
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  obtain ⟨m, b, -, hb⟩ := hT V D.toPre k (by omega) α
  have hb₁ : ∀ (R' : Type) [CommRing R'] (f : V →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of V)),
      t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T := Over.mk t) (A := D.toPre.P.A) _
        (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.toPre.P.A).left) := by
    intro R' _ f t ht
    subst ht
    exact hb R' f _ (fun i j => rfl)
  obtain ⟨a, ha, hsa⟩ := exists_coord hϖ hv b (hb₁ _ _ _ rfl) hs
  obtain ⟨i₀, hi₀⟩ := exists_eq_zero (fun i => v (a i)) (fun i => (a i).2) fun q hq h => hs' q hq (ha q h)
  have hres : residue (Ov v) (a i₀) ≠ 0 := by
    rw [residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
    exact (valuation_eq_one_iff (fun _ => Iff.rfl) _).2 hi₀
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, j, hx₀, hu⟩ := exists_torsion_sum hL.1 D.toPre b
    (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom)
    (hb₁ _ ((residue (Ov v)).comp (fO v hϖ hv)) _ (Spec.map_comp _ _).symm) (fun i => residue _ (a i)) ⟨i₀, hres⟩
    hn.two_le hK
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P (n ^ j) (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n ^ j = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    ExactTerm.exists_torsion_lift (Ov v) D.toPre.P.A (n ^ j) (TO hϖ hv).hom x₀ hx₀
  obtain ⟨G₀, hG₀, c, hc, hval⟩ := exists_value_unit hϖ hv b a x (fun z J hJ => by rw [ex]; exact hu z J hJ)
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨g, hg₁, hg₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq hN (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨j, g, 0, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hg₂.symm, fun w _ hω => ?_⟩
  obtain ⟨d, hd, vd⟩ := CoefUnit.v_of_isCoef hϖ hv (genV_torsion hϖ hv hN g hg₂ α) hω x hg₁.symm (s.s α) G₀ hG₀ c
    (fun z J hJ => by
      rw [hsa _ _ z J hJ, ← hval z J hJ, ← Over.comp_left, lift_snd, hg₁]
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl)
  rw [CoefBasic.coef_eq hd, vd, hc]
  simp

end GlobalTheory.OneBasis.UnitTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem existsUnique_hom_extension_smConn_semiAbelian_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  intro T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨hcomm, hsm, hsep, hqc, hgc⟩ := hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one
    AbelianSubgroupFinite.finite_of_torsionFree (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hsm hgc hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.DivisiblePart

open RationalPoint

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y)
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) :
    Surjective f.left := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hC := (isConstructible_image_of_isClosed f isClosed_univ).compl
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible
    continuous_id hC
  rw [Set.preimage_id] at h1 h2
  have hne : (V ∩ closure (f.left '' Set.univ)ᶜ).Nonempty := by
    rw [← closure_nonempty_iff, h2, closure_nonempty_iff]
    exact ⟨y, fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩⟩
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨z, hz⟩ := exists_pt_mem (X := Y) (Z := {c}) hc ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := h z
  exact h1 hcZ ⟨pt x, trivial, hz⟩

theorem geometricallyConnected_of_surjective {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [GeometricallyConnected (f ≫ g)] : GeometricallyConnected g := by
  refine ⟨fun K _ y W fst snd hW => ?_⟩
  have h1 := (IsPullback.of_hasPullback f fst).paste_vert hW
  have : ConnectedSpace ↥(pullback f fst) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h1
  exact (pullback.snd f fst).surjective.connectedSpace (pullback.snd f fst).continuous

theorem isIso_of_dim_le {k : Type} [Field k] {N G : Scheme.{0}} (ν : N ⟶ G) (s : G ⟶ Sp k)
    [IsClosedImmersion ν] [IsIntegral G] [IsReduced N] [Nonempty N] {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g s) (hg' : SmoothOfRelativeDimension g' (ν ≫ s))
    (hle : g ≤ g') : IsIso ν := by
  suffices Surjective ν from isIso_of_isClosedImmersion_of_surjective ν
  refine ⟨fun y => ?_⟩
  by_contra hy
  obtain ⟨n⟩ := ‹Nonempty N›
  obtain ⟨_, ⟨U, hU, rfl⟩, hnU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ν n)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let W : G.Opens := ⟨(Set.range ν)ᶜ, ν.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨z, hzU, hzW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨_, hnU⟩ ⟨y, hy⟩
  obtain ⟨r, hrW, hzr⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hzU
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hzr
  have hr1 : (ν.app U).hom r = 0 := by
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    exact (hrW ht ⟨t, rfl⟩).elim
  have : Nonempty U := ⟨⟨_, hnU⟩⟩
  have h1 := ringKrullDim_succ_le_of_surjective (ν.app U).hom (ν.app_surjective U hU)
    (mem_nonZeroDivisors_of_ne_zero hr0) hr1
  rw [SmoothDim.ringKrullDim_affineOpen k G s g hg U hU ⟨_, hnU⟩,
    SmoothDim.ringKrullDim_affineOpen k N _ g' hg' _ (hU.preimage ν) ⟨n, hnU⟩] at h1
  have : g' + 1 ≤ g := by exact_mod_cast h1
  omega

theorem exists_divisiblePart : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ G), SmConn N ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ (∀ y : (𝟙_ (Over (Sp k)) ⟶ N), ∃ x : (𝟙_ (Over (Sp k)) ⟶ N), x ^ p = y) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) (n : ℕ), n.Coprime p → n ≠ 0 → x ^ n = 1 → ∃ y, y ≫ ν = x) ∧ (∀ F : G ⟶ G, IsMonHom F → ∃ F' : N ⟶ N, IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ g', SmoothOfRelativeDimension g' N.hom ∧ (g ≤ g' → IsIso ν) := by
  intro k _ _ p G _ ⟨hc, hs, hsep, hqc, hgc⟩
  obtain ⟨a, ha⟩ := TorsionDense.exists_pow_stable G p ⊤ Set.univ isClosed_univ (by simp)
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  obtain ⟨Z, hZ, h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ (p ^ a))
    (hpow _) inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ
    (by simp)
  replace h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, (∃ x, x ^ (p ^ a) = y) ↔ Set.range y.left ⊆ Z := by
    intro y
    rw [← h]
    simp only [MonObj.comp_pow, Category.comp_id, Subgroup.mem_top, true_and]
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    have := hpow (p ^ a)
    MonoidHom.mk' (fun x => x ≫ 𝟙 G ^ (p ^ a)) fun x y => MonObj.mul_comp x y _
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance φ.range Z hZ (fun x => by
      rw [← h, MonoidHom.mem_range]
      simp only [φ, MonoidHom.mk'_apply, MonObj.comp_pow, Category.comp_id])
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hw : N.hom = ν.left ≫ G.hom := (Over.w ν).symm
  have hNsep : IsSeparated N.hom := by rw [hw]; infer_instance
  have hNqc : QuasiCompact N.hom := by rw [hw]; infer_instance
  have hGi : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have hNr : IsReduced N.left :=
    have := isNormalScheme_of_smooth N.hom
    IsNormalScheme.isReduced
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ G),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, ∃ y, y ^ (p ^ a) = x ≫ g) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset g.left ν.left
      (hr ▸ ReducedSubgroup.range_subset_of_points g hZ fun x => (h _).1 (hg x))
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, g.w]
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, ∃ y, y ^ (p ^ a) = x ≫ ν := fun x => by
    rw [h, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  obtain ⟨l, hl⟩ := hlift (𝟙 G ^ (p ^ a)) fun x => ⟨x, by rw [MonObj.comp_pow, Category.comp_id]⟩
  have hl' : ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (x ≫ l) ≫ ν = x ^ (p ^ a) := fun x => by
    rw [Category.assoc, hl, MonObj.comp_pow, Category.comp_id]
  have : Surjective l.left := surjective_of_rationalPoints l fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, by rw [← cancel_mono ν, hl', hx]⟩
  have hNgc : GeometricallyConnected N.hom := by
    have : GeometricallyConnected (l.left ≫ N.hom) := by rw [Over.w l]; exact hgc
    exact geometricallyConnected_of_surjective l.left N.hom
  refine ⟨N, _, ν, ⟨AbelianSubgroupFinite.isCommMonObj_of_mono ν, hNs, hNsep, hNqc, hNgc⟩, hν, hνc,
    fun y => ?_, fun x n hn hn0 hx => ?_, fun F hF => ?_, fun g hg => ?_⟩
  · obtain ⟨x, hx⟩ := hmem y
    obtain ⟨z, -, hz⟩ := ha x trivial
    refine ⟨z ≫ l, ?_⟩
    rw [← cancel_mono ν, MonObj.pow_comp, hl', ← pow_mul, ← pow_succ, hz, hx]
  · have hco : (p ^ a).Coprime (orderOf x) :=
      (Nat.Coprime.pow_left a hn.symm).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
    exact ⟨(x ^ m) ≫ l, by rw [hl', ← pow_mul, mul_comm, pow_mul, hm]⟩
  · obtain ⟨F', hF'⟩ := hlift (ν ≫ F) fun x => by
      obtain ⟨y, hy⟩ := hmem x
      exact ⟨y ≫ F, by rw [← MonObj.pow_comp, hy, Category.assoc]⟩
    refine ⟨F', ⟨?_, ?_⟩, hF'⟩
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hF']
  · have hNi : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
    obtain ⟨g', hg'⟩ := exists_dim_of_preconnected N.hom (Classical.arbitrary _)
    refine ⟨g', hg', fun hle => ?_⟩
    have : IsIso ν.left := isIso_of_dim_le ν.left G.hom hg (hw ▸ hg') hle
    have : IsIso ((Over.forget _).map ν) := this
    exact isIso_of_reflects_iso ν (Over.forget _)

end GlobalTheory.DivisiblePart
end

