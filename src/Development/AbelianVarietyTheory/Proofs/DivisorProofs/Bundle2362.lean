module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

noncomputable section

namespace GlobalTheory.Mum.SecBZeroBpf

theorem unitAt_pow {S : Scheme.{0}} [IsLocallyNoetherian S] (hL : Laws) (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ P.A) (m : ℕ) :
    UnitAt P.L ![(translPt P.A (1 : Over.mk t ⟶ P.A)).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left (IsLocalRing.closedPoint K)) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : AlgebraicGeometry.IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := GlobalTheory.ThetaRep.finrank_secM hL.secBaseChange P (n := 1) le_rfl t
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    GlobalTheory.NoBasePoint.unitAt_transl P.isLB θ k a y (by
      rw [← GlobalTheory.NoBasePoint.ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (GlobalTheory.NoBasePoint.unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m 1

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  have h' : D.c 0 * D.c 0 = D.c 0 := h.symm
  rw [mul_eq_left] at h'
  rw [h']
  show toUnit _ ≫ η[D.P.A] = η[D.P.A]
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem _root_.GlobalTheory.Mum.exists_secB_zero_mem_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  intro R _ _ _ hB D k hk x hx
  haveI : IsNoetherianRing R := hB.1.1
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hTW : DVR.TwistBCSpanStatement := DVR.twistBCSpan_of GlobalTheory.twistBaseChange
  let P := D.toPre.P
  let K := AlgebraicClosure (P.A.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ P.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.A.left.residueField x) K)) ≫ P.A.left.fromSpecResidueField x
  have hu : ∀ q, u q = x := fun q => (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply x _)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ P.A.hom)
  let f : R →+* K := φ.hom
  have hφ' : Spec.map (CommRingCat.ofHom f) = u ≫ P.A.hom := hφ
  have e2 : (u ≫ P.A.hom) (closedPoint K) = closedPoint R :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ (hu _)).trans hx)
  have e : (Spec.map (CommRingCat.ofHom f)) (closedPoint K) = closedPoint R := by rw [hφ']; exact e2
  have e3 : Ideal.comap f (maximalIdeal K) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal e
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal R := (mem_maximalIdeal a).2 hna
    rw [← e3] at h1
    exact (mem_maximalIdeal _).1 h1 ha⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let xb : T ⟶ P.A := Over.homMk u hφ'.symm
  let y := (ptSecT P.A xb).left (closedPoint K)
  have hy : (snd T P.A).left y = x := by
    have e4 : ptSecT P.A xb ≫ snd T P.A = xb := lift_snd _ _
    have e5 := congrArg (fun q => q.left (closedPoint K)) e4
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e5
    exact e5.trans (hu _)
  have c0 := c_zero D.toPre
  have a0 : (snd T P.A).left ≫ D.toPre.famφB 0 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.toPre.famφB 0 1 = (translPt P.A (1 : T ⟶ P.A)).left := by
    show (snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0) =
        snd T P.A * (toUnit _ ≫ D.toPre.c 0) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm, GlobalTheory.NoBasePoint.translPt_eq, c0, MonObj.comp_one]
    rfl
  have a2 : (snd T P.A).left ≫ D.toPre.famφB 0 2 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.toPre.c 0).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left, c0]
  have a3 : (snd T P.A).left ≫ D.toPre.famφB 0 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[D.toPre.P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.toPre.famφB 0 i) (DegPre.famε k) y := by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (unitAt_pow hL P (Spec.map (CommRingCat.ofHom f)) xb (k - 2))
    rw [Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_two]
    have hk' : ((k - 2 : ℕ) : ℤ) + 1 = (k : ℤ) - 1 := by omega
    simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hk']
    abel
  obtain ⟨m, c', β, hβ⟩ := hTW R D.toPre k (by omega) 0 K f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e6 := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e6).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  rw [← hy]
  exact ⟨β i, _, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

end GlobalTheory.Mum.SecBZeroBpf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.ZeroFam

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval; exact (congrArg (gs r z _) (hs _)).trans (gs_zero' _ _ _)

theorem secB_zero_of_pullB {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x))
    (b' : D'.SecB k x) (hb : ∀ j, b.f j = 0) (h : PullB hD x b b') : ∀ q, b'.f q = 0 := by
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB
    ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ y))
  have e := h _ (𝟙 _) y p q (fun κ => hp κ) (fun κ => Set.mem_iInter.1 hy κ)
  rw [show b.f p = 0 from hb _] at e
  have e2 := e.symm.trans (gs_zero' _ _ _)
  exact ((Units.mul_right_eq_zero _).1 e2).trans (gs_zero' _ _ _).symm

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

open GlobalTheory.ExpInt

theorem section_eq_zero_of_expansion_zero_family {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ α j, (f α).f j = 0)
    (hE : ∀ e, U.ExpandsAt e k σ f) : ∀ j, σ.f j = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have ex : ∀ (φ' : Fin 1 → (pullback G.hom (jK W) ⟶ G.left))
      (_ : φ' = fun _ => pullback.fst G.hom (jK W) ≫ 𝟙 G.left),
      ∃ s' : LB.Sec (LB.LinComb U.LG.L φ' (fun _ => (k : ℤ))), ∀ z J, Good U.LG.L z J →
        sval s' (𝟙 _) z J = sval σ (pullback.fst G.hom (jK W)) z J := by
    rintro _ rfl
    exact ⟨pullSec _ _ _ σ _, fun z J hJ => (SectionScalarValuation.sval_pullSec _ _ σ _ (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩
  obtain ⟨s₀, hs₀⟩ := ex (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm)
  have h1 : scal (pullback.snd G.hom (jK W) ≫ jK W) (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have h1' : scal (DegPre.BF D.toPre (FractionRing W)).hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have hF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing W) α) (DegPre.famε k)
      ((0 : Fam D.toPre (FractionRing W) k).s α) (D.toPre.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D.toPre (FractionRing W)).left (scal (DegPre.BF D.toPre (FractionRing W)).hom 1) := fun α => by
    rw [h1']
    exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J _ =>
      (sval_eq_zero _ (hf α) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm
  have hE₀ : ∀ e, U.ExpandsAt e k (SecOps.secZero : H0 U.LG.L k) f := fun e => by
    refine ⟨∅, fun α _ j => by rw [show (f α).f j = 0 from hf α j, map_zero], fun p j₁ jf jt _ _ => ?_⟩
    simp only [Finset.attach_empty, Finset.sum_empty]
    erw [show (SecOps.secZero : H0 U.LG.L k).f j₁ = 0 from rfl, map_zero, map_zero, mul_zero]
  have hEs₀ : U.Expands k s₀ 0 := ⟨1, one_ne_zero, σ, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp]; exact (hs₀ y J hJ).symm, hF, hE⟩
  have hEz : U.Expands k SecOps.secZero 0 := ⟨1, one_ne_zero, SecOps.secZero, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm, hF, hE₀⟩
  have e₀ : s₀ = SecOps.secZero := ((U.expand k hk).2 0).unique hEs₀ hEz
  have hm := secIsMul_of_generic G U.LG.isLB k SecOps.secZero σ SecOps.secZero 1
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm)
    (by
      rw [h1]
      exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp, ← hs₀ y J hJ, e₀])
  intro j
  rw [hm j]
  exact mul_zero _

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

theorem exp_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  intro R _ _ _ _ D C W _ _ _ T k hk s F hF a b hExp b'
  obtain ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩ := hExp
  have hf' : ∀ x q, (f' x).f q = 0 := fun x => secB_zero_of_pullB T.hD x _ (f' x) (hF _) (hP x)
  have hσ' := section_eq_zero_of_expansion_zero_family T.U hk σ' f' hf' hE
  refine ⟨σ, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hP, hE⟩, hs⟩
  rw [hC Z r z J J' hJ hJ', sval_eq_zero _ hσ', mul_zero, mul_zero]

end GlobalTheory.Mum.ZeroFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  intro hA hHS k _ X _ p D hX P a b M hRep hAmp hSemi ρ t₁ hv
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => M).1
  have hα : M.IsSelfInter (Φ (MvPolynomial.X PUnit.unit ^ (D + 1))) :=
    ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, hlim⟩ := _root_.GlobalTheory.HSNef.ampleHS_pair hHS k X p D hX P a b 0 0 M _ hRep hAmp hSemi hα
  have key := _root_.GlobalTheory.rank_le_of_growth_in_radius D (fun t m => P.lc (m * a) (m * b) (Real.exp (t * m)))
    (Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / ((D + 1).factorial : ℝ))
    (((D : ℝ) + 1) * gdeg M D / ((D + 1).factorial : ℝ)) ρ t₀ t₁ (Nat.cast_nonneg _) ?_ ?_
  · have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * (D.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hf, mul_div_mul_left _ _ hD1.ne', le_div_iff₀ hD] at key
    linarith
  · intro t ht
    simpa using hlim t ht
  · intro t m Q hm hQ hle
    obtain ⟨v, hli, hvB⟩ := hv m hm
    have hB := GlobalTheory.VolBr.Pair.isBallFam k X p P (m * a) (m * b)
    have hcard := _root_.GlobalTheory.VolBr.isBallFam_pow_le_encard _ _ _ hB (ρ * m ^ D) Q (Real.exp (t₁ * m)) v (Real.exp_pos _).le hli hvB
    have hsub : P.Bl (m * a) (m * b) (((ρ * m ^ D : ℕ) : ℝ) * Q * Real.exp (t₁ * m)) ⊆
        P.Bl (m * a) (m * b) (Real.exp (t * m)) :=
      (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ hB).1 _ _ (by push_cast; linarith)
    have hfin := _root_.GlobalTheory.HSNef.bl_finite k X p D hX P (m * a) (m * b) (Real.exp (t * m))
    have h1 : ((Q ^ (ρ * m ^ D) : ℕ) : ℕ∞) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard :=
      hcard.trans (Set.encard_le_encard hsub)
    rw [← hfin.cast_ncard_eq] at h1
    have hn : Q ^ (ρ * m ^ D) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard := by exact_mod_cast h1
    show _ ≤ Real.log _
    have hQ' : (0 : ℝ) < ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by positivity
    calc (ρ : ℝ) * (m : ℝ) ^ D * Real.log Q = Real.log ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard : ℝ) :=
          Real.log_le_log hQ' (by exact_mod_cast hn)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

section Helpers
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_zpow (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => n * ε k)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨GeneratorPullback.powGen L φ ε t m, DVR.powGen_isGen _ _ _ _ ht m,
      fun Z r z J _ => (DVR.val_pow t m r z J).trans (zpow_natCast _ _).symm⟩
  · obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => -(m : ℤ) * ε k) (fun U _ h => by
        refine Finset.prod_congr rfl fun k _ => ?_
        show _ = h (φ k) ^ (-(m : ℤ) * ε k)
        rw [neg_mul]) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t m))
        (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht m))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv Z r z J hJ, val_inv, DVR.val_pow, zpow_neg, zpow_natCast]

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Helpers

section Rows
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem comp_tensφ' {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = GlobalTheory.PolDeg.lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem matAct_zero (T : Tens D D' W) : GlobalTheory.TensAct.matAct T 0 = 1 := by
  have h := GlobalTheory.TensAct.matAct_add T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem four_eq (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A)
    (hf : f = GlobalTheory.TensAct.matAct T A) (a : Fin 4) :
    (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] :
      Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) a =
      (GlobalTheory.TensAct.matAct T ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a)).left := by
  subst hf
  fin_cases a
  · show (padd D'.P.A (𝟙 _) _).left = (GlobalTheory.TensAct.matAct T (1 + A)).left
    rw [GlobalTheory.TensAct.matAct_add, GlobalTheory.TensAct.matAct_one]; rfl
  · show 𝟙 D'.P.A.left = (GlobalTheory.TensAct.matAct T 1).left
    rw [GlobalTheory.TensAct.matAct_one]; rfl
  · rfl
  · show (toUnit D'.P.A ≫ η[D'.P.A]).left = (GlobalTheory.TensAct.matAct T 0).left
    rw [matAct_zero]; rfl

theorem sum_one_smul {X : Type} [AddCommGroup X] (v : Fin r → X) (i : Fin r) :
    ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • v k = v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem xe_four (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (a : Fin 4) (i : Fin r) :
    T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i =
      ∑ k, (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k • T.xe y k := by
  fin_cases a
  · show T.xe (y + GlobalTheory.TensAct.latAct T A y) i = ∑ k, (1 + A) i k • T.xe y k
    rw [map_add (f := _), Pi.add_apply, GlobalTheory.TensAct.xe_latAct]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_one_smul]
  · show T.xe y i = ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    rw [sum_one_smul]
  · show T.xe (GlobalTheory.TensAct.latAct T A y) i = ∑ k, A i k • T.xe y k
    rw [GlobalTheory.TensAct.xe_latAct]
  · show T.xe 0 i = ∑ k, (0 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    simp only [map_zero, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

end Rows

end GlobalTheory.MumSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SmallFin

theorem smallSec_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  intro k _ X _ p D hX M
  obtain ⟨P, hL, -⟩ := GlobalTheory.VolBr.exists_pair M M
  subst hL
  have hrep : P.Rep 1 0 P.L := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  obtain ⟨e, he, hrange, hnorm, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P 1 0 P.L hrep
  have hfin : (P.Bl 1 0 1).Finite := _root_.GlobalTheory.HSNef.bl_finite k X p D hX P 1 0 1
  refine (hfin.preimage he.injOn).subset ?_
  intro u hu
  refine ⟨?_, fun σ y => ?_⟩
  · have hm : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at hm
    exact hm
  have h0 : 0 ≤ P.nu 1 0 σ y (e u) := by
    unfold Pair.nu; positivity
  have h1 : P.nu 1 0 σ y (e u) ^ 2 ≤ 1 := by
    rw [hnorm]; exact hu σ y
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 h1

end GlobalTheory.SmallFin
end

