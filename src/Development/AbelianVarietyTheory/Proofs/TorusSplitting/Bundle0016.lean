module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem mul_le_of_forall_rat_le (N : ℕ) (hN : 0 < N) (x : ℝ) (a : ℤ)
    (h : ∀ q : ℚ, (q : ℝ) ≤ x → (N : ℚ) * q ≤ (a : ℚ)) : (N : ℝ) * x ≤ (a : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hc
  have h1 : (a : ℝ) / N < x := by
    rw [div_lt_iff₀ hN', mul_comm]; exact not_le.mp hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  have h2 : (N : ℝ) * (q : ℝ) ≤ (a : ℝ) := by exact_mod_cast h q hq2.le
  rw [div_lt_iff₀ hN', mul_comm] at hq1
  linarith


set_option maxHeartbeats 1000000 in
theorem card_mul_phiC_le_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ _ hcpl _ y G S P ϖ hϖ Q hQ hQ0 cj hcj β hβ R hR hR1 J _ n cf xs val hsp hval hne
  obtain ⟨hLL, h2, h3, h4, h5⟩ := GlobalTheory.lawsAndExpansions
  have hL : Laws := hLL.1
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have htors := GlobalTheory.UT.torsionIso_of_pelUnif hLL h2 h3 h4 h5 E H V _ hA G P
  haveI hfin : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R hR1).1
  obtain ⟨v, hv, hvv⟩ := _root_.GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra c.F F := ((algebraMap (FractionRing V) F).comp (algebraMap c.F (FractionRing V))).toAlgebra
  let ψ : FractionRing V →ₐ[c.F] F := { algebraMap (FractionRing V) F with commutes' := fun _ => rfl }
  have hψ : ψ.toRingHom = algebraMap (FractionRing V) F := rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c _ F ψ y
  have hzx : z.x = spMap (algebraMap (FractionRing V) F) ≫ y.x := hz.1
  have hR0 : 0 < R := by omega
  have e4 : (R ^ 2) ^ 2 = R ^ 4 := by rw [← pow_mul]
  have hR2 : Odd (R ^ 2) := hR.pow
  obtain ⟨-, hbc, hloc, hex⟩ := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (pow_pos hR0 4)
  obtain ⟨ev, hev⟩ := hex F z.x
  have hevt : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := by
    rw [e4]
    exact (hbc F F (RingHom.id F) z.x z.x (𝟙 _) (by simp [spMap]) ev hev).2
  have hevs : ∀ p : ptO Xo z.x ⟶ Xo.univ.t.G, p ^ ((R ^ 2) ^ 2) = 1 → ∃ q, ev q = p := by
    rw [e4]
    exact (hloc F z.x ev hev).1
  have hw := fun q => ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR2).1 F z (ev q) (hevt q)).exists
  choose w hw using hw
  have hz' : EtaValAt Xo c R cf xs z (etaExpr (R ^ 4) cf xs w) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id _ _, z, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, PullbackSections.frMap_refl z, hev, hw, rfl⟩
  have hvalF : algebraMap (FractionRing V) F val = etaExpr (R ^ 4) cf xs w :=
    (GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hR J n cf xs).2 _ F ψ y z hz _ _ hval hz'
  obtain ⟨Φ, w₀, hN, hact, hint⟩ := GlobalTheory.T.exists_fib_normW_of_intSec E H Dw l Xo c V y G S P
  obtain ⟨th, hth⟩ := _root_.GlobalTheory.EtaVal.exists_secA_secTie E H Dw l Xo V y.x P.A Φ F z.x hzx z.s
  obtain ⟨ϑ, hϑ, hν⟩ := _root_.GlobalTheory.EtaVal.exists_expansion_nonneg V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ hN.1 th
    (hint F ψ z th hψ hz hth)
  obtain ⟨tr, htr, htra⟩ := GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp E H Dw l Xo V y.x P.A Φ F z.x hzx
  obtain ⟨pt, hpt, hspan⟩ := GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses E H V G P htors F ((R ^ 2) ^ 2) (pow_pos (pow_pos hR0 2) 2)
    (LatMod Dw (R ^ 4)) (fun a => tr (ev a)) (fun a b => by rw [hev.1, map_mul])
    (fun o a => by rw [hev.2.1]; exact htra _ _ (hact o) _)
    (fun a => by rw [← map_pow, hevt, map_one])
    (fun u hu => by
      obtain ⟨a, ha⟩ := hevs (tr.symm u) (by rw [← map_pow, hu, map_one])
      exact ⟨a, by rw [ha, MulEquiv.apply_symm_apply]⟩)
  have hb : ∀ a (q : ℚ), (∀ χ, q ≤ (Q ((R ^ 2) • χ + (pt a).y) : ℚ) / ((R ^ 2) ^ 2 : ℕ)) →
      (q : WithTop ℚ) ≤ v (w a) := by
    intro a q hq
    obtain ⟨t, ht⟩ := GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value E H Dw l Xo c V y.x P.A Φ F z hzx th hth (R ^ 2) hR2 (ev a) (tr (ev a)) (w a)
      (hevt a) (htr _) (hw a)
    exact _root_.GlobalTheory.EtaVal.le_val_thetaConst V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ Φ.ρ hN th ϑ hϑ hν (R ^ 2) hR2 (pt a)
      (tr (ev a)) t (w a) (hpt a) ht q hq
  haveI : Module.Finite ℤ P.D.toPre.X := P.D.toPre.finX
  have hcj1 : ∀ a : 𝓞 E, ∃ a' : 𝓞 E, (a' : E) = cj a := fun a => ⟨H.bar a, by rw [H.bar_eq, hcj]⟩
  have hcj2 : (H.w0 : E) + cj H.w0 = 1 := by
    rw [hcj, ← H.bar_eq, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]; simp
  have key : ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (R : ℝ) ^ 4 →
      (Nat.card (LevGrp Dw (R ^ 4)) : ℚ) * q ≤ ((vV V val : ℤ) : ℚ) := by
    intro q hq
    have h := _root_.GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr E H Dw (R ^ 4) J n cf xs F v w q (fun g j => by
      refine _root_.GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq E cj hcj1 H.w0 hcj2 P.D.toPre.X Q β hβ hQ0 (R ^ 2) (by nlinarith) n
        (fun b => (pt (g (xs j b))).y) (hspan n (fun b => g (xs j b)) ?_) (fun b => v (w (g (xs j b))))
        (fun b => hb _) q ?_
      · have := congrArg (Submodule.map (g : LatMod Dw (R ^ 4) →ₗ[𝓞 E] LatMod Dw (R ^ 4))) (hsp j)
        rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this
        exact this
      · rw [Nat.cast_pow, ← pow_mul]; exact hq)
    rw [← hvalF, hvv val hne] at h
    exact_mod_cast h
  have := mul_le_of_forall_rat_le _ Nat.card_pos _ _ key
  rw [div_mul_eq_mul_div, mul_div_assoc]
  exact this

end GlobalTheory.EtaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn.ArchPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem gen_mod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pm : D.La →+ (Fin g → ℂ)}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {T : I2.PT E} {ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim}
    (hP : IsPeriod D ty Pm) (hT : IsTorusOf D ty Pm Hm T ψ) (R : ℕ) {n : ℕ} (a : Fin n → D.La)
    (ha : ∀ u : D.La, ∃ (cf : Fin n → 𝓞 E) (v : D.La), u = ∑ b, cf b • a b + (R ^ 4) • v) :
    ∀ x ∈ T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (ψ (Pm (a b))) + (R : ℂ) • y := by
  obtain ⟨-, -, -, hL, hact, -⟩ := hT
  intro x hx
  obtain ⟨u, rfl⟩ := (hL x).1 hx
  obtain ⟨cf, v, rfl⟩ := ha u
  refine ⟨cf, ψ (Pm ((R ^ 3) • v)), (hL _).2 ⟨_, rfl⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hact]
    congr 1
    funext k
    exact hP.1 _ _ _
  · rw [Nat.cast_smul_eq_nsmul, ← map_nsmul ψ, ← map_nsmul Pm, smul_smul, ← pow_succ']

theorem evR_eq {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (hA : AllTest Xo c)
    {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ} {xs : J → Fin n → LatMod Dw (R ^ 4)}
    {f : Rul Xo c} (hf : IsEtaRule Xo c R cf xs f) (y : FrPt Xo c (CAt σ))
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → CAt σ)
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    evR Xo c f y = etaExpr (R ^ 4) cf xs w := by
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have h₁ := (GlobalTheory.T.etaProductRule_value_eq_productForm_of_testRing E H Dw l Xo c R hR J n cf xs f hf (CAt σ) y (hA _ y)).1
  have h₂ : EtaValAt Xo c R cf xs y (etaExpr (R ^ 4) cf xs w) :=
    ⟨CAt σ, inferInstance, inferInstance, AlgHom.id c.F _, y, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hev, hw, rfl⟩
  exact ((GlobalTheory.EtaForm.etaValAt_existsUnique_natural GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR J n cf xs).1 _ y).unique h₁ h₂

end GlobalTheory.EtaAn.ArchPt

namespace GlobalTheory.EtaAn

theorem norm_productForm_le_at_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R i N : ℕ), Odd R → 1 < R → Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i → 1 ≤ N → ∀ (J : Type) [Fintype J] (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) → (∀ j, |cf j| ≤ N) → Spans xs → IsEtaRule Xo c R cf xs f → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) → ‖rdU U f k x.1‖ ≤ Real.exp (-(i : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R N)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA R i N hR h1R hcard hN J _ cf xs f hJ hcf hsp hf DF q m R0 hrun hm k x hx
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (_root_.GlobalTheory.EtaAn.relab_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q (fun j => relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := _root_.GlobalTheory.PeriodTorus.exists_torusOf E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := _root_.GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact _root_.GlobalTheory.EtaAn.isFnOf_entire_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := _root_.GlobalTheory.ahFrame_factor_eq_negOnePow E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := _root_.GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) (U.un k x).x ev :=
    (GlobalTheory.fullLevel_cover_baseChange_torsor GlobalTheory.firstFiveLaws.1 E H Dw l Xo (R ^ 4) hR4).2.2.2 ℂ (U.un k x).x
  obtain ⟨a, ha, hgen⟩ := _root_.GlobalTheory.fullLevel_eq_exp_periods E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact _root_.GlobalTheory.norm_nullVal_eq_norm_theta E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)
  haveI : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1R).1
  haveI := Fintype.ofFinite (LevGrp Dw (R ^ 4))
  have hval : rdU U f k x.1 = ∏ g : LevGrp Dw (R ^ 4), ∑ j, (cf j : ℂ) * ∏ b, toC (w (g (xs j b))) := by
    have e₁ : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e₁, ArchPt.evR_eq hA hR hf (U.un k x) ev w hev hw, etaExpr, finprod_eq_prod_of_fintype]
    rfl
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hspan : ∀ (g : LevGrp Dw (R ^ 4)) j, Submodule.span (𝓞 E) (Set.range fun b => g (xs j b)) = ⊤ := fun g j => by
    have : (Set.range fun b => g (xs j b)) = g.toLinearMap '' Set.range (xs j) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, hsp j, Submodule.map_top, LinearEquiv.range]
  have hgen' : ∀ (g : LevGrp Dw (R ^ 4)) j, ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (g (xs j b)))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact ArchPt.gen_mod hP hT R (fun b => a (g (xs j b))) (hgen r _ (hspan g j))
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : LevGrp Dw (R ^ 4) → J → Fin r → ℂ) (a : LevGrp Dw (R ^ 4) → J → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R N)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R i N h1R hN _ hsec hl2' (LevGrp Dw (R ^ 4)) J
      (by rw [← Nat.card_eq_fintype_card, hcard]) hJ' cf w' a' hcf
  exact key r hr hJ (fun g j b => toC (w (g (xs j b)))) (fun g j b => ψ (z (g (xs j b))))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)

end GlobalTheory.EtaAn
end
end

