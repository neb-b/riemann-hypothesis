module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ProductFormIsSectionPointwiseNormLeStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBounds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem phiFD_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) (t : ℝ)
    (x : FD.Frame X.Ψ r) : 0 ≤ I2.phiFD X t x := by
  unfold I2.phiFD
  split_ifs
  · positivity
  · exact le_rfl

theorem exists_etaRule_cusp_ne_zero_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ₀ : c.F →+* ℂ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodEmb c σ₀ → AllTest Xo c → 2 ≤ r → ∀ (R : ℕ), Odd R → 1 < R → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (i : ℕ) (J : Type) (_ : Fintype J) (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Spans xs ∧ IsEtaRule Xo c R cf xs f ∧ f ∈ cusp Xo c U 0 (2 * R ^ 4 * r * i) ∧ f ≠ 0 ∧ (∀ k, ∃ x ∈ ((U σ₀).X k).dom, rdU (U σ₀) f k x ≠ 0) ∧ (∀ a n g, Dom a n → g ∈ sec Xo c a n → f * g = 0 → g = 0) ∧ (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 (2 * R ^ 4 * r * i) k) (rdU (U σ) f k) x ≤ Real.exp (-(i : ℝ) * (I2.phiFD ((U σ).X k) (I2.th (E := E) q R0) x - p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))))) ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 (2 * R ^ 4 * r * i) f ≤ Real.exp (i * p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))) := by
  intro E _ _ _ H Dw l Xo c r U σ₀ hU hσ₀ hT hr R hR hR1 DF q m R0 hrun hm
  obtain ⟨i, inst, x₀, cf, f, hi, hG, hJ, hcf, hsp, hf, hnz⟩ :=
    GlobalTheory.EtaAn.exists_small_coeff_rule_ne_zero E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) hT R hR hR1 hr
  have hn : r * (2 * R ^ 4 * i) = 2 * R ^ 4 * r * i := by ring
  have hRp : 0 < R := by omega
  have hsec : f ∈ sec Xo c 0 (2 * R ^ 4 * r * i) := by
    rw [← hn, ← hG]
    exact (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR _ r cf _).2 f hf
  have hev : Even (2 * R ^ 4 * r * i) := ⟨R ^ 4 * r * i, by ring⟩
  have h2 : 2 ≤ 2 * R ^ 4 * r * i := by
    have h1 : 0 < R ^ 4 * r * i := by positivity
    have h3 : 2 * R ^ 4 * r * i = 2 * (R ^ 4 * r * i) := by ring
    omega
  have hN : 1 ≤ max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2) :=
    Nat.mul_pos (lt_of_lt_of_le Nat.one_pos (le_max_left _ _)) (pow_pos hRp _)
  have harch : ∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom,
      ((U σ).X k).pnorm (laU (U σ) 0 (2 * R ^ 4 * r * i) k) (rdU (U σ) f k) x ≤
        Real.exp (-(i : ℝ) * (I2.phiFD ((U σ).X k) (I2.th (E := E) q R0) x -
          p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2)))) := by
    intro σ hσ
    rw [← hn]
    exact (GlobalTheory.T.productForm_isSection_pointwiseNorm_le E H Dw l Xo c σ r (U σ) hσ (hU σ hσ) hT R i _ hR hR1 hG hN _ cf _ f hJ hcf hsp hf
      DF q m R0 hrun hm).2
  have hcusp := GlobalTheory.cusp_and_supC_le_of_bounded E H Dw l Xo c r U (2 * R ^ 4 * r * i) f
    (Real.exp (i * p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2)))) h2 hev hU hsec
    (fun σ hσ k x hx => (harch σ hσ k x hx).trans (Real.exp_le_exp.2 (by
      have h0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (phiFD_nonneg ((U σ).X k) (I2.th (E := E) q R0) x)
      linarith))) (Real.exp_pos _).le
  refine ⟨i, _, inferInstance, cf, _, f, hi, hG, hsp, hf, hcusp.1, ?_, hnz, ?_, harch, hcusp.2⟩
  · rintro rfl
    obtain ⟨k⟩ := _root_.GlobalTheory.nonempty_comp_of_isUnf E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) (by omega)
    obtain ⟨x, -, hx⟩ := hnz k
    apply hx
    rw [map_zero]
    rfl
  · intro a n g hD hg hfg
    exact GlobalTheory.eq_zero_of_mul_eq_zero_of_reading_ne_zero E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) 0 a _ n f g
      ⟨fun _ => antitone_const, hev⟩ hD hsec hg hnz hfg

end GlobalTheory.EtaAn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem phiC_le_normalized_valuation_local_model_base_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (O : Type) [CommRing O]
    (β₀ : O →+* c.F) (Y : Model Xo c β₀) (hB : PointsOfFlagModel.BaseAt la β₀) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (y : IntFr Xo c T io) (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (Pc : PointsOfFlagModel.PtC Y C) (hO : OverLa la T.V io e)
    (hAlg : T.FinRes) (eF : T.Fr →+* ↥C.S) (heF : eF.comp io = Pc.fK)
    (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (hy : letI := io.toAlgebra; Pc.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x)
    (cj : E → E) (hcj : ∀ a, cj a = IsCMField.complexConj E a) :
    ∃ (A : DatAt Y Pc) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧
      ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ)
        (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f →
        ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 *
          (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  letI := io.toAlgebra
  obtain ⟨G, ⟨I⟩⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).1 T io y
  obtain ⟨T', φ, G', m, hφi, hφf, -, -, U, hU, hUt⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G I.t' I.m2 y.1.x I.m1 hAlg
  obtain ⟨i, ρ, hρ, hi, hiv, hf⟩ := _root_.GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' φ hφi hφf
  obtain ⟨f, hfi, hfφ, hfm⟩ := hf _ C eF hle hlt
  obtain ⟨A, e', hA⟩ := _root_.GlobalTheory.EtaVal.datAt_of_uniformisation E H Dw l Xo c O β₀ Y la hB
    T io e hO y.1.x y.1.s G I y.1.x_over T' φ G' m U hU hUt _ C Pc eF f heF hy hfφ hfm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨Q, β, hQ, hQ0, -, hβQ, hβ⟩ := _root_.GlobalTheory.ValForm.main E H T'.V G' U ϖ hϖ cj hcj
  have hf1 : ∀ a, ‖((intO ↥C.S).subtype.comp f) a‖ ≤ 1 := fun a => (f a).2
  have hfi' : Function.Injective ((intO ↥C.S).subtype.comp f) :=
    (intO ↥C.S).subtype_injective.comp hfi
  have hO' := hO.bc i hρ hiv
  obtain ⟨hun, hew⟩ := _root_.GlobalTheory.EtaVal.UnitNorm.logb_norm_uniformiser c.F la T' (i.comp io) (ρ * e) hO' ϖ hϖ C _ hf1
  set t : ℝ := -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖((intO ↥C.S).subtype.comp f) ϖ‖ with ht
  have hρe : (0 : ℝ) < ((ρ * e : ℕ) : ℝ) := by exact_mod_cast hO'.1
  have hew' : (0 : ℝ) < (Formalism.BasicNotions.eWL c.F la : ℝ) := by exact_mod_cast hew
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (mul_pos hρe hew')
    linarith
  obtain ⟨bA, hbA, hφ⟩ := _root_.GlobalTheory.EtaVal.phiC_smul_pull E cj A.Ylat U.D.toPre.X e' β t ht0
  refine ⟨A, bA, fun a b => ?_, ?_⟩
  · rw [hbA, hA, hβ _ _ _ hfi' hf1]
  intro R hR hR1 J _ n cf xs g hsp hg
  letI : Algebra c.F T'.Fr := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr T'.Fr ψ y.1
  obtain ⟨I'⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).2 T.V T'.V φ ψ y.1 y' G G' m I hi hy'
  have hval := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR J n cf xs g hg T.Fr y.1 y.2.1).2
    T'.Fr ψ y' hy'
  by_cases h0 : evI y g = 0
  · rw [h0, nval_zero]; exact le_top
  have h0' : i (evI y g) ≠ 0 := (map_ne_zero i).2 h0
  have hpt := _root_.GlobalTheory.EtaVal.card_mul_phiC_le_valuation E H Dw l Xo c T'.V y' G' I' U ϖ hϖ Q hQ hQ0 cj hcj β hβQ R hR hR1 J n cf xs
    (i (evI y g)) hsp hval h0'
  rw [← nval_bc (V' := T'.V) i hρ hiv e, nval_of_ne h0', EReal.coe_le_coe_iff, le_div_iff₀ hρe, hφ]
  refine le_trans (le_of_eq ?_) hpt
  calc _ = (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β *
        (t * (((ρ * e : ℕ) : ℝ) * Formalism.BasicNotions.eWL c.F la)) := by ring
    _ = _ := by rw [hun, _root_.mul_one]

theorem phiC_le_nval_of_lies :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (z : PointsOfFlagModel.Pt Tw .yy), OverLa la T.V io e → y.IsAlg → LiesOverBaseChange la Tw T io y z → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (A : DatAt (Tw.Y z.1) z.2.2.1) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧ ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f → ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  intro E _ _ _ H Dw l Xo c la Tw hTw T io e y z hO hAlg hL cj hcj
  have hv : z.1.1 = la := congrArg Subtype.val hL.1
  have hB : PointsOfFlagModel.BaseAt la (Tw.β z.1) := by
    have h := (hTw.1 z.1).1
    rwa [hv] at h
  refine hL.2.elim fun eF h => ?_
  exact phiC_le_normalized_valuation_local_model_base_change E H Dw l Xo c la _ (Tw.β z.1) (Tw.Y z.1) hB T io e y z.2.1 z.2.2.1
    hO hAlg eF h.1 h.2.1 h.2.2.1 h.2.2.2.1 cj hcj

end GlobalTheory.EtaVal
end
end

