module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.Bundle0004

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace PositivityTheory.Xj7N.Inj

open GlobalTheory

section Generic

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rat_small (L : HermLB p) (s₀ : L.B.Sec) (hs₀ : genericPoint X ∈ nonzeroLocus s₀) (τ : ℕ) (t : ℝ) :
    ∃ R : (lbPow L.B τ).Sec → X.functionField, Function.Injective R ∧ ∀ h : X.functionField,
      (∀ (c : L.B.ι) (x : X) (hx : x ∈ L.B.U c), RegAt x (h * fnOf (L.B.U c) (gen_mem hx) (s₀.f c) ^ τ)) →
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) (c : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U c)),
        RegAt (under y) (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) →
        ‖ratVal (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) y‖ ^ 2 *
          Real.exp (-((τ : ℝ) * (L.φ σ).φ c y)) ≤ Real.exp (2 * (τ : ℝ) * t)) →
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow τ).smallSec, R S = h := by
  have hr := isRatSec_ratOfSec s₀ hs₀
  have hrτ := GlobalTheory.TrueGeo.SmallSec.isRatSec_pow hr τ
  have hPr := presents_divOfRatSec (L.pow τ).isLB hrτ
  refine ⟨hPr.rat, hPr.rat_injective, fun h hreg hb => ?_⟩
  have hsec : h ∈ (divOfRatSec (L.pow τ).isLB hrτ).sections := by
    refine CartierDiv.mem_sections.2 fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart (L.pow τ).isLB x
    have hx : x ∈ L.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
    refine ⟨_, hPr.isEqn c x hc, ?_⟩
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hx)]
    exact hreg _ x hx
  obtain ⟨S, hS⟩ := hPr.exists_rat_eq hsec
  refine ⟨S, fun σ y => ?_, hS⟩
  let Lτ := (L.shift (fun _ => t) (fun _ => rfl)).pow τ
  obtain ⟨c, hc⟩ := exists_chart Lτ.isLB (under y)
  have hy : y ∈ ptsIn p σ (Lτ.B.U c) := mem_ptsIn.2 hc
  have hy1 : y ∈ ptsIn p σ (L.B.U (c PUnit.unit)) := mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hgen : genericPoint X ∈ Lτ.B.U c := gen_mem hc
  have e0 : fnOf (Lτ.B.U c) hgen ((S : Lτ.B.Sec).f c) =
      h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ := by
    have := hPr.rat_mul S c hgen
    rw [hS, Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem (mem_ptsIn.1 hy1))] at this
    exact this.symm
  have e1 : ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y =
      ratVal (h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ) y := by
    rw [← e0]; exact (ratVal_fnOf hy hgen ((S : Lτ.B.Sec).f c)).symm
  have e2 : (Lτ.φ σ).φ c y = (τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t) := by
    have := Weight.zpow_φ ((L.φ σ).addFn fun _ => 2 * t) (τ : ℤ) c y
    exact this.trans (by push_cast; rfl)
  have hb' := hb σ y (c PUnit.unit) hy1 (hreg _ _ (mem_ptsIn.1 hy1))
  have hn := Weight.nsq_eq (Lτ.φ σ) (secVal_mem (p := p) (σ := σ) (S : Lτ.B.Sec)) hy
  show (Lτ.φ σ).nsq (secVal p σ (S : Lτ.B.Sec)) y ≤ 1
  refine hn.le.trans ?_
  have e4 : secVal p σ (S : Lτ.B.Sec) c y = ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y := by
    erw [secVal_apply]; rfl
  rw [e4, e1, e2]
  have e3 : Real.exp (-((τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t))) =
      Real.exp (-((τ : ℝ) * (L.φ σ).φ (c PUnit.unit) y)) * (Real.exp (2 * (τ : ℝ) * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e3, ← mul_assoc, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  exact hb'

end Generic

theorem eq_zero_of_genVal' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) : f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hZ hf.2


end PositivityTheory.Xj7N.Inj

end
