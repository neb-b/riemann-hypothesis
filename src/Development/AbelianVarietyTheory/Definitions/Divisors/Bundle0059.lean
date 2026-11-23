module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnramPtsDefinite
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}


theorem mem_holSub_model {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem mul_mem_cuspOn_of_isSec {Z : Comp Xo c} {G₀ : WTZ E} (h0 : Even G₀.2) {s : Rul Xo c}
    (hs : s ∈ secZ Xo c (exZ Dw G₀)) (hZ : s ∈ suppOn Z)
    (hh : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G₀ k) (rdU (U σ) s k))
    (hb : ∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C)
    {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * s ∈ cuspOn U Z (G + G₀) := by
  refine ⟨?_, mul_mem_suppOn _ hZ⟩
  have hf' := mem_cuspW.1 hf.1
  refine mem_cuspW.2 ⟨exZ_add_eq (Dw := Dw) G G₀ ▸ mul_mem_secZ hf'.1 hs, fun σ hσ => ?_⟩
  rw [AllWt.rdU_mul, mem_holSub_model]
  intro k
  rw [modelWt_add (U σ) hG h0 k]
  refine (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_model _ _ _).1 (hf'.2 σ hσ) k) _ ⟨hh σ hσ k, ?_⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  refine ⟨max 0 (C / lieFacZ Dw x G₀), fun y _ => ?_⟩
  by_cases hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · refine le_max_of_le_right ((le_div_iff₀' (lieFacZ_pos x G₀)).2 ?_)
    have := hC _ hy
    unfold homN ptN at this
    exact this
  · have := rdU_eq_zero (U σ) hZ hy
    simp only at this
    simp [Data.pnorm, this]


end GlobalTheory.FlatTw
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
section
namespace GlobalTheory.CovTop

structure Hypotheses2 : Prop where

  p1 : GlobalTheory.Published.ToroidalCompactification

  p2 : GlobalTheory.Published.VolGe

  p3 : GlobalTheory.Published.VolNef

  p4 : GlobalTheory.Published.ArCalc

  p5 : GlobalTheory.Published.AbelianDeRham

  p6 : GlobalTheory.Published.TamagawaSpecialUnitary

  p8 : GlobalTheory.Published.RayClassFieldSt

  p12 : GlobalTheory.Published.SemistableReductionSt

  p13 : GlobalTheory.Published.StrongApproxSU

  p14 : GlobalTheory.Published.GreenSeriesSt

  p16 : GlobalTheory.Published.GoodChernWeil

  p19 : GlobalTheory.Published.LandherrSt

  p20 : GlobalTheory.Published.HasseNormSt

  p22 : GlobalTheory.Published.SemiAbelianHomExtension

  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove

  p25 : GlobalTheory.Published.principalPolarisationOneSection

  p26 : GlobalTheory.Published.AbMulNSt

  q1 : GlobalTheory.Published.GrothendieckMessing

  q3 : GlobalTheory.Published.DeRhamCanonicalExtension

  q4 : GlobalTheory.Published.PrismaticDieudonneHodge

  q6 : GlobalTheory.Published.KawamataViehweg

  q7 : GlobalTheory.Published.NefNumerics

  q8 : GlobalTheory.Published.L2ExtensionLogCanonical

  q9 : GlobalTheory.Published.ArithHilbertSamuel

  q10 : GlobalTheory.Published.ChowFormExists

  q11 : GlobalTheory.Published.CycleHeights

  q13 : GlobalTheory.Published.SerreHolomorphicSections

  q15 : GlobalTheory.Published.NadelVanishingAndNonKltDivisor

  q16 : GlobalTheory.Published.Principalisation

  q18 : GlobalTheory.Published.FormalAlgebraisation

end GlobalTheory.CovTop
end

