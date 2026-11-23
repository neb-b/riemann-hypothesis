module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0042
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
namespace GlobalTheory.PlaceTop


set_option maxHeartbeats 4000000 in
theorem integralityCondition_of_addedPoints_secondNorm {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : GlobalTheory.RunIn.SecNorm B) (X : PJ D B P j)
    (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (hX : H2 X S ka wL wF) :
    H2 (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF := hX


set_option maxHeartbeats 4000000 in
theorem integralityCondition_algebraicPoints (D : D7) (T : Top D) (h : LawsP T) (hs : LawsSh T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (ho : Oriented T EX) (p : ℕ) (hp : ∀ n, (T.dδ j n).pd = p)
    (ka wL wF : WeightFamilies.Wt D j) (T₀ nP : ℕ) (hF : IsF' ka wL wF T₀ nP) :
    H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF T₀) ka wL wF := by
  have key : ∀ (w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) →
      (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) →
      (recPJ h j hj).Thc ((zOwnP D p w : 𝓞 (recB h.toLawsCore).KO) * nnW (recB h.toLawsCore) hinj EX wL ^ k *
        nnW (recB h.toLawsCore) hinj EX wF *
        (pPow D (k * c2 D wL + c2 D wF) (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
          (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 (recB h.toLawsCore).KO)) w ≤
        (recB h.toLawsCore).Mlat j w := by
    intro w k h1 h2
    obtain ⟨e, a, b⟩ := _root_.GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum D (recB h.toLawsCore) hinj EX j wL wF w k h1 h2
    refine _root_.GlobalTheory.PlaceTop.thc_le_of_shortBound _root_.GlobalTheory.ShortBound.shortBound D T h hs j hj hinj EX ho w _ _ _ a b ?_
    rw [hp, e]
    exact congrArg (· * _) (mul_assoc _ _ _)
  refine ⟨GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX ho wL, ?_, ?_, ?_⟩
  · refine _root_.GlobalTheory.PlaceTop.thc_le_of_shortBound _root_.GlobalTheory.ShortBound.shortBound D T h hs j hj hinj EX ho wF _ _ _ le_rfl le_rfl ?_
    rw [hp]
    rfl
  · exact key (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) (WeightFamilies.dimY D j) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key ka T₀ (fun τ i => by have := hF.2.1 τ i; zify; linarith)
      (fun τ i => by have := hF.2.2 τ i; zify; linarith)

theorem scaledRunLatticesInSupLattices_proof : ScaledLatticesInSupLattices := by
  intro D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  have H := integralityCondition_algebraicPoints D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  exact ⟨H, fun n => integralityCondition_of_addedPoints_secondNorm n _ _ _ _ ka wL wF H⟩

end GlobalTheory.PlaceTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShortChange

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem trivAt_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {Λ : GenLat E n} {a b : ℕ}
    (ha : Λ.TrivAt a) (hb : Λ.TrivAt b) : Λ.TrivAt (a * b) := by
  obtain ⟨k, hk, h1, h2⟩ := ha
  obtain ⟨m, hm, h3, h4⟩ := hb
  have hg : Ideal.span {((Nat.gcd k m : ℕ) : 𝓞 E)} ≤ Ideal.span {(k : 𝓞 E)} ⊔ Ideal.span {(m : 𝓞 E)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : ((Nat.gcd k m : ℕ) : 𝓞 E) = (k : 𝓞 E) * (Nat.gcdA k m : ℤ) + (m : 𝓞 E) * (Nat.gcdB k m : ℤ) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) (Nat.gcd_eq_gcd_ab k m)
      push_cast at this
      exact this
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨Nat.gcd k m, (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _)).mul_right
    (hm.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h1 h3
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h2 h4

theorem badOK_host (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) :
    BadOK l (D.host.QS * D.host.q * D.host.d * l.M) := by
  have hqd := D.host.qd_big
  have hM := l.three_le
  refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (by omega),
    D.host.toHostRaw.two_dvd_condN.mul_right _, Dvd.intro_left _ rfl, fun p hp h => ?_⟩
  exact dvd_mul_of_dvd_left (D.host.der.discr_primes.1 p hp h) _

theorem odd_rank {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) :
    Odd ((T.Q.Dw j).p + (T.Q.Dw j).q) := by
  obtain ⟨h1, h2, -⟩ := hF.p.toLawsCore.pins.2.2.2 j hj
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  obtain ⟨hj1, hj2⟩ := hj
  rw [h1, h2]
  exact ⟨a + b - 1, by unfold Ranks.sigW; dsimp only; omega⟩

end GlobalTheory.ShortChange
end

