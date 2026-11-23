module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0270
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0217
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0269
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0268

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompact
section
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := pb_builtBounds2Cpt_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem isBoundedBilinearMap_compR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => q.1.comp q.2) :=
  ((ContinuousLinearMap.compL ℂ Wq Wq Wp).bilinearRestrictScalars ℝ).isBoundedBilinearMap


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_comp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    {A : B.Mat k r → (Wq →L[ℂ] Wq)} (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, A1, hU2, h2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (A1 g), hU1.inter hU2, ⟨h1, h2⟩, ?_, ?_⟩
  · exact isBoundedBilinearMap_compR.contDiff.comp_contDiffOn
      ((hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right))
  · intro x hx hxG
    simp only [he1 x hx.1 hxG, he2 x hx.2 hxG]

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

section fpm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end fpm

def LimE (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
      (𝓝 (sz * (B.beta p.T.base F F).re))

def LemB (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (κ₀ : ℝ) : Prop :=
  ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F

def Amaps (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ : ℕ) : Prop :=
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)

def BigCellDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
    ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
    (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
    (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
    ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
        ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrpFinal
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_right_group_action : RDSOpRGrp := rDSOpRGrp_of_nice spectral_nice_polynomial

theorem spectral_adjoint_right_group : RDSOpRvGrp := rDSOpRvGrp_of_nice spectral_nice_polynomial

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPairDone
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_identity : RDSPair :=
  rDSPair_of_cut spectral_pairing_inner_swap spectral_pairing_big_cell spectral_pairing_zero_right spectral_pairing_exhaustion spectral_pairing_orbital_membership spectral_pairing_operator
    spectral_pairing_locality

end Formalism.FourierDecayAlt.P.CutSE
end

