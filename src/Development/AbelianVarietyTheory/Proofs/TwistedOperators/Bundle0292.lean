module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelParsevalThetaInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixParseval


set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem parseval : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → Continuous (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∧ Integrable (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') μ ∧ ∫ w in 𝓕₀, f₁ w * starRingEnd ℂ (f₂ w) ∂μ₀ = ∫ u : Mx D W.rank r, (∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μ₀ 𝓕₀ hμ₀ μ' 𝓕' hμ' f₁ f₂ hf₁ hf₂
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, hμ'.2.2]; exact ENNReal.one_lt_top⟩
  let R : (WO V W → ℂ) → WO V' W → Mx D W.rank r → ℂ := fun f x u =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x
  let h : WO V' W → Mx D W.rank r → ℂ := fun x u => R f₁ x u * starRingEnd ℂ (R f₂ x u)
  obtain ⟨hc₁, M₁, hM₁⟩ := _root_.GlobalTheory.IndefiniteRowSideFullHecke.ResCont.res_heisO_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₁ hf₁
  obtain ⟨hc₂, M₂, hM₂⟩ := _root_.GlobalTheory.IndefiniteRowSideFullHecke.ResCont.res_heisO_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₂ hf₂
  have hhc : Continuous (Function.uncurry h) := hc₁.mul (Complex.continuous_conj.comp hc₂)
  have hhb : ∀ x u, ‖h x u‖ ≤ M₁ * M₂ := fun x u => by
    show ‖R f₁ x u * starRingEnd ℂ (R f₂ x u)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM₁ x u) (hM₂ x u) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x u))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₂
  have hYr : μ.real 𝓨 = 1 := by simp [Measure.real, hμ.2.2]
  have hsq : ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ Cf : ℝ, (∀ w, ‖f w‖ ≤ Cf) → ∀ x u,
      Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 ≤ Cf ^ 2 := by
    intro f hf Cf hCf x u
    obtain ⟨hs1, hs2⟩ := _root_.GlobalTheory.MixParsevalPoint.parseval_point D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f f hf hf x u
    have e : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        ‖R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u))‖ = ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      fun ξ => by rw [norm_mul, Complex.norm_conj, sq]
    have hsum : Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) :=
      hs1.congr e
    refine ⟨hsum, ?_⟩
    have e2 : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u)) =
          ((‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hI := hs2.tsum_eq
    have hI' : ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) =
        ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ := by
      rw [Complex.ofReal_tsum, ← hI]
      exact tsum_congr fun ξ => (e2 ξ).symm
    have hnn : 0 ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      tsum_nonneg fun _ => by positivity
    have hb : ∀ w, ‖f w * starRingEnd ℂ (f w)‖ ≤ Cf ^ 2 := fun w => by
      rw [norm_mul, Complex.norm_conj, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCf w) 2
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2
        = ‖((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ Cf ^ 2 * (μ.restrict 𝓨).real Set.univ := by
          rw [hI']
          exact norm_integral_le_of_norm_le_const (.of_forall fun y => hb _)
      _ = Cf ^ 2 := by simp [Measure.real, Measure.restrict_apply_univ, hμ.2.2]
  have hb : ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by
    intro x u
    obtain ⟨s1, t1⟩ := hsq f₁ hf₁ C₁ hC₁ x u
    obtain ⟨s2, t2⟩ := hsq f₂ hf₂ C₂ hC₂ x u
    have hle : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤
        (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := fun ξ => by
      show ‖R f₁ x (ξ.map (incA D) + u) * starRingEnd ℂ (R f₂ x (ξ.map (incA D) + u))‖ ≤ _
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖R f₁ x (ξ.map (incA D) + u)‖ - ‖R f₂ x (ξ.map (incA D) + u)‖)]
    have hs' := (s1.add s2).div_const 2
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖
        ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
            (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs').tsum_le_tsum hle hs'
      _ = ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2) +
            ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := by
          rw [tsum_div_const, s1.tsum_add s2]
      _ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by linarith
  obtain ⟨hint, hEq⟩ := _root_.GlobalTheory.UnfoldRat.unfold D W.rank r (WO V' W) (μ'.restrict 𝓕') μ 𝓨 hμ h hhc _ hb
  have a1 : ∀ x, Continuous (h x) := fun x => hhc.uncurry_left x
  have a2 : ∀ u, Continuous (fun x => h x u) := fun u => hhc.uncurry_right u
  have a3 : ∀ u, AEStronglyMeasurable (fun x => h x u) (μ'.restrict 𝓕') := fun u => (a2 u).aestronglyMeasurable
  haveI : FirstCountableTopology (Mx D W.rank r) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hG : Continuous (fun u => ∫ x, h x u ∂(μ'.restrict 𝓕')) :=
    continuous_of_dominated (bound := fun _ => M₁ * M₂) a3
      (fun u => .of_forall fun x => hhb x u) (integrable_const _) (.of_forall a1)
  refine ⟨hG, hint, ?_⟩
  show _ = ∫ u, (∫ x, h x u ∂(μ'.restrict 𝓕')) ∂μ
  rw [hEq]
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hμ
    μ₀ 𝓕₀ hμ₀.1 hμ₀.2.1 μ' 𝓕' hμ'.1 hμ'.2.1
  have hκ1 : κ = 1 := by
    have e := hκ (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ (fun _ _ _ => rfl)
    simp only [setIntegral_const, Measure.real, hμ₀.2.2, hμ.2.2, hμ'.2.2, ENNReal.toReal_one, one_smul] at e
    rw [Complex.real_smul, mul_one] at e
    exact_mod_cast e.symm
  let H : WO V W → ℂ := fun w => f₁ w * starRingEnd ℂ (f₂ w)
  have hHc : Continuous H := hf₁.cont.mul (Complex.continuous_conj.comp hf₂.cont)
  have hHb : ∃ b : ℝ, ∀ w, ‖H w‖ ≤ b := ⟨C₁ * C₂, fun w => by
    show ‖f₁ w * starRingEnd ℂ (f₂ w)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ w) (hC₂ w) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ w))⟩
  have hHp : ∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w := by
    rintro γ ⟨g, rfl⟩ w
    show f₁ (ratW W V g + w) * starRingEnd ℂ (f₂ (ratW W V g + w)) = f₁ w * starRingEnd ℂ (f₂ w)
    rw [hf₁.quasi g w, hf₂.quasi g w, map_mul]
    have hu : ∀ a, ψ a * starRingEnd ℂ (ψ a) = 1 := fun a => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1]; norm_num
    calc ψ (-symplOH V W (ratW W V g) w) * f₁ w * (starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w)) * starRingEnd ℂ (f₂ w))
        = (ψ (-symplOH V W (ratW W V g) w) * starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w))) *
            (f₁ w * starRingEnd ℂ (f₂ w)) := by ring
      _ = _ := by rw [hu, one_mul]
  show ∫ w in 𝓕₀, H w ∂μ₀ = _
  rw [hκ H hHc hHb hHp, hκ1, one_smul]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have hInt : Integrable (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := by
    obtain ⟨b, hb'⟩ := hHb
    have hcont : Continuous (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) :=
      hHc.comp ((continuous_const.add ((continuous_fst).matrix_mul continuous_const)).add
        ((continuous_snd).matrix_mul continuous_const))
    exact Integrable.of_bound hcont.aestronglyMeasurable b (.of_forall fun p => hb' _)
  show ∫ y, ∫ x, H _ ∂(μ'.restrict 𝓕') ∂(μ.restrict 𝓨) = _
  haveI : SFinite (μ'.restrict 𝓕') := instSFiniteOfSigmaFinite
  haveI : SFinite (μ.restrict 𝓨) := instSFiniteOfSigmaFinite
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hp := (_root_.GlobalTheory.MixParsevalPoint.parseval_point D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f₁ f₂ hf₁ hf₂ x t).2
  refine Eq.trans ?_ hp.tsum_eq.symm
  refine integral_congr_ae (.of_forall fun y => ?_)
  show H _ = H _
  congr 1
  abel

end GlobalTheory.MixParseval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaTermsSummableHeightBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev supWord (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (k : ℕ) (G : WO V W → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G

theorem enorm_real_cast {a : ℝ} (h : 0 ≤ a) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg h]

def opAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  G - (((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) • derAlong ψ θ V W C x (derAlong ψ θ V W C x G)

theorem theta_derAlong {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : IsThetaFunO ψ V W (derAlong ψ θ V W C x G) := by
  obtain ⟨U, -, hU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hG
  unfold derAlong
  exact GlobalTheory.Size.theta_finsetSum Finset.univ fun τ _ => (GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hU τ _).1

theorem theta_sub_smul {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {G H : WO V W → ℂ} (c : ℂ)
    (hG : IsThetaFunO ψ V W G) (hH : IsThetaFunO ψ V W H) : IsThetaFunO ψ V W (G - c • H) := by
  have h := GlobalTheory.OrientedHeis.theta_add hG (GlobalTheory.OrientedHeis.theta_smul (-c) hH)
  rwa [neg_smul, ← sub_eq_add_neg] at h

theorem term_opAlong {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (x y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C x G) y =
      ((1 + ratPair W y x ^ 2 : ℝ) : ℂ) * term ψ V V' W C C' B μ 𝓨 G y := by
  have hG1 := theta_derAlong hψ hθ C x hG
  have hG2 := theta_derAlong hψ hθ C x hG1
  obtain ⟨hadd, hsmul⟩ := _root_.GlobalTheory.MixedTerm.term_linear D V V' W r C C' B ψ hψ μ 𝓨 hμ y
  have e1 := _root_.GlobalTheory.MixedTerm.DerLaw.term_derAlong D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ G hG x y
  have e2 := _root_.GlobalTheory.MixedTerm.DerLaw.term_derAlong D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ _ hG1 x y
  have hsplit : opAlong ψ θ V W C x G = G + (-(((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) •
      derAlong ψ θ V W C x (derAlong ψ θ V W C x G) := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  rw [hsplit, hadd _ _ hG (GlobalTheory.OrientedHeis.theta_smul _ hG2), hsmul _ _ hG2, e2, e1]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (4 * (Real.pi : ℂ) ^ 2)⁻¹ * (4 * (Real.pi : ℂ) ^ 2) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ))
  push_cast
  linear_combination (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y * Complex.I ^ 2) * hc +
    (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y) * Complex.I_sq

theorem term_decay {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    (l : List (Matrix (Fin W.rank) (Fin r) D.host.E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ y,
      ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod ≤
        ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) G := by
  induction l with
  | nil =>
    refine ⟨1, zero_le_one, fun G _ y => ?_⟩
    simp only [List.map_nil, List.prod_nil, mul_one, ENNReal.ofReal_one, one_mul, List.length_nil,
      mul_zero]
    unfold supWord
    rw [GlobalTheory.Size.wordSum_zero]
    exact _root_.GlobalTheory.MixedTerm.enorm_term_le_iSup D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  | cons a l ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨hsub, hder⟩ := _root_.GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong D V W ψ hψ θ hθ
    obtain ⟨c₀, hc₀, hd⟩ := hder r C a
    have he0 : (0 : ℝ) ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
    refine ⟨K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀), by positivity, fun G hG y => ?_⟩
    have hG1 := theta_derAlong hψ hθ C a hG
    have hG2 := theta_derAlong hψ hθ C a hG1
    have hop : IsThetaFunO ψ V W (opAlong ψ θ V W C a G) :=
      theta_sub_smul ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) hG hG2
    have hp : (0 : ℝ) ≤ 1 + ratPair W y a ^ 2 := by positivity
    have hterm : ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ =
        ENNReal.ofReal (1 + ratPair W y a ^ 2) * ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ := by
      rw [term_opAlong hs h1 hψ hθ hμ hG a y, enorm_mul, enorm_real_cast hp]
    have hlen : 2 * (a :: l).length = 2 * l.length + 1 + 1 := by
      simp only [List.length_cons]
      ring
    have hsize : supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) ≤
        ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * (a :: l).length) G := by
      rw [hlen]
      have s1 := hsub G _ ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) (2 * l.length) hG hG2
      have s2 := hd _ hG1 (2 * l.length)
      have s3 := hd G hG (2 * l.length + 1)
      have s4 := GlobalTheory.Size.wordSum_mono (A := GlobalTheory.Size.heisDer ψ θ)
        (p := fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (show 2 * l.length ≤ 2 * l.length + 1 + 1 by omega) G
      rw [enorm_real_cast he0] at s1
      calc supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G)
          ≤ supWord ψ θ V W (2 * l.length) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              supWord ψ θ V W (2 * l.length) (derAlong ψ θ V W C a (derAlong ψ θ V W C a G)) := s1
        _ ≤ supWord ψ θ V W (2 * l.length + 1 + 1) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              (ENNReal.ofReal c₀ * (ENNReal.ofReal c₀ * supWord ψ θ V W (2 * l.length + 1 + 1) G)) := by
            gcongr
            exact s2.trans (by gcongr)
        _ = ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * l.length + 1 + 1) G := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul he0]
            ring
    rw [List.map_cons, List.prod_cons]
    calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (ENNReal.ofReal (1 + ratPair W y a ^ 2) *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod)
        = ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod := by
          rw [hterm]
          ring
      _ ≤ ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) := hb _ hop y
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) *
          supWord ψ θ V W (2 * (a :: l).length) G) := by gcongr
      _ = ENNReal.ofReal (K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀)) *
          supWord ψ θ V W (2 * (a :: l).length) G := by
          rw [ENNReal.ofReal_mul hK]
          ring

theorem mixed_terms_bound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  intro D V V' W r C C' B hs h1 _ _ ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨e, he⟩ := _root_.GlobalTheory.MixedTermIntegral.integral D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨n, X, hXint, hXsep⟩ := _root_.GlobalTheory.RatPairSep.main D W r
  obtain ⟨K₀, hK₀, hdec⟩ := term_decay hs h1 hψ hθ hμ (List.ofFn X)
  refine ⟨2 * e * n, 2 * n, fun U hU => ?_⟩
  obtain ⟨M, _, hN⟩ := he U hU
  refine ⟨K₀ * (5 * (M : ℝ) ^ 2) ^ n, fun g h F hF hfix => ?_⟩
  obtain ⟨N, hNpos, hNle, hint⟩ := hN g h
  have hg1 := (GlobalTheory.Size.height_laws V).1 g
  have hh1 := (GlobalTheory.Size.height_laws W).1 h
  have ht0 : (0 : ℝ) ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (by linarith) (by linarith)
  have hbound := GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay (Y := Matrix (Fin W.rank) (Fin r) D.host.E) n N hNpos
    (fun y => ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ) (fun j y => ratPair W y (X j))
    (fun y y' _ _ hyy => hXsep y y' hyy)
    (fun y hy j => hint F hF hfix y (enorm_ne_zero.mp hy) (X j) (hXint j))
    (ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F)
    (fun y => by
      have hy := hdec F hF y
      rw [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hy
      exact hy)
  have hNM : (5 * (N : ℝ) ^ 2) ^ n ≤
      (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by
    calc (5 * (N : ℝ) ^ 2) ^ n
        ≤ (5 * ((M : ℝ) * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e) ^ 2) ^ n := by gcongr
      _ = (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by ring
  show ∑' y, ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ ≤ _
  refine hbound.trans ?_
  calc ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n)
      ≤ ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (M : ℝ) ^ 2) ^ n *
          (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) := by gcongr
    _ = ENNReal.ofReal (K₀ * (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) *
          supWord ψ θ V W (2 * n) F := by
        rw [mul_assoc K₀, ENNReal.ofReal_mul hK₀]
        ring

end GlobalTheory.MixedTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegrals
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrClassTerm

theorem integrable_descend_of_stdDom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} {φ : G → ℂ} (hi : LeftInv Γ φ) (h : IntegrableOn φ (stdDom Γ) μ) :
    Integrable (descend Γ φ) (quotMeasure Γ μ) ∧
      ∫ q, descend Γ φ q ∂quotMeasure Γ μ = ∫ x in stdDom Γ, φ x ∂μ := by
  have e : descend Γ φ = φ ∘ sec Γ := funext fun q => by
    rw [Function.comp_apply, ← hi.descend_mk, mk_sec]
  rw [e]
  exact ⟨(measurePreserving_sec.integrable_comp_emb measurableEmbedding_sec).2 h,
    measurePreserving_sec.integral_comp measurableEmbedding_sec φ⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_tensor {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    Continuous (tensor σ J fa ff) ∧ HasCompactSupport (tensor σ J fa ff) := by
  have hb := hf.tensorFin_mem
  have h1 : Continuous (tensorInf σ J fa) :=
    continuous_finsetProd _ fun w _ => (ha w).1.comp (continuous_projInfArch σ J w)
  have h2 : HasCompactSupport (tensorInf σ J fa) := by
    refine .intro ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_univ_pi fun w => (ha w).2)) fun g hg => ?_
    by_contra hne
    exact hg fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne w (Finset.mem_univ w))
  rw [tensor_eq_infFin]
  refine ⟨(h1.comp (continuous_projInf σ J)).mul (hb.1.continuous.comp (continuous_projFin σ J)), .intro
    ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod h2 hb.2)) fun g hg => ?_⟩
  by_contra hne
  exact hg ⟨subset_tsupport _ (left_ne_zero_of_mul hne), subset_tsupport _ (right_ne_zero_of_mul hne)⟩

theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) : IsMulCommutative (cent (ratEmb σ J γ)) :=
  ⟨⟨fun a b => Subtype.ext (GAd_ext σ J
    (fun w => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).1.1
          (centMap (projArch σ J w) _ a) (centMap (projArch σ J w) _ b)))
    fun v => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).1.1
          (centMap (proj σ J v) _ a) (centMap (proj σ J v) _ b)))⟩⟩

theorem class_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
  have hreg : IsRegSS γ.1.1 := by
    rw [IsRegSS, hγ]; exact P.2.2.1.separable
  obtain ⟨ea, ef, e, hc, ⟨𝓣, h𝓣, hvol⟩, hf, ha⟩ := _root_.GlobalTheory.TrEllMeas.exists_isCentProd_torus F E σ hcm r P J hJ L γ hγ dta dtf dt hdt
  obtain ⟨pf, pa⟩ := GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ
  have := hμ.haar
  have := hc.1
  have := hc.2.1
  have := hc.2.2.1
  have : ∀ w, (ea w).IsMulRightInvariant := fun w =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have : ∀ v, (ef v).IsMulRightInvariant := fun v =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hf' : ∀ v, HasOrbInt (μf v) (proj σ J v (ratEmb σ J γ)) (ef v) (ff v) (orbCls (μf v) (dtf v) (ff v) (qf v)) :=
    fun v => by
      obtain ⟨x, φ, h, e1, e2⟩ := hqf v
      have := (pf v (μf v) (dtf v) (ff v) (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) (hff.1 v).1.continuous
        (hff.1 v).2).2 x φ h
      rw [show qf v = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
      exact (hf v x φ h e2 _ _ _).1 this
  have ha' : ∀ w, HasOrbInt (μa w) (projArch σ J w (ratEmb σ J γ)) (ea w) (fa w)
      (orbCls (μa w) (dta w) (fa w) (qa w)) := fun w => by
    obtain ⟨x, φ, h, e1, e2⟩ := hqa w
    have := (pa w (μa w) (dta w) (fa w) (hμ.haar_arch w) (IsRestrictedProd.haar_arch hdt w) (hfa w).1
      (hfa w).2).2 x φ h
    rw [show qa w = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
    exact (ha w x φ h e2 _ _ _).1 this
  have hO := (hasOrbInt_tensor_of_hasOrbInt hμ hc hff.2 (eventually_conj_mem_stabLoc hcm hJ L hreg) ha' hf').2
  have hfin := (_root_.GlobalTheory.TorCompact.torus_compact_finiteVol F E σ hcm r P).2 dt (IsRestrictedProd.haar hdt)
  have ht := continuous_tensor hfa hff
  obtain ⟨-, h1, h2⟩ := _root_.GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt (GAd σ J) (ratPts σ J) (ratEmb σ J γ) (range_ratEmb σ J ▸ ⟨γ, rfl⟩)
    (isMulCommutative_cent_ratEmb hreg) μ e 𝓣 h𝓣 (hvol ▸ hfin.lt_top) _ _ ht.1 ht.2 hO _
    (isFundamentalDomain_stdDom _ μ)
  obtain ⟨h3, h4⟩ := integrable_descend_of_stdDom
    (fun g hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul (ratEmb σ J γ) (tensor σ J fa ff) hg x) h1
  refine ⟨h3, ?_⟩
  rw [h4, h2, Measure.real, hvol, mul_comm (∏ w, _)]

end GlobalTheory.TrClassTerm
end
end

