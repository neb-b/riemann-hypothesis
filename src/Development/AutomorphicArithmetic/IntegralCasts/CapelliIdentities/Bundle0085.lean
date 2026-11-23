module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
public import GroundTheory.AutomorphicForms.ReductionMahler
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import GroundTheory.AutomorphicForms.Reduction
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsXTranslate
section
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem UpperTheory.Reformulated.B.Gul4.lev_top :
    Lev (fun w : Pl K => (GLnLocal.integralGL (w.adicCompletion K) n : Subgroup (Gw n w))) := fun w =>
  ⟨⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩, le_rfl⟩

private theorem UpperTheory.Reformulated.B.Gul4.mem_iff (μ : Measure (G1 K n)) (τ : Submodule ℂ (L2 μ))
    (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (hp : IdemA κ p) (hμ : μ.IsHaarMeasure)
    (S : Finset (Pl K)) (φ : G1 K n → ℂ) : φ ∈ Xs μ τ κ p S ↔ IsX μ τ κ p S φ := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  obtain ⟨-, hinf, -, harc, hcpt, -⟩ := levLaws (K := K) n S
  have hq := RightCosetSpace.quasiMeasurePreserving_mk (Gam K n) μ
  have := hp.haar.prob
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨continuous_const, ⟨0, τ.zero_mem, ?_⟩, fun g => by simp, _, UpperTheory.Reformulated.B.Gul4.lev_top, fun u _ g => rfl⟩
    exact MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_zero ℂ 2 _)
  | add x y _ _ hx hy =>
    obtain ⟨cx, ⟨v, hv, rv⟩, ax, U, hU, fx⟩ := hx
    obtain ⟨cy, ⟨v', hv', rv'⟩, ay, U', hU', fy⟩ := hy
    obtain ⟨hL, hE⟩ := hinf U U' hU hU'
    refine ⟨cx.add cy, ⟨v + v', τ.add_mem hv hv', ?_⟩, UpperTheory.mean_value_uniqueness κ arc1 p harc hp.cont x y cx cy ax ay,
      _, hL, fun u hu g => ?_⟩
    · filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_add v v'), rv, rv'] with z h1 h2 h3
      rw [Pi.add_apply, ← h2, ← h3]
      exact h1
    · rw [hE] at hu
      rw [Pi.add_apply, Pi.add_apply, fx u hu.1, fy u hu.2]
  | smul c x _ hx =>
    obtain ⟨cx, ⟨v, hv, rv⟩, ax, U, hU, fx⟩ := hx
    refine ⟨cx.const_smul c, ⟨c • v, τ.smul_mem c hv, ?_⟩, fun g => ?_, U, hU, fun u hu g => ?_⟩
    · filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_smul c v), rv] with z h1 h2
      rw [Pi.smul_apply, ← h2]
      exact h1
    · rw [Pi.smul_apply, ← ax g, smul_eq_mul, ← integral_const_mul]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    · rw [Pi.smul_apply, Pi.smul_apply, fx u hu]

private theorem UpperTheory.Reformulated.B.Gul4.isX_translate (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ))
    (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (hτ : CuspIrr μ τ)
    {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n) (hw : Function.Injective w) (hι : IsEmb w ι)
    (φ : G1 K n → ℂ) (hφ : IsX μ τ κ p (im w) φ) (g : GS n w) :
    IsX μ τ κ p (im w) fun x => φ (x * fin1 (ι g)) := by
  obtain ⟨-, -, hcomm, -, -, hconj⟩ := levLaws (K := K) n (im w)
  obtain ⟨cφ, ⟨v, hv, rv⟩, aφ, U, hU, fφ⟩ := hφ
  obtain ⟨U', hU', hc⟩ := hconj w ι hw hι rfl U hU g
  obtain ⟨-, -, -, hst, -⟩ := hτ
  refine ⟨cφ.comp (continuous_id.mul continuous_const), ⟨_, hst (fin1 (ι g)) v hv, ?_⟩, fun x => ?_, U', hU',
    fun u hu x => ?_⟩
  · exact UpperTheory.ae_translate_eq μ _ (RightCosetSpace.mk (Gam K n)) (RightCosetSpace.rightMul (Gam K n) (fin1 (ι g))) _ v _ φ
      (RightCosetSpace.quasiMeasurePreserving_mk (Gam K n) μ) (fun y => RightCosetSpace.rightMul_mk _ _)
      (RightCosetSpace.coeFn_rightRegularRep (Gam K n) μ _ v) rv
  · beta_reduce
    rw [← aφ (x * fin1 (ι g))]
    simp only [mul_assoc, fun k => (hcomm k (ι g)).eq]
  · have h := fφ _ (hc u hu) (x * fin1 (ι g))
    beta_reduce
    rw [← h]
    simp only [fin1, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]

end

theorem UpperTheory.Reformulated.B.Gul4.xMem :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [NumberField.IsTotallyComplex K]
      (μ : MeasureTheory.Measure (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ))) [inst_3 : μ.IsHaarMeasure]
      (τ : Submodule ℂ (PositivityTheory.Rg.Tf.Core.L2 μ))
      (κ : MeasureTheory.Measure ↥(GroundTheory.Automorphic.AutomorphicForm.archCompact K (2 : ℕ)))
      (p : ↥(GroundTheory.Automorphic.AutomorphicForm.archCompact K (2 : ℕ)) → ℂ),
      UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IdemA κ p →
        (∀ (S : Finset (UpperTheory.ConvolutionTheory.Pl K)) (φ : PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ),
            φ ∈ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p S ↔ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IsX μ τ κ p S φ) ∧
          (PositivityTheory.Rg.Tf.Adel.CuspIrr μ τ →
            ∀ {r : ℕ} (w : Fin r → UpperTheory.ConvolutionTheory.Pl K) (ι : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →* UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.FA K (2 : ℕ)),
              Function.Injective w →
                UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IsEmb w ι →
                  ∀ φ ∈ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.im w),
                    IsOpen
                        {g : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w |
                          ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.rS ι :
                                          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →
                                            (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) →ₗ[ℂ] PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                                        g :
                                (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) → PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                              φ =
                            φ} ∧
                      ∀ (g : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w),
                        ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.rS ι :
                                        UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →
                                          (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) →ₗ[ℂ] PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                                      g :
                              (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) → PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                            φ ∈
                          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.im w)) := by
  intro K _ _ _ μ hμ τ κ p hp
  refine ⟨UpperTheory.Reformulated.B.Gul4.mem_iff μ τ κ p hp hμ, fun hτ r w ι hw hι φ hφ => ?_⟩
  rw [UpperTheory.Reformulated.B.Gul4.mem_iff μ τ κ p hp hμ] at hφ
  refine ⟨?_, fun g => Submodule.subset_span (UpperTheory.Reformulated.B.Gul4.isX_translate μ τ κ p hτ w ι hw hι φ hφ g)⟩
  obtain ⟨-, -, -, U, hU, fφ⟩ := hφ
  exact UpperTheory.isOpen_right_invariance ι (GroundTheory.Automorphic.MultiplicityOne.finProj K 2) _ φ
    ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.embEx 2 w hw).2 ι hι).1 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws 2 _).1 U hU).1.2 fφ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsSmul
section
open MeasureTheory GroundTheory.Automorphic

private theorem UpperTheory.Reformulated.B.Glb3.ae_pull {G : Type} [Group G] (Γ : Subgroup G) [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [DiscreteTopology ↥Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (p : RightCosetSpace Γ → Prop)
    (hp : ∀ᵐ q ∂(RightCosetSpace.quotientMeasure Γ μ), p q) :
    ∀ᵐ y ∂μ, p (RightCosetSpace.mk Γ y) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine UpperTheory.ae_fundamental_domain Γ μ (RightCosetSpace.fundamentalDomain Γ) (RightCosetSpace.mk Γ)
    measurable_quotient_mk'' (fun γ g => Quotient.sound ⟨γ, rfl⟩) (fun g => ?_) p hp
  exact (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain Γ g).exists

private theorem UpperTheory.Reformulated.B.Glb3.reps_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (μ : Measure (PositivityTheory.Rg.Tf.Core.G1 K n)) [μ.IsHaarMeasure] (v : PositivityTheory.Rg.Tf.Core.L2 μ)
    (φ : PositivityTheory.Rg.Tf.Core.G1 K n → ℂ) (c : ℂ) (h : PositivityTheory.Rg.Tf.Adel.Reps μ v φ) :
    PositivityTheory.Rg.Tf.Adel.Reps μ (c • v) (c • φ) := by
  have h1 := UpperTheory.Reformulated.B.Glb3.ae_pull (PositivityTheory.Rg.Tf.Core.Gam K n) μ _ (Lp.coeFn_smul c v)
  filter_upwards [h, h1] with y hy hy1
  exact hy1.trans (congrArg (c • ·) hy)

theorem UpperTheory.Reformulated.B.Glb3.sec_add :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {μ₂ : MeasureTheory.Measure (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ))}
      [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (PositivityTheory.Rg.Tf.Core.L2 μ₂)}
      {f f' : PositivityTheory.Rg.Tf.Core.G1 K ((2 : ℕ) + (2 : ℕ)) → ℂ},
      PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f →
        PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f' → ∀ (c : ℂ), PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ (f + c • f') := by
  intro K _ _ μ _ τ₁ τ₂ f f' hf hf' c
  obtain ⟨h1, ⟨C, h2⟩, h3, h4, h5⟩ := hf
  obtain ⟨h1', ⟨C', h2'⟩, h3', h4', h5'⟩ := hf'
  refine ⟨h1.add (h1'.const_smul c), ⟨C + ‖c‖ * C', fun g => ?_⟩, fun X g => ?_,
    fun r x g hx => ?_, fun g => ?_⟩
  · refine (norm_add_le (f g) (c • f' g)).trans (add_le_add (h2 g) ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h2' g) (norm_nonneg c)
  · simp only [Pi.add_apply, Pi.smul_apply, h3 X g, h3' X g]
  · simp only [Pi.add_apply, Pi.smul_apply, h4 r x g hx, h4' r x g hx]
  · obtain ⟨d, φ, ψ, hφ, hψ, hs⟩ := h5 g
    obtain ⟨d', φ', ψ', hφ', hψ', hs'⟩ := h5' g
    refine ⟨d + d', Fin.append φ (fun i => c • φ' i), Fin.append ψ ψ', fun i => ?_, fun i => ?_,
      fun m₁ m₂ x hx => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hφ j
      · rw [Fin.append_right]
        obtain ⟨hc, v, hv, hr⟩ := hφ' j
        exact ⟨hc.const_smul c, c • v, τ₁.smul_mem c hv, UpperTheory.Reformulated.B.Glb3.reps_smul μ v _ c hr⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hψ j
      · rw [Fin.append_right]; exact hψ' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hs m₁ m₂ x hx, hs' m₁ m₂ x hx, Finset.mul_sum, mul_assoc]
end

