module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwSummand
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.FamScalar
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical InnerProductSpace ComplexOrder

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famScalar :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
          ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
          ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d) (𝔞 : Amp μ) (φ : TF K (2 + 2)) (c : ℂ) (β : ℝ → Eu d →L[ℂ] Eu d), 𝔞.U = levOn S U →
          (∀ x, φ x = (levOn S U : Set (FA K (2 + 2))).indicator 1 x) → c ≠ 0 → Rop μ (c • tens 𝔞.a₀ φ) = 𝔞.A → ActsBy μ A (c • tens 𝔞.a₀ φ) β →
          (∃ v g, ∫ y, 𝔞.a₀ y * flat 0 (A.sec v) (g * archP K (2 + 2) y) ∂𝔞.ν ≠ 0) → 0 < d ∧ ∃ x : ℝ, 0 < x ∧ symb β 0 = (x : ℂ) • (1 : Eu d →L[ℂ] Eu d) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A 𝔞 φ c β hU hφ hc hR hA hne
  obtain ⟨v₀, g₀, hI⟩ := hne
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hflat0 : ∀ x, flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := fun x => by simp [flat]
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      apply hI
      rw [show v₀ = 0 from Subsingleton.elim _ _, map_zero]
      simp only [hflat0, mul_zero, integral_zero]
    · exact h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨h0, h1, -⟩ := UpperTheory.ConvolutionTheory.evEx K (2 + 2) (by norm_num) μ 𝔞
  have hpos := (posSymb A.J 𝔞.A β hA.1 (hR ▸ hA.2.1) h0 h1).1
  have hcomm : ∀ h M, HeckeAt A (levOn S U) h M → Commute M (symb β 0 : Eu d →ₗ[ℂ] Eu d) := by
    have hA' : ActsBy μ A (tens (c • 𝔞.a₀) φ) β := by
      rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K (2 + 2) (by norm_num) 𝔞.a₀ φ).2.2.2.2 c).1]
      exact hA
    exact (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hL.idem S U hLev D hD d A).2.2 _ φ β hφ hA'
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (symb β 0 : Eu d →ₗ[ℂ] Eu d)
  have hE : Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l = ⊤ := by
    refine (irrW K μ μ₂ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A _ fun w _ g M hM v hv => ?_).resolve_left hl
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := LinearMap.congr_fun (hcomm _ M hM).eq v
    simp only [Module.End.mul_apply] at h
    rw [← h, hv, map_smul]
  have hT : ∀ v, symb β 0 v = l • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top : v ∈ Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l)
  have hl0 : 0 ≤ l := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Eu d)
    have hp := ContinuousLinearMap.nonneg_iff_isPositive.1 hpos
    have h2 := hp.inner_nonneg_right v
    rw [hT, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
    have h3 : 0 ≤ l * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h2
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h3
    rw [Complex.re_mul_ofReal] at a
    rw [Complex.im_mul_ofReal] at b
    refine Complex.nonneg_iff.2 ⟨le_of_mul_le_mul_right (by simpa using a) hn, ?_⟩
    exact ((mul_eq_zero.1 (by simpa using b.symm)).resolve_right hn.ne').symm
  have hlne : l ≠ 0 := by
    rintro rfl
    obtain ⟨⟨c', hc', hint, -⟩, -⟩ := tensAmp K (2 + 2) (by norm_num) μ 𝔞 φ (fun x => by rw [hφ, hU])
    have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hpSpec.2.2.2.1))
    have hΘ : Continuous (flat 0 (A.sec v₀)) := hH.mul (hsec v₀).1.cont
    have hfix : FixF 𝔞.U (flat 0 (A.sec v₀)) := by
      refine (((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr μ₂ τ₁ τ₂ κ e hL.idem).2.1 _ (hsec v₀).1.cont).2 𝔞.U 𝔞.le).2 ?_
      rw [hU]
      exact ((hD.fix _ (hsec v₀).1.cont).1 (hsec v₀).2).2
    have e1 := hA.2.2 0 v₀ g₀
    rw [hT, zero_smul, map_zero, hflat0] at e1
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_assoc] at e1
    rw [integral_const_mul, hint _ hΘ hfix g₀] at e1
    exact mul_ne_zero hc (mul_ne_zero (Complex.ofReal_ne_zero.2 hc'.ne') hI) e1
  obtain ⟨a, b⟩ := Complex.nonneg_iff.1 hl0
  have hre : l = ((l.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← b])
  refine ⟨hd, l.re, lt_of_le_of_ne a fun h => hlne (by rw [hre, ← h]; simp), ?_⟩
  ext1 v
  rw [hT, ← hre]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IndNorm
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem U_invol {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ)
    (h : ∀ g, θ.e (θ.e g) = g) (v : L2 μ) : θ.U (θ.U v) = v := by
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by
    rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h2, q2⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e.symm hg' hp'
  have hs : ∀ g, θ.e.symm (θ.e.symm g) = g := fun g => by
    have := h (θ.e.symm (θ.e.symm g))
    rw [θ.e.apply_symm_apply, θ.e.apply_symm_apply] at this
    exact this.symm
  refine Lp.ext ?_
  filter_upwards [θ.U_spec (θ.U v), q2.quasiMeasurePreserving.ae_eq_comp (θ.U_spec v)] with y a b
  simp only [Function.comp_apply] at b
  rw [a, b, h2, hs]
  congr 1
  exact Quotient.out_eq y

private theorem irr_of {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {V : Submodule ℂ (L2 μ)} (h : IsSummand μ V) : CuspIrr μ V :=
  ⟨h.le, h.closed, h.ne_bot, fun g v hv => h.inv g v hv, fun ρ a b c => h.irred ρ a b c⟩

private theorem unr_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (h : GM.Split M v) : GM.Unr M v := by
  rintro ⟨w, hl⟩
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hl.over
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (Nat.eq_one_of_mul_eq_one_right h1)

private theorem sat_iff {M : Type} [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] {n : ℕ} {μ : Measure (G1 M n)} [μ.IsHaarMeasure]
    {π : CuspSub M n} {V : Submodule ℂ (L2 μ)} (h : Dp.Carries μ π V) (w : Pl M) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ SSat μ V w (B.map fun b : ℂˣ => (b : ℂ)) := by
  rw [Dp.sSatIff M n μ π V h w]
  constructor
  · exact fun hB => ⟨B, rfl, hB⟩
  · rintro ⟨B', e, hB⟩
    rw [Multiset.map_injective Units.val_injective e]
    exact hB

private theorem exAt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (hn : 0 < n) {μ : Measure (G1 E n)}
    [μ.IsHaarMeasure] {V : Submodule ℂ (L2 μ)} (hV : IsSummand μ V) (S : Set (Pl E)) (h : ∀ w ∉ S, ∃ B, SSat μ V w B) :
    ∃ m B, At μ S V m B := by
  choose m hm using fun τ => ((Dp.parEx E n hn μ V hV).1 τ).exists
  refine ⟨m, fun w => if hw : ∃ B, SSat μ V w B then hw.choose else 0, hm, fun w hw => ?_⟩
  have hx := h w hw
  simp only [dif_pos hx]
  exact hx.choose_spec

private theorem emb_two {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (h2 : Module.finrank K M = 2) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (τ τ' : M →+* ℂ) (hne : τ ≠ τ')
    (he : τ.comp (algebraMap K M) = τ'.comp (algebraMap K M)) : τ.comp σ.toRingEquiv.toRingHom = τ' :=
  _root_.UpperTheory.Reformulated.B.Qe21.emb_two h2 σ hσ τ τ' hne he

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indNorm :
    CoreInd → IndNorm := by
  intro hC K M _ _ _ _ _ _ _ _ h2 π hn hc hb
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : M ≃ₐ[K] M)
  have hgen : ∀ τ : M ≃ₐ[K] M, τ ∈ Subgroup.zpowers σ := fun τ => mem_zpowers_of_prime_card hcard hσ
  obtain ⟨-, hAtE, -, -, -, θ, hθ, hst⟩ :=
    UpperTheory.ConvolutionTheory.T.carryLift K M σ hgen hp 2 two_pos (BW.mu1 M 2) (BW.mu1 K 2)
  have hG := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc K M σ h2 hgen 2 two_pos (BW.mu1 M 2) θ
  have hIsGal := hG.1.1 hθ
  obtain ⟨hinv, -, hspl⟩ := hG.2 hθ
  obtain ⟨τ₁, hτ₁⟩ : ∃ V, Dp.Carries (BW.mu1 M 2) π V :=
    ⟨_, (Dp.exSummand M 2 _ π _).2 ⟨(Dp.normIff M 2 π).1 hn, rfl⟩⟩
  have hs₁ := hτ₁.summand
  obtain ⟨τ₂, hτ₂d⟩ : ∃ τ₂, τ₁.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₂ := ⟨_, rfl⟩
  have hs₂ : IsSummand (BW.mu1 M 2) τ₂ := hτ₂d ▸ (Dp.twSummand M 2 _ θ τ₁).1 hs₁
  have hback : τ₂.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₁ := by
    rw [← hτ₂d]
    ext v
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      show θ.U (θ.U u) ∈ τ₁
      rwa [U_invol θ hinv]
    · intro hv
      exact ⟨θ.U v, ⟨v, hv, rfl⟩, U_invol θ hinv v⟩
  have hne : τ₁ ≠ τ₂ := fun e => hc σ hσ ((hst π τ₁ hτ₁).2 (hτ₂d.trans e.symm) σ)
  have hPair : Pair (BW.mu1 M 2) τ₁ τ₂ := ⟨irr_of hs₁, irr_of hs₂, Dp.multiplicity_one_cuspidal_spectrum_normOneGL M 2 _ τ₁ τ₂ hs₁ hs₂ hne⟩
  obtain ⟨π', hτ₂, -⟩ := Dp.exCusp M 2 _ τ₂ hs₂
  obtain ⟨hsI, hsS⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.swapAt K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback
  obtain ⟨Λ₁, t₁, S₁, hfin, hAt₁⟩ := hAtE τ₁ hs₁
  let S : Finset (Pl K) := (hfin.image fun w => w.under (𝓞 K)).toFinset.filter (GM.Split M)
  have hS : ∀ v, v ∈ S ↔ GM.Split M v ∧ ∃ w ∈ S₁, w.under (𝓞 K) = v := fun v => by
    simp [S, and_comm]
  have hSs : ∀ v ∈ S, GM.Split M v := fun v hv => ((hS v).1 hv).1
  have hSu : ∀ v ∉ S, GM.Unr M v := fun v _ => by
    by_cases h : GM.Split M v
    · exact unr_of_split v h
    · exact (hb v h).1
  have other : ∀ w : Pl M, GM.Split M (w.under (𝓞 K)) → ∃ w' : Pl M, w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K) := fun w h => by
    obtain ⟨e, -⟩ := hspl _ h
    haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have hx : e (e.symm ⟨w, hl⟩ + 1) ≠ ⟨w, hl⟩ := fun hh => by
      have := e.injective (hh.trans (e.apply_symm_apply _).symm)
      revert this
      generalize e.symm _ = i
      revert i
      decide
    exact ⟨(e (e.symm ⟨w, hl⟩ + 1)).1, fun hh => hx (Subtype.ext hh), HeightOneSpectrum.ext (e _).2.over.symm⟩
  have hSat₁ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₁ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · exact ⟨t₁ w, hAt₁.2 w fun hm => hw ((hS _).2 ⟨h, w, hm, rfl⟩)⟩
    · obtain ⟨B, hB⟩ := (hb _ h).2 w rfl
      exact ⟨_, (sat_iff hτ₁ w B).1 hB⟩
  have hSat₂ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₂ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · obtain ⟨w', hne', hu⟩ := other w h
      obtain ⟨B, hB⟩ := hSat₁ w' (hu ▸ hw)
      exact ⟨B, (hsS w w' hu.symm (Or.inl hne'.symm) B).2 hB⟩
    · obtain ⟨B, hB⟩ := hSat₁ w hw
      exact ⟨B, (hsS w w rfl (Or.inr h) B).2 hB⟩
  obtain ⟨m₁, B₁, hA₁⟩ := exAt two_pos hs₁ {w | w.under (𝓞 K) ∈ S} hSat₁
  obtain ⟨m₂, B₂, hA₂⟩ := exAt two_pos hs₂ {w | w.under (𝓞 K) ∈ S} hSat₂
  obtain ⟨V, Λ, t, hV, ⟨S₃, hf₃, hA₃⟩, hΛ, ht⟩ :=
    hC K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback S hSs hSu m₁ m₂ B₁ B₂ hA₁ hA₂ (BW.mu1 K (2 + 2))
  obtain ⟨P, hP, -⟩ := Dp.exCusp K (2 + 2) _ V hV
  refine ⟨P, ?_, ?_⟩
  · refine sysOf K M h2 (CG.mk π) (CG.mk π') (CG.mk P) (fun w w' hu hor B => ?_) ?_
    · rw [sat_iff hτ₂, sat_iff hτ₁]
      exact hsS w w' hu hor _
    · have hev : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S₃ :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hf₃.compl_mem_cofinite
      have hev' : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually S.finite_toSet.compl_mem_cofinite
      filter_upwards [ht, hev, hev'] with w hw₁ hw₃ hwS f hf
      obtain ⟨C₁, e₁, c₁⟩ := (Dp.sSatIff M 2 _ π τ₁ hτ₁ w _).1 (hA₁.2 w hwS)
      obtain ⟨C₂, e₂, c₂⟩ := (Dp.sSatIff M 2 _ π' τ₂ hτ₂ w _).1 (hA₂.2 w hwS)
      obtain ⟨C₃, e₃, c₃⟩ := (Dp.sSatIff K (2 + 2) _ P V hP _ _).1 (hA₃.2 _ hw₃)
      have hnorm : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
          Formalism.ConjugateSelfDual.normV v = Ideal.absNorm v.asIdeal := by
        intro F _ _ v
        rw [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
        rw [hnorm]
        exact NumberField.HeightOneSpectrum.one_lt_absNorm _
      have hfr : f = resDeg K w := by
        have hpl : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ resDeg K w :=
          by
            rw [hnorm, hnorm]
            exact (UpperTheory.ConvolutionTheory.T.places K M hp).2.2.2.2.1 w
        exact Nat.pow_right_injective hq (hf.symm.trans hpl)
      refine ⟨C₃, c₃, ![C₁, C₂], ?_, ?_⟩
      · intro i
        fin_cases i
        · exact c₁
        · exact c₂
      · apply Multiset.map_injective Units.val_injective
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Multiset.map_add (f := _), ← e₁, ← e₂, hw₁, bcSat, e₃, hfr]
        simp [Multiset.map_map, Function.comp_def]
  · intro τ τ' m m' hne' hk hm hm'
    have e1 : m₁ τ = m := ((Dp.parEx M 2 two_pos _ τ₁ hs₁).1 τ).unique (hA₁.1 τ) ((Dp.sInfIff M 2 _ π τ₁ hτ₁ τ m).2 hm)
    have e2 : m₂ τ = m' := by
      refine ((Dp.parEx M 2 two_pos _ τ₂ hs₂).1 τ).unique (hA₂.1 τ) ((hsI τ m').2 ?_)
      rw [emb_two h2 σ hσ τ τ' hne' hk]
      exact (Dp.sInfIff M 2 _ π τ₁ hτ₁ τ' m').2 hm'
    have e3 : Λ (τ.comp (algebraMap K M)) = m + m' := by
      have := congrFun hΛ τ
      simp only [bcInf] at this
      rw [← this, e1, e2]
    have h4 := hA₃.1 (τ.comp (algebraMap K M))
    rw [e3] at h4
    exact (Dp.sInfIff K (2 + 2) _ P V hP _ _).1 h4
end

