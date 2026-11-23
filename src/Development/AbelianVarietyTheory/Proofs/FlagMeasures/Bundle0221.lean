module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.PsiPolarProof

variable {n : ℕ}

lemma exp_posDef_of_herm {X : Matrix (Fin n) (Fin n) ℂ} (h : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, h]; simp
  have e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have e2 : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X) := by
    rw [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]
  rw [e2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))

lemma mem_KC_of_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

lemma mul_mem_K {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) : k * k' ∈ Kset ε :=
  ⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

lemma star_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose hk.2
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem psiPolar_of (hB : PsBasic) (hE : PsEquiv) : PsiPolar := by
  intro n ε lam W _ _ τ w hl hτ
  refine ⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1
    (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩
  · have h := Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))
    rw [Matrix.mul_one] at h
    rw [h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]
    rfl
  · intro k₁ h₁ k₂ h₂ g hg
    obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
    have hp := exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)
    set p := NormedSpace.exp X
    have hs : k₂ * k₂ᴴ = 1 := Unitary.mul_star_self_of_mem h₂.1
    have hc := mem_KC_of_mem_K (star_mem_K h₂)
    have hq : (k₂ᴴ * p * k₂).PosDef :=
      hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)
    have e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]
    have hk3 := mul_mem_K (mul_mem_K h₁ hk) h₂
    have he := hE n ε lam W τ w hl hτ p k₂ᴴ hp hc
    rw [Matrix.conjTranspose_conjTranspose] at he
    rw [e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he,
      ← ContinuousLinearMap.comp_assoc]
    have hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k) := by
      have a := hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc
      have b := hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)
      rw [Matrix.mul_assoc, hs, Matrix.mul_one] at a
      exact a.symm.trans b
    rw [hm]
    rfl

end GlobalTheory.Dec.PsiPolarProof

theorem GlobalTheory.Dec.psiPolar : GlobalTheory.Dec.PsiPolar :=
  GlobalTheory.Dec.PsiPolarProof.psiPolar_of _root_.GlobalTheory.Dec.psBasic _root_.GlobalTheory.Dec.Equivar.psEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.Local

theorem eventually_eq_zero_of_fixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (σ : E → E)
    (hadd : ∀ x y, σ (x + y) = σ x + σ y) (hsmul : ∀ (c : ℂ) x, σ (c • x) = star c • σ x)
    (hinv : ∀ x, σ (σ x) = x) (hcont : Continuous σ) (x₀ : E) (hx₀ : σ x₀ = x₀) (f : E → F)
    (hf : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ f x ∧ (σ x = x → f x = 0)) :
    ∀ᶠ x in 𝓝 x₀, f x = 0 := by
  let u : E → E := fun x => (1 / 2 : ℂ) • (x + σ x)
  let v : E → E := fun x => (-Complex.I / 2 : ℂ) • x + (Complex.I / 2 : ℂ) • σ x
  have hu : ∀ x, σ (u x) = u x := by
    intro x
    simp only [u, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have hv : ∀ x, σ (v x) = v x := by
    intro x
    simp only [v, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have huv : ∀ x, u x + Complex.I • v x = x := by
    intro x
    simp only [u, v]
    match_scalars <;> (ring_nf; try simp) <;> norm_num
  have hG : Continuous fun p : E × ℂ => u p.1 + p.2 • v p.1 := by
    simp only [u, v]; fun_prop
  have h0 : ∀ t : ℂ, u x₀ + t • v x₀ = x₀ := by
    intro t
    simp only [u, v, hx₀]
    match_scalars; ring
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Metric.closedBall (0 : ℂ) 2,
      DifferentiableAt ℂ f (u x + t • v x) ∧ (σ (u x + t • v x) = u x + t • v x → f (u x + t • v x) = 0) := by
    apply (isCompact_closedBall (0 : ℂ) 2).eventually_forall_of_forall_eventually
    intro t _
    have := hG.tendsto (x₀, t)
    simp only [h0] at this
    exact this.eventually hf
  filter_upwards [htube] with x hx
  have hd : DifferentiableOn ℂ (fun t : ℂ => f (u x + t • v x)) (Metric.ball 0 2) := by
    intro t ht
    exact ((hx t (Metric.ball_subset_closedBall ht)).1.comp t (by fun_prop)).differentiableWithinAt
  have hfr : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (u x + t • v x) = 0 := by
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    refine ht.frequently (Eventually.frequently ?_)
    have hb : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ Metric.closedBall (0 : ℝ) 2 :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 two_pos)
    filter_upwards [hb] with s hs
    refine (hx s (by simpa using hs)).2 ?_
    rw [hadd, hu, hsmul, hv]; simp
  have := (hd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (Metric.mem_ball_self two_pos) hfr
    (show Complex.I ∈ Metric.ball (0 : ℂ) 2 by simp)
  simpa [huv] using this

theorem differentiableAt_of_coef {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (f : E → (W →L[ℂ] W)) (x : E)
    (hf : ∀ u v : W, DifferentiableAt ℂ (fun y => ⟪u, f y v⟫_ℂ) x) : DifferentiableAt ℂ f x := by
  let b := stdOrthonormalBasis ℂ W
  have e : f = fun y => ∑ i, ∑ j, ⟪b i, f y (b j)⟫_ℂ • (innerSL ℂ (b j)).smulRight (b i) := by
    funext y
    ext v
    conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' (f y _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Finset.sum_smul, smul_smul]
    simp only [mul_comm]
  rw [e]
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  exact (hf _ _).smul_const _

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

def prJ (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (a + Jm ε * a * Jm ε)

theorem prJ_comm (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε a * Jm ε = Jm ε * prJ ε a := by
  simp only [prJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, add_comm]

theorem prJ_of_comm {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (h : a * Jm ε = Jm ε * a) :
    prJ ε a = a := by
  rw [prJ, ← h, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  match_scalars; norm_num

theorem prJ_one (ε : Fin n → Bool) : prJ ε 1 = 1 := prJ_of_comm (by simp)

theorem prJ_conjTranspose (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε aᴴ = (prJ ε a)ᴴ := by
  simp [prJ, Jm_conjTranspose, Matrix.mul_assoc]

theorem differentiable_prJ (ε : Fin n → Bool) : Differentiable ℂ (prJ ε) := by
  unfold prJ; fun_prop

theorem eventually_isUnit : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), IsUnit a :=
  Units.isOpen.mem_nhds isUnit_one

theorem eventually_prJ_mem (ε : Fin n → Bool) : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), prJ ε a ∈ KC ε := by
  have := ((differentiable_prJ ε).continuous.tendsto' 1 1 (prJ_one ε)).eventually eventually_isUnit
  filter_upwards [this] with a ha
  exact ⟨ha, prJ_comm ε a⟩

theorem posDef_mul_conjTranspose {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsUnit c) : (c * cᴴ).PosDef := by
  rw [(Matrix.posSemidef_self_mul_conjTranspose c).posDef_iff_isUnit]
  exact hc.mul (by simpa [Matrix.star_eq_conjTranspose] using hc.star)

theorem posDef_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by simp [hX]
  have e : X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • X := by match_scalars; norm_num
  have := posDef_mul_conjTranspose (Matrix.isUnit_exp ((1 / 2 : ℂ) • X))
  rwa [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e] at this

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_differentiableAt_tau {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) :
    ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (fun y => τ (prJ ε y)) a := by
  haveI := hτ.1
  filter_upwards [(eventually_prJ_mem ε).eventually_nhds] with a ha
  refine differentiableAt_of_coef _ _ fun u v => ?_
  have h : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ y v⟫_ℂ) (KC ε) := hτ.2.2.1 u v
  have h2 : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ (prJ ε y) v⟫_ℂ)
      {y | prJ ε y ∈ KC ε} :=
    h.comp (differentiable_prJ ε).differentiableOn fun y hy => hy
  exact h2.differentiableAt ha

theorem eventually_ps_mul (hB : PsBasic) (hE : PsEquiv) (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) :
    ∀ᶠ x : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) in 𝓝 ((1, 1), (1, 1)),
      ps ε lam τ w (prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1) -
        τ (prJ ε x.1.1) * ps ε lam τ w (x.1.2 * x.2.2) * τ (prJ ε x.2.1) = 0 := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨hopen, hpos, hdiff, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hdiff' : DifferentiableOn ℂ (ps ε lam τ w) (U1 ε) := hdiff
  have hps : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
    exact hdiff'.differentiableAt (hopen'.mem_nhds hz)
  have hP := differentiable_prJ ε
  refine eventually_eq_zero_of_fixed (fun x => ((x.2.1ᴴ, x.2.2ᴴ), (x.1.1ᴴ, x.1.2ᴴ))) ?_ ?_ ?_ ?_ _ ?_ _ ?_
  · intro x y; simp
  · intro c x; simp
  · intro x; simp
  · fun_prop
  · simp
  · let E := (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    have d1 : Differentiable ℂ fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1 := by
      fun_prop
    have d2 : Differentiable ℂ fun x : E => x.1.2 * x.2.2 := by fun_prop
    have d3 : Differentiable ℂ fun x : E => x.1.1 := by fun_prop
    have d4 : Differentiable ℂ fun x : E => x.2.1 := by fun_prop
    have d5 : Differentiable ℂ fun x : E => x.1.2 := by fun_prop
    filter_upwards [(d1.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp [prJ_one])).eventually hps,
      (d2.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp)).eventually hps,
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d4.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_prJ_mem ε),
      (d5.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually eventually_isUnit] with x h1 h2 h3 h4 h5 h6
    have k1 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1)
      x h1 (d1 x)
    have k2 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => x.1.2 * x.2.2) x h2 (d2 x)
    have k3 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.1.1) x h3 (d3 x)
    have k4 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.2.1) x h4 (d4 x)
    refine ⟨k1.sub ((k3.mul k2).mul k4), ?_⟩
    intro hx
    have e1 : x.2.1 = x.1.1ᴴ := (congrArg (fun y => y.2.1) hx).symm
    have e2 : x.2.2 = x.1.2ᴴ := (congrArg (fun y => y.2.2) hx).symm
    rw [e1, e2, prJ_conjTranspose, hE n ε lam W τ w hl hτ _ _ (posDef_mul_conjTranspose h6) h5, sub_eq_zero]
    rfl

theorem psLocal_of (hB : PsBasic) (hE : PsEquiv) : PsLocal := by
  intro n ε lam W _ _ τ w hl hτ
  obtain ⟨hopen, hpos, -, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hu1 : umat (1 : UJ ε) = 1 := rfl
  obtain ⟨L, hLc, hL⟩ := (polar_decomposition_holds n ε).2.2
  have hdec : ∀ g : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp (-L g) * NormedSpace.exp (L g) = g := by
    intro g
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have h1U : inUJ ε 1 := by simp [inUJ]
  have hL1 : L 1 = 0 := by
    refine ((polar_decomposition_holds n ε).2.1 _ 1 _ 0 (hL 1 h1U).2 ⟨one_mem _, by simp⟩ (hL 1 h1U).1
      (by simp [inP, inG]) ?_).2
    rw [hdec]; simp
  have hLc' : Continuous fun g : UJ ε => L (umat g) := hLc.comp_continuous hu fun g => g.2
  have hexp : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have hc : Continuous fun g : UJ ε =>
      (((umat g * NormedSpace.exp (-L (umat g)), NormedSpace.exp (L (umat g))), (1, 1)) :
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
          (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    ((hu.mul (hexp.comp hLc'.neg)).prodMk (hexp.comp hLc')).prodMk continuous_const
  filter_upwards [(hu.tendsto' 1 1 hu1).eventually (hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)),
    (hc.tendsto' 1 ((1, 1), (1, 1)) (by simp [hu1, hL1])).eventually (eventually_ps_mul hB hE hl hτ)]
    with g hg1 hg2
  refine ⟨hg1, ?_⟩
  obtain ⟨hX, hk⟩ := hL (umat g) g.2
  simp only [prJ_one, prJ_of_comm hk.2, mul_one, hτ.2.1.1, hdec, sub_eq_zero] at hg2
  rw [hg2]
  conv_lhs => rw [← hdec (umat g)]
  exact Psi_unitary_mul ε lam τ w hk.1 (posDef_exp (hermitian_of_mem_hermitian_part hX))

end GlobalTheory.Dec.Local

theorem GlobalTheory.Dec.psLocal : PsLocal := GlobalTheory.Dec.Local.psLocal_of _root_.GlobalTheory.Dec.psBasic _root_.GlobalTheory.Dec.Equivar.psEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeWeightTermDatumPos
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WtPos

theorem finrank_loc {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem wt_pos : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d0 d : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → (∃ t, LocNG.IsTermOver P d t) → 0 < LocNG.Datum.wt d0 d := by
  intro D Z p P hR d0 d ⟨t0, ht0⟩ ⟨t, ht⟩
  have hOK := (Z.agree p).1
  haveI := hOK.loc
  haveI := hOK.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord (Z.M p) hOK (locH Z p) D.R.rS D.R.k P (finrank_loc p) hR
  have h0 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d0 t0 ht0).1
  have h1 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d t ht).1
  obtain ⟨a0, b0⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h0
  obtain ⟨a1, b1⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h1
  rw [(GlobalTheory.HL.CoordDatum.transport (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).2.2.2.2 d0 d]
  have e1 := Subgroup.relIndex_ne_zero_trans b1 a0
  have e2 := Subgroup.relIndex_ne_zero_trans b0 a1
  unfold GlobalTheory.HL.invVol
  positivity

end GlobalTheory.WtPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSideIotaMapsFixedColumnsOntoOfMatrices
section
open Formalism.BasicNotions Formalism.MainNotions

theorem GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices : ∀ (D : D7) (μ : D.what₂.Tup) (n nV dQ d : ℕ) (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb μ) (E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin dQ) (Fin nV) D.what₂.LL) (ι : Matrix (Fin d) (Fin dQ) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (RowSide.sharp D).RR.V), (∀ x, (RowSide.sharp D).eOp μ (jA x) = jA (E.mulVec x)) → (∀ F, E.mulVec (V.mulVec F) = V.mulVec F) → Function.Surjective Pq.mulVec → Function.Surjective ι.mulVec → (∀ F, (RowSide.sharp D).iota μ (jA (V.mulVec F)) = (RowSide.sharp D).jEE (eRR (ι.mulVec (Pq.mulVec F)))) → (D.what₂.V0 μ).map (D.what₂.iota μ) = ⊤ := by
  intro D μ n nV dQ d jA E V Pq ι eRR hE hV hP hι hio
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    unfold RowSide.iota Rows.Data.iota
    rw [PrimeDegreeVariant.sharp_downTo]
    rfl
  have hV0 : (RowSide.sharp D).V0 μ = D.what₂.V0 μ := rfl
  rw [eq_top_iff, ← (RowSide.sharp D).jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := hι (eRR.symm ((RowSide.sharp D).RR.b i))
  obtain ⟨F, hF⟩ := hP y
  have h1 := hio F
  rw [hF, hy, LinearEquiv.apply_symm_apply, hi] at h1
  refine ⟨jA (V.mulVec F), ?_, h1⟩
  rw [← hV0]
  exact ⟨jA (V.mulVec F), by rw [hE, hV]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.FixedForm

theorem sum_le_orbit {G α ι : Type} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞)
    (t : Finset ι) (x : ι → α) (hQ : ∀ i ∈ t, ∀ ρ : G, Q (ρ • x i) ∧ w (ρ • x i) = w (x i))
    (hd : ∀ i ∈ t, ∀ i' ∈ t, (∃ ρ : G, ρ • x i = x i') → i = i') :
    ∑ i ∈ t, w (x i) ≤ ∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0 := by
  let q : ι → MulAction.orbitRel.Quotient G α := fun i => Quotient.mk _ (x i)
  have hinj : ∀ i ∈ t, ∀ i' ∈ t, q i = q i' → i = i' := by
    intro i hi i' hi' h
    have h1 : (MulAction.orbitRel G α) (x i') (x i) := Quotient.exact h.symm
    rw [MulAction.orbitRel_apply] at h1
    exact hd i hi i' hi' h1
  have h1 : ∑ i ∈ t, w (x i) = ∑ o ∈ t.image q, if Q o.out then w o.out else 0 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 : (MulAction.orbitRel G α) (q i).out (x i) := Quotient.exact (Quotient.out_eq (q i))
    rw [MulAction.orbitRel_apply] at h2
    obtain ⟨ρ, hρ⟩ := h2
    have hρ' : ρ • x i = (q i).out := hρ
    rw [← hρ', if_pos (hQ i hi ρ).1, (hQ i hi ρ).2]
  rw [h1]
  exact ENNReal.sum_le_tsum _

theorem nD_nonneg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : NF H r) (l : ℕ) :
    0 ≤ N.nD l := by
  unfold NF.nD
  split_ifs
  · positivity
  · exact le_rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ₀ ι s Λ hg h0 hs hd
  set B : ℝ := (N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hB
  have hDel : 0 ≤ N.Del := nD_nonneg N _
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => nD_nonneg N l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hom := (GlobalTheory.DegAsm.WeightInf.main K V H hK r).1 N g
  let f : ι → Submodule (𝓞 K) V := fun i => latL N.F' N.F (Λ i)
  have hcard : ((s.image f).card : ℝ) ≤ N.NT ^ 2 := by
    have h1 := _root_.GlobalTheory.DegCnt.GlueZ.main K V H hK r N g Λ₀ hg h0
    have h2 : ((s.image f : Finset _) : Set (Submodule (𝓞 K) V)) ⊆ {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ₀} := by
      intro L hL
      rw [Finset.mem_coe, Finset.mem_image] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact ⟨Λ i, (hs i hi).1, rfl, (hs i hi).2.2.1⟩
    have h3 := (ENat.toENNReal_le.2 (Set.encard_le_encard h2)).trans h1
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hfib : ∀ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) ≤ B := by
    intro L hL
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hL
    have h1 := _root_.GlobalTheory.DegCnt.omSum_sameDat_le K V H hK r N g (Λ i₀) hg (hs i₀ hi₀).1
    have hgI : N.gI g (Λ i₀) = N.gI g Λ₀ := by
      unfold NF.gI latLa flagPairDefinitePartLattice
      rw [(hs i₀ hi₀).2.1, (hs i₀ hi₀).2.2.2]
    rw [hgI, ← hB] at h1
    have h2 := sum_le_orbit (G := N.R) (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g (Λ i₀) Λ')
      (fun Λ' => ENNReal.ofReal (N.om Λ')) (s.filter fun i => f i = f i₀) Λ
      (by
        intro i hi ρ
        obtain ⟨hi, hfi⟩ := Finset.mem_filter.1 hi
        obtain ⟨a1, ⟨a2, a3, a4⟩, -⟩ := GlobalTheory.DegCnt.StabInv.main K V H hK r N g (Λ i) hg (hs i hi).1 ρ.1 ρ.2
        refine ⟨⟨a1, a2.trans ((hs i hi).2.1.trans (hs i₀ hi₀).2.1.symm), a3.trans hfi,
          a4.trans ((hs i hi).2.2.2.trans (hs i₀ hi₀).2.2.2.symm)⟩, ?_⟩
        exact congrArg ENNReal.ofReal ((hom (Λ i) hg (hs i hi).1).2 ρ.1 ρ.2))
      (by
        rintro i hi i' hi' ⟨ρ, hρ⟩
        exact hd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 ⟨ρ.1, ρ.2, hρ⟩)
    have h3 : ∑ i ∈ s with f i = f i₀, ENNReal.ofReal (N.om (Λ i)) ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h1
      unfold NF.omSum
      convert h2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      (hom (Λ i) hg (hs i (Finset.mem_filter.1 hi).1).1).1.le), ENNReal.ofReal_le_ofReal_iff hB0] at h3
    exact h3
  calc ∑ i ∈ s, N.om (Λ i) = ∑ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ ≤ (s.image f).card • B := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = ((s.image f).card : ℝ) * B := nsmul_eq_mul _ _
    _ ≤ N.NT ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0

end GlobalTheory.DegAsm.FixedForm
end

