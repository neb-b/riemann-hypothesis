module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0220
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0221
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0219
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0218
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0217

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorizationStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | exact GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | (intros; apply GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyIdentityOfLengthFunction
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.Vanish

variable {n : ℕ} {W : Type} [NormedAddCommGroup W]

theorem dens_nonneg [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : 0 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  positivity

theorem sq_le_dens [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) :
    ‖u s y‖ ^ 2 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [sq_nonneg ‖dt u s y‖]

theorem dens_continuousOn [NormedSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) :
    ContinuousOn (dens u s) (GLs n) := by
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu
  have a : ContinuousOn (dt u s) (GLs n) := ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (dt u) h1).2.2.1 s).continuousOn
  have b : ContinuousOn (u s) (GLs n) := (h3 s).continuousOn
  have c : ∀ p : Ix n, ContinuousOn (Rt (hm p) u s) (GLs n) := fun p =>
    ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (Rt (hm p) u) (h2 (hm p))).2.2.1 s).continuousOn
  unfold dens
  refine ((a.norm.pow 2).add (continuousOn_const.mul ?_)).add (b.norm.pow 2)
  exact continuousOn_finsetSum _ (fun p _ => (c p).norm.pow 2)

theorem weighted_zero [NormedSpace ℝ W] (ℓ : Mat n → ℝ) (hℓ : ContinuousOn ℓ (GLs n))
    (χ : ℝ → ℝ) (hχ : ∀ x, 1 ≤ x → χ x = 0) (u : ℝ → Mat n → W) (r : ℝ)
    (h0 : ∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) (h1 : ∀ y ∈ GLs n, dt u 0 y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : χ (ℓ y - r) * dens u 0 y = 0 := by
  by_cases hc : 1 ≤ ℓ y - r
  · rw [hχ _ hc, zero_mul]
  · have hlt : ℓ y < r + 1 := by linarith
    have hnh : GLs n ∈ nhds y := isOpen_GLs.mem_nhds hy
    have hca : ContinuousAt ℓ y := hℓ.continuousAt hnh
    have hev : u 0 =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hca.eventually_lt continuousAt_const hlt, hnh] with z hz hzG
      exact h0 z hzG hz
    have hR : ∀ p : Ix n, Rt (hm p) u 0 y = 0 := fun p => by
      change fderiv ℝ (u 0) y (y * hm p) = 0
      rw [hev.fderiv_eq]
      simp
    have hd : dens u 0 y = 0 := by
      unfold dens
      simp [hR, h1 y hy, h0 y hy hlt]
    rw [hd, mul_zero]

theorem energy_vanish : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) →
    ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) →
    (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) →
      ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) →
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) →
    (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W),
    (∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) →
    ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) →
    (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) →
    ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r hχ2 h0 h1
    t ht y hy hyt
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.CompanionTheory.WaveSpd.LocEnergy.energy_diff_ineq μ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r
  choose e' he' hle using hK
  have hℓc : ContinuousOn ℓ (GLs n) := hℓ.continuousOn
  have hnn : ∀ (s : ℝ) (z : G n), 0 ≤ χ (ℓ z.val + C * s - r) * dens u s z.val := fun s z =>
    mul_nonneg (hχ0 _) (dens_nonneg u s _)
  have hzero : (∫ z : G n, χ (ℓ z.val + C * t - r) * dens u t z.val ∂μ) = 0 := by
    refine GlobalTheory.CompanionTheory.WaveSpd.GronwallZero.eq_zero_of_deriv_le_mul
      (fun s => ∫ z : G n, χ (ℓ z.val + C * s - r) * dens u s z.val ∂μ) e' K t ht he' hle
      (fun s => integral_nonneg (hnn s)) ?_
    have : ∀ z : G n, χ (ℓ z.val + C * 0 - r) * dens u 0 z.val = 0 := fun z => by
      have := weighted_zero ℓ hℓc χ hχ1 u r h0 h1 z.val (val_mem_GLs z)
      simpa using this
    simp only [this, integral_zero]
  have hval : Continuous (fun z : G n => z.val) := Units.continuous_val
  have hcont : Continuous (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    have c1 : Continuous (fun z : G n => ℓ z.val) := hℓc.comp_continuous hval val_mem_GLs
    have c2 : Continuous (fun z : G n => dens u t z.val) :=
      (dens_continuousOn u hu t).comp_continuous hval val_mem_GLs
    exact (hχs.continuous.comp ((c1.add continuous_const).sub continuous_const)).mul c2
  have hsupp : HasCompactSupport (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    refine HasCompactSupport.intro (hcpt (1 + r - C * t)) ?_
    intro z hz
    have hz' : 1 + r - C * t < ℓ z.val := not_le.1 hz
    have : χ (ℓ z.val + C * t - r) = 0 := hχ1 _ (by linarith)
    simp only [this, zero_mul]
  let yu : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  have hyu : yu.val = y := rfl
  have hat : χ (ℓ y + C * t - r) * dens u t y = 0 := by
    by_contra hne
    have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := yu) hsupp
      (fun z => hnn t z) (by simpa [hyu] using hne)
    exact this.ne' hzero
  rw [hχ2 _ (by linarith), one_mul] at hat
  have hsq := sq_le_dens u t y
  rw [hat] at hsq
  have : ‖u t y‖ ^ 2 = 0 := le_antisymm hsq (by positivity)
  simpa using this

end GlobalTheory.CompanionTheory.WaveSpd.Vanish
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenEmbeddingVal
section
noncomputable section

open NumberField IsDedekindDomain Topology Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1

namespace GlobalTheory.CompanionTheory.HeckeFin

variable (L : Type) [Field L] [NumberField L]

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem continuous_infIdele : Continuous (infIdele L) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : (InfiniteAdeleRing L)ˣ → InfiniteAdeleRing L) :=
  Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace L, v.Completion)

theorem denseRange_units :
    DenseRange (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom : Lˣ → (InfiniteAdeleRing L)ˣ) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨l, w, hw, hl⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open
    ((isOpenEmbedding_val L).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero] at hl
    exact w.ne_zero hl
  exact ⟨w, hw, Units.mk0 l hl0, Units.ext hl.symm⟩

variable {L}

end GlobalTheory.CompanionTheory.HeckeFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coe_toC0 {f : ℝ → ℂ} (h₁ : Continuous f) (h₂ : Tendsto f (cocompact ℝ) (𝓝 0)) (y : ℝ) : toC0 f y = f y := by
  have : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0) := ⟨h₁, h₂⟩
  simp only [toC0]
  rw [dite_eq_left this]
  rfl

theorem adj_rho {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  have hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)
    simpa using this.symm
  have hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)
    simpa using this.symm
  let I : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩
  ext v
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := I.inner_map_map v (E.ρ k⁻¹ w)
  have e : ∀ z, I z = E.ρ k z := fun _ => rfl
  rw [e, e, hmul] at this
  exact this.symm

theorem kerCore_of (hFR : RowExists) (hRM : RowMatrix) (hAS : AdjSmooth) (hRL : RowLeft) (hAF : ActFormula)
    (hWR : WaveRep) (hWU : WaveUniq) (hPR : PhiRes) (hWI : WaveInt) (hSR : SupportRow) : KerCore := by
  intro n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  obtain ⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩ := id hCS
  obtain ⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩ :=
    hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD
  obtain ⟨F⟩ := hAbsFC _ _ Ω T hDense hSym hEx hLeft
  obtain ⟨c, hc⟩ := hSB n μ E hLg hUn hRC
  have hStd : Std μ E F c :=
    ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩
  have hPW1 := (hPW c g T₀ hb).1
  have hPW2 := (hPW c g T₀ hb).2
  have hC0 : ∀ y, toC0 (hg c g) y = hg c g y := fun y => by
    have := hPW1 0
    simp only [pow_zero, one_mul] at this
    exact coe_toC0 this.1 (by simpa using this.2) y
  have hR : Rapid (toC0 (hg c g)) := fun m =>
    ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by
      rw [coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩
  obtain ⟨A, hA⟩ := hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)
  have hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
      cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x := by
    intro f hf hcpt u hu h0 f' hs _ hcl x hx
    obtain ⟨N, b, U, hN, hT, hUw, hU0, hUt⟩ := hWR n μ E Ω T F c hStd f hf hcpt
    have huU : ∀ t, u t x = U t x := fun t =>
      hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx
    have hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b := by
      rw [hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]
      rfl
    have := hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx
    simpa only [huU] using this
  obtain ⟨R, hRsup⟩ := hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV
  have hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y := by
    intro k y hy
    ext v
    exact (hA v).2.1 y hy k
  have hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n := by
    intro k y hy
    have hk : (k.1 : Mat n).det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hk hy
  refine ⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩
  · intro y hy hl
    have : A y = 0 := by
      ext v
      exact hRsup v _ (hA v) y hy hl
    simp [this]
  · intro y hy k₁ k₂
    have e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y) := hKdef k₂ _ (hkG k₁ y hy)
    have e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹ := by
      ext v
      exact hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v
    show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _
    rw [e1, e2]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]
  · intro f hf hcpt u hu h0 x hx
    have hSf : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hcpt).1
    obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR
    obtain ⟨f', hf's, hf'e, hf'c, -⟩ := hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)
    rw [hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx,
      hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]

theorem kerCore : KerCore :=
  have hLC := _root_.GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob _root_.GlobalTheory.CompanionTheory.KerFc.ltSob
  kerCore_of (GlobalTheory.T.kernel_row_exists _root_.GlobalTheory.CompanionTheory.KerFc.factorRapid _root_.GlobalTheory.CompanionTheory.KerFc.evAdj) _root_.GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds _root_.GlobalTheory.CompanionTheory.KerFc.adjSmooth
    (GlobalTheory.T.kernel_row_left_invariant _root_.GlobalTheory.CompanionTheory.KerFc.ltSob hLC) (GlobalTheory.T.kernel_action_formula _root_.GlobalTheory.CompanionTheory.KerFc.ltSob hLC) _root_.GlobalTheory.CompanionTheory.KerFc.waveRep _root_.GlobalTheory.CompanionTheory.KerFc.waveUniq _root_.GlobalTheory.CompanionTheory.KerFc.phiRes_holds
    _root_.GlobalTheory.CompanionTheory.KerFc.waveInt _root_.GlobalTheory.CompanionTheory.KerFc.supportRow

end GlobalTheory.CompanionTheory.KerFc
end
end

