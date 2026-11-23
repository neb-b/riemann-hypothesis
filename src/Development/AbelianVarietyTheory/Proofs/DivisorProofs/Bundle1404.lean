module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeIntegralNonvanishing
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagTan GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

private theorem evR_eq_zero_of_genVal_eq_zero {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) {L : Type} [Field L] [Algebra c.F L] (z : FrPt Xo c L) :
    evR Xo c g z = 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    obtain ⟨C, ψ, z0, t', hψ, hb⟩ := hA hG L z
    rw [evR_frBor hg hb]
    have hnat := (mem_secZ.mp hg).1
    obtain ⟨p, φ0, u, hu⟩ := hL.test C.R C.y
    have e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))
    have e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))
    have e3 := evR_frBor hg C.bor
    have e4 : evR Xo c g (genFr hG C.Z) = 0 := by
      have h1 := h0 C.Z
      rw [genVal_apply hG] at h1
      exact h1
    rw [e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val] at e3
    have e5 : φ0 (g p u) = 0 := Subtype.ext e3
    rw [e1, AlgHom.comp_apply, e5, map_zero, mul_zero]

theorem secZ_eq_zero_of_genVal {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) : g = 0 :=by
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u := Ideal.Quotient.mk_surjective _
  show g p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := by
    first
    | exact IsJacobsonRing.out' _ p.rad
    | exact IsJacobsonRing.out inferInstance p.rad
    | exact Ideal.IsJacobson.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m := Ideal.Quotient.factorₐ c.F hIm
  obtain ⟨z, hz⟩ := exists_frMap φ u
  have h1 := evR_eq (mem_secZ.mp hg).1 hz
  rw [evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha] at h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h1.symm

theorem genVal_eq_zero_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Z : Comp Xo c) (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, genVal Z f = 0 ↔ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c f y = 0 :=by
  intro E _ _ _ H Dw l Xo c Z e f hf
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  constructor
  · intro h0 S _ _ y hy
    by_cases ht : Tested y
    · have hz : idem Z * f = 0 := by
        refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)
        by_cases hZ : Z' = Z
        · subst hZ
          rw [map_mul, h0, mul_zero]
        · rw [genVal_apply hG]
          exact evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))
      have h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y := evalAt_mul _ _ _ _ y
      rw [hz, evR_idem hy ht, one_mul] at h1
      rw [← h1]
      exact evalAt_zero _ _ y
    · unfold evR evalAt
      rw [dite_eq_right ht]
  · intro hall
    rw [genVal_apply hG]
    exact hall _ _ (liesOn_genFr hG Z)

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExtOfApplyEq
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel

theorem section_ext_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (h : X ⟶ Sp k) {f g : Sp k ⟶ X}
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (pt : Sp k) (e : f pt = g pt) : f = g := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective f
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hf hg e ⊢
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
    Scheme.fromSpecResidueField_apply] at e
  subst e
  set ρ := Spec.preimage (X.fromSpecResidueField x ≫ h) with hρ
  have hr : X.fromSpecResidueField x ≫ h = Spec.map ρ := (Spec.map_preimage _).symm
  rw [Category.assoc, hr, ← Spec.map_comp, ← Spec.map_id] at hf hg
  have hφ := Spec.map_injective hf
  have hψ := Spec.map_injective hg
  suffices hfg : φ = ψ by rw [hfg]
  ext u
  have h1 : ∀ t : k, φ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hφ
    simpa using this
  have h2 : ∀ t : k, ψ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hψ
    simpa using this
  have hu : ρ.hom (φ.hom u) = u := φ.hom.injective (h1 _)
  rw [← hu, h2, h1]

theorem finite_points_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B) (d : ℕ),
    IsIsogDeg π d → Set.Finite {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π = 1} := by
  intro k _ A B _ π d hπ
  have := hπ.fin
  let pt : Sp k := IsLocalRing.closedPoint k
  have hF := π.left.finite_preimage_singleton ((1 : 𝟙_ (Over (Sp k)) ⟶ B).left pt)
  refine Set.Finite.of_finite_image (f := fun a => a.left pt) (hF.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change π.left (a.left pt) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, show a ≫ π = 1 from ha]
  · intro a _ b _ hab
    exact Over.OverMorphism.ext (section_ext_of_apply_eq A.hom (Over.w a) (Over.w b) pt hab)

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def wspToVV (lam : InfinitePlace E → DomWeight n) : Wsp lam →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  PiTensorProduct.lift (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)

def vvToWsp (lam : InfinitePlace E → DomWeight n) : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] Wsp lam :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose

theorem vvToWsp_tenMul (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    vvToWsp lam (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = PiTensorProduct.tprod ℂ u :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose_spec u

theorem wspToVV_tprod (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wspToVV lam (PiTensorProduct.tprod ℂ u) = GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u := by
  simp [wspToVV]

theorem wInf_tprod (lam : InfinitePlace E → DomWeight n) (g : UA E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wInf lam g (PiTensorProduct.tprod ℂ u) =
      PiTensorProduct.tprod ℂ fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g) (u v) :=
  PiTensorProduct.map_tprod _ _

theorem rep_tenMul (lam : InfinitePlace E → DomWeight n) (x : infU E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) =
      GlobalTheory.CoefIrred.tenMul (K := ℂ) lam fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) (u v) :=
  GlobalTheory.DefU.rhoK_tenMul lam (GlobalTheory.DefU.cAll x.1) u

def wspEquivVV (lam : InfinitePlace E → DomWeight n) : Wsp lam ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  LinearEquiv.ofLinear (wspToVV lam) (vvToWsp lam)
    (by
      have hu := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Formalism.L2.DIV.VV ℂ lam) (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)).unique
        (y₁ := wspToVV lam ∘ₗ vvToWsp lam) (y₂ := LinearMap.id)
        (fun u => by simp [vvToWsp_tenMul, wspToVV_tprod]) (fun u => rfl)
      exact hu)
    (by
      apply PiTensorProduct.ext
      ext u
      simp [wspToVV_tprod, vvToWsp_tenMul])

theorem wspEquivVV_wInf (lam : InfinitePlace E → DomWeight n) (x : infU E n) (w : Wsp lam) :
    wspEquivVV lam (wInf lam x.1 w) = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (wspEquivVV lam w) := by
  have h : wspToVV lam ∘ₗ wInf lam x.1 = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x ∘ₗ wspToVV lam := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun u => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [wInf_tprod, wspToVV_tprod, wspToVV_tprod, rep_tenMul]
  exact LinearMap.congr_fun h w

def wInfU (lam : InfinitePlace E → DomWeight n) : Representation ℂ (infU E n) (Wsp lam) :=
  (wInf lam).comp (infU E n).subtype

theorem isIrreducible_wInfU (lam : InfinitePlace E → DomWeight n) : (wInfU lam).IsIrreducible :=
  (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv id Function.surjective_id (wspEquivVV lam)
    (ρ := wInfU lam) (σ := GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam)
    (fun x w => wspEquivVV_wInf lam x w)).2 (GlobalTheory.DefU.Wt.isIrreducible_rep E n lam)

theorem span_wInf_infU_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  intro E _ _ _ n lam
  exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible (infU E n) (Wsp lam) (wInfU lam) (isIrreducible_wInfU lam)

end GlobalTheory.BCT.TrKer
end
end

