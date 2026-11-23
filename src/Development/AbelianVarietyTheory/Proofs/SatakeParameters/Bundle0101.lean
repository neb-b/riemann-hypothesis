module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem congr_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  intro D p _ hpd ι cE s δ hcE hδ hsδ hss hpair hK
  set th : ℂ_[p] := ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) with hth
  have hp0 : (0 : ℝ) < ‖(p : ℂ_[p])‖ := Formalism.L2.Th1.GD.norm_p_pos
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.GD.norm_p_lt_one
  have hsq : th ^ 2 = -(p : ℂ_[p]) := by
    rw [hth, ← map_pow, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ← hpd]
    simp
  have hnorm2 : ‖th‖ ^ 2 = ‖(p : ℂ_[p])‖ := by
    rw [← norm_pow, hsq, norm_neg]
  have hnth : ‖th‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm2, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : 1 < ‖th‖ ^ 2 := by nlinarith
    linarith
  · intro h
    rw [h, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  · intro t y
    have hp2 : p ≠ 2 := by
      have h := hypOdd_of_hostHyp D.host.hyp
      obtain ⟨-, -, h1, h2, h3⟩ := h
      omega
    have hI := Formalism.L2.Th1.GD.InertiaRam_proof p hp2 D.host.E s δ (rho D ι (false, t)) hδ hsδ hss
      (fun y hy => hK _ y hy)
    let y' : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv y
    have hy' : ((y' : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := rfl
    have h2 := hI.2.1 y'
    rw [hy'] at h2
    have htrue : rho D ι (true, t) (y : D.host.E) = rho D ι (false, t) (s (D.host.conj (y : D.host.E))) := by
      show ι (TaylorLogMetric.embT D (tauPl D (true, t)) (y : D.host.E)) = ι (TaylorLogMetric.embT D (tauPl D (false, t)) _)
      rw [hpair t, hcE]
    rw [htrue, hnth]
    exact h2

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitUnif

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)


omit [NumberField E] [Algebra F E] in
theorem map_mem (x : 𝓞 E) : φ x ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem lt_one_iff (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_max (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))

theorem irreducible_of_valued (p : v.adicCompletionIntegers F)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-1)) : Irreducible p := by
  have hp0 : (p : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_max, lt_one_iff, Ideal.mem_span_singleton', ← hp]
  constructor
  · intro h
    refine ⟨⟨(x : v.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    show Valued.v ((x : v.adicCompletion F) / p) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ h zero_le
  · rintro ⟨a, rfl⟩
    show Valued.v ((a : v.adicCompletion F) * p) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' a.2

variable (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in
theorem valued_unif (ϖ : 𝓞 E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    Valued.v (φ ϖ) = WithZero.exp (-1) := by
  refine le_antisymm ((lt_one_iff _).1 ((hP ϖ).1 h1)) ?_
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  let s : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) t
  have hs : Valued.v (φ s) = WithZero.exp (-1) := by
    have e1 : (s : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t)) =
        v.valuation F (algebraMap (𝓞 F) F t) := v.valuedAdicCompletion_eq_valuation' _
    rw [e1, hφ, e2, HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hsP : s ∈ P.asIdeal := by rw [hP, lt_one_iff, hs]
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _
  have hle : P.intValuation s ≤ P.intValuation ϖ := by
    have a1 := (P.intValuation_le_pow_iff_mem s 1).2 (by simpa using hsP)
    have a2 := mt (P.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : P.intValuation ϖ ≠ 0 := P.intValuation_ne_zero ϖ (fun h => hϖ0 (by rw [h]; rfl))
    refine a1.trans ?_
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a2 ⊢
    push_cast at a2 ⊢
    omega
  have hx : P.valuation E ((s : E) / ϖ) ≤ 1 := by
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact hle
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
  have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
    le_antisymm (map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
  have h3 : (s : E) * ((d : 𝓞 E) : E) = (n : E) * ϖ := by
    have h' : (s : E) / ϖ * ((d : 𝓞 E) : E) = (n : E) := h
    rw [← h']
    field_simp
  have h4 := congrArg (fun z => Valued.v (φ z)) h3
  simp only [map_mul] at h4
  rw [hd, mul_one, hs] at h4
  rw [h4]
  exact mul_le_of_le_one_left' (map_mem v φ n)

include hφ hP in
theorem card_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm P.asIdeal := by
  let ψ : 𝓞 E →+* v.adicCompletionIntegers F :=
    (φ.comp (algebraMap (𝓞 E) E)).codRestrict _ (map_mem v φ)
  let χ : 𝓞 E →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp ψ
  have hker : RingHom.ker χ = P.asIdeal := by
    ext x
    rw [RingHom.mem_ker, hP]
    show IsLocalRing.residue _ (ψ x) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, mem_max]
    rfl
  have hsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := Formalism.UG.P.glint_exists_approx v x
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
    show IsLocalRing.residue _ (ψ _) = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max]
    have e1 : ((ψ (algebraMap (𝓞 F) (𝓞 E) r) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← hφ]
      rfl
    rw [AddSubgroupClass.coe_sub, e1]
    exact hr
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end General

theorem unif_chart : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  intro D e P v π he hc ϖ h1 h2
  let φ : D.host.E →+* v.adicCompletion D.host.F := π.comp (incA D)
  have hφ : ∀ t : D.host.F, φ (algebraMap D.host.F D.host.E t) =
      algebraMap D.host.F (v.adicCompletion D.host.F) t := by
    intro t
    have e1 : incA D (algebraMap D.host.F D.host.E t) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
    show π (incA D _) = _
    rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, hc.2.2.2, isInt_Ov]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  exact ⟨⟨⟨φ ϖ, map_mem v φ ϖ⟩, rfl, irreducible_of_valued v _ (valued_unif v φ P hφ hP ϖ h1 h2)⟩,
    card_residueField v φ P hφ hP⟩

end GlobalTheory.SplitUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem flin_pad {K : Type} [Field K] {σ n m : Type} [Fintype n] [Fintype m] {l linv : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) (c : n ⊕ m → K) (u : m → MvPowerSeries σ K) :
    Formalism.L2.Th1.C.flin l linv c (Sum.elim (fun _ => (0 : MvPowerSeries σ K)) u) =
      Formalism.L2.Th1.C.flin l linv (fun j => c (Sum.inr j)) u := by
  unfold Formalism.L2.Th1.C.flin
  congr 1
  rw [Fintype.sum_sum_type]
  simp [hl]


open Formalism.L2.Th1.C in
theorem unitaryInv_rect {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hFr : Frame R l linv ph) (O : Type) [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hF1 : Formalism.L2.Th1.C.F1 R l linv ph)
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (γ : Matrix n m O)
    (hγ : γ.conjTranspose * γ = 1) {σ : Type} (u : m → MvPowerSeries σ K) (hu : ∀ j, IsPt R (u j)) :
    Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (γ i j)) u) ph) (∑ j, PowerSeries.subst (u j) ph) := by
  set P : Matrix n n O := 1 - γ * γ.conjTranspose with hP
  have hPh : P.conjTranspose = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPγ : P * γ = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hγ, Matrix.mul_one, sub_self]
  have hγP : γ.conjTranspose * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hγ, Matrix.one_mul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [show P * P = P * (1 - γ * γ.conjTranspose) from rfl]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPγ, Matrix.zero_mul, sub_zero]
  have hΔ : (Matrix.fromBlocks P γ γ.conjTranspose 0).conjTranspose * Matrix.fromBlocks P γ γ.conjTranspose 0 = 1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose, hPh, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, hPP, hPγ, hγP, hγ, ← Matrix.fromBlocks_one]
    congr 1
    · rw [hP]; abel
    · simp
    · simp
    · simp
  have hu' : ∀ c : n ⊕ m, IsPt R (Sum.elim (fun _ : n => (0 : MvPowerSeries σ K)) u c) := by
    rintro (c | c)
    · exact ⟨by simp, fun k => by simp⟩
    · exact hu c
  have key := unitaryInv K R l linv ph hFr O τ hE hB hF1 hN hA (n ⊕ m)
    (Matrix.fromBlocks P γ γ.conjTranspose 0) hΔ σ (Sum.elim (fun _ : n => 0) u) hu'
  have hph : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hl : PowerSeries.constantCoeff l = 0 := hFr.1.1
  have hli : PowerSeries.constantCoeff linv = 0 := hFr.1.2.2.1
  simp only [Fintype.sum_sum_type, flin_pad hl, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, map_zero] at key
  have h0 : PowerSeries.subst (flin l linv (fun _ : m => (0 : K)) u) ph = 0 := by
    unfold flin
    simp [hli, hph]
  simpa [hph, h0] using key

theorem HostLog.subst_unitary : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  intro p _ g2 g3 s2 ε σ F hD n m _ _ _ γ hγ hγo Θ hΘ
  classical
  obtain ⟨h5, hg2, hg3, hε, hθ, hU, hF, hN⟩ := hD
  obtain ⟨hFr, hF1, hall, hbin⟩ := Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension p, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (Formalism.L2.Th1.D.frobSq (MaximalUnramifiedExtension p) p σ hU).2
  let _ : StarRing (Formalism.L2.Th1.D.BrC.Osub σ) := Formalism.L2.Th1.D.BrC.starO hσ
  let τ : Formalism.L2.Th1.D.BrC.Osub σ →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (Formalism.L2.Th1.D.BrC.Osub σ).subtype
  let γO : Matrix n m (Formalism.L2.Th1.D.BrC.Osub σ) :=
    Matrix.of fun i j => ⟨γ i j, Formalism.L2.Th1.D.BrC.mem_Osub.2 (hγ i j)⟩
  have hun : γO.conjTranspose * γO = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγo a b
    have e : ((if a = b then (1 : Formalism.L2.Th1.D.BrC.Osub σ) else 0 : Formalism.L2.Th1.D.BrC.Osub σ) : MaximalUnramifiedExtension p) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl_def
  set linv := Formalism.L2.Th1.D.expF ℂ_[p] p with hlinv_def
  set ph := PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε) with hph_def
  let t : n → MvPowerSeries m ℂ_[p] := fun i =>
    Formalism.L2.Th1.C.flin l linv (fun j => τ (γO i j)) MvPowerSeries.X
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (Formalism.G.unitBall ℂ_[p]) (t i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1 (fun j => (hall _ (hγ i j).1 (hγ i j).2).1)
      (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hcc : ∀ i, MvPowerSeries.constantCoeff (t i) = 0 := fun i => (hpt i).1
  have hcong := unitaryInv_rect (Formalism.G.unitBall ℂ_[p]) l linv ph hFr (Formalism.L2.Th1.D.BrC.Osub σ) τ
    (fun α => (hall α.1 α.2.1 α.2.2).1) (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz)) hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1) (fun α => (hall α.1 α.2.1 α.2.2).2.2) γO hun
    (MvPowerSeries.X) (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hph0 : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hb0 : ∀ (k : Type) (i : k), MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries k ℂ_[p]) = 0 :=
    fun k i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hFr.1 (MvPowerSeries.constantCoeff_X i)
  set Θt : MvPowerSeries n ℂ_[p] := MvPowerSeries.subst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) Θ with hΘt
  have hΘ' : Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) := hΘ
  have hΘe : Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) = Θt := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  obtain ⟨h3, h4, h5'⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[p] n m t hcc (fun i k => (hpt i).2 k)
    (Formalism.L2.Th1.E.phSum ph) _ hPh0 hΘ'
  rw [hΘe, Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h3
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h5'
  have hid : MvPowerSeries.subst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p]))
      (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) =
      MvPowerSeries.subst t Θt := by
    have hb : MvPowerSeries.HasSubst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 m)
    have hb' : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 n)
    have hlin : MvPowerSeries.HasSubst
        (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
    have ht : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc
    rw [MvPowerSeries.subst_comp_subst_apply hlin hb, hΘt, MvPowerSeries.subst_comp_subst_apply hb' ht]
    congr 1
    funext i
    rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hcc,
      MvPowerSeries.subst_X ht]
    simp only [t, Formalism.L2.Th1.C.flin]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.L2.Th1.C.Pts.subst_l_linv hFr.1 (by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [map_mul, show PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m ℂ_[p]) l = Formalism.InvariantFactorPaths.G7.at1 j l from rfl,
          hb0, mul_zero])]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hb, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_X hb]
    rw [MvPowerSeries.subst_C]
    rfl
  unfold HostLog
  rw [hid, h3, ← mul_assoc]
  refine Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' ?_ h4
  obtain ⟨hc0, hcI⟩ := Formalism.L2.Th1.C.Calc.cong_symm hcong
  have hA0 : MvPowerSeries.constantCoeff (∑ i : m, Formalism.InvariantFactorPaths.G7.at1 i ph : MvPowerSeries m ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hB0 : MvPowerSeries.constantCoeff (-(∑ i, PowerSeries.subst (t i) ph) : MvPowerSeries m ℂ_[p]) = 0 := by
    rw [map_neg, h5', neg_zero]
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.C.mvExp_add hA0 hB0,
    ← sub_eq_add_neg]
  exact fun k => hcI k

end GlobalTheory.KerStd
end
end

