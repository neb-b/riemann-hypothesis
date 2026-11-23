module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.AdmissibleDesigns.StatementOneBFromUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ContDiff

namespace GlobalTheory.SmOfDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def compLmul (ℓ : Lie E a →L[ℝ] ℂ) : Lie E a →L[ℝ] (Lie E a →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ℓ.comp (lmul M)
      map_add' := fun M N => by
        ext v
        change ℓ (toL ((Matrix.of M + Matrix.of N) * Matrix.of v)) = ℓ (toL (Matrix.of M * Matrix.of v)) + ℓ (toL (Matrix.of N * Matrix.of v))
        rw [Matrix.add_mul]
        exact map_add ℓ (toL (Matrix.of M * Matrix.of v)) (toL (Matrix.of N * Matrix.of v))
      map_smul' := fun c M => by
        ext v
        change ℓ (toL ((c • Matrix.of M) * Matrix.of v)) = c • ℓ (toL (Matrix.of M * Matrix.of v))
        rw [Matrix.smul_mul]
        exact map_smul ℓ c (toL (Matrix.of M * Matrix.of v)) }

theorem contDiffAt_inv {z : Lie E a} (hz : z ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) z := by
  have hdet : IsUnit (Matrix.of z).det := (Matrix.isUnit_iff_isUnit_det _).1 hz
  have h1 : ContDiffAt ℝ ∞ (fun x : Lie E a => Ring.inverse (Matrix.of x).det) z := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) hdet.unit
    rw [IsUnit.unit_spec] at h
    exact h.comp z (contDiff_det (E := E)).contDiffAt
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun x : Lie E a => Matrix.adjugate (Matrix.of x) i j := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ _ k).comp (contDiff_apply ℝ _ (σ k))
  have e : (fun x : Lie E a => toL (Matrix.of x)⁻¹ i j) =
      fun x => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x
    rw [Matrix.inv_def]
    rfl
  rw [e]
  exact h1.mul h2.contDiffAt

theorem hasFDerivAt_chart {f : GA E a → ℂ} {ι : Type} [Fintype ι] {fs : ι → GA E a → ℂ}
    {ℓ : ι → (Lie E a →L[ℝ] ℂ)} (hd : ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a))
    (g : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart f g) (∑ i, chart (fs i) g z • compLmul (ℓ i) (toL (Matrix.of z)⁻¹)) z := by
  obtain ⟨y, hy⟩ := hz
  obtain rfl : z = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  have h := hd (g * infGL E a y)
  rw [← e1] at h
  have h2 := h.comp (toL y.val) (lmul (toL (y⁻¹).val)).hasFDerivAt
  rw [← e] at h2
  refine h2.congr_fderiv ?_
  have ei : toL (Matrix.of (toL y.val))⁻¹ = toL (y⁻¹).val := by
    change toL (y.val)⁻¹ = toL (y⁻¹).val
    rw [Matrix.coe_units_inv]
  rw [ei]
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chart_val]
  rfl

theorem mem_Sm_of_hasFDerivAt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  intro E _ _ _ a K hK
  have key : ∀ n : ℕ, ∀ f ∈ K, ∀ g, ∀ z ∈ invSet E a, ContDiffAt ℝ n (chart f g) z := by
    intro n
    induction n with
    | zero =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, -, hd⟩ := hK f hf
      exact contDiffAt_zero.2 ⟨invSet E a, isOpen_invSet.mem_nhds hz, fun x hx =>
        (hasFDerivAt_chart hd g hx).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, hfs, hd⟩ := hK f hf
      rw [Nat.cast_succ]
      refine contDiffAt_succ_iff_hasFDerivAt.2 ⟨_, ⟨invSet E a, isOpen_invSet.mem_nhds hz,
        fun x hx => hasFDerivAt_chart hd g hx⟩, ?_⟩
      refine ContDiffAt.sum fun i _ => (ih (fs i) (hfs i) g z hz).smul ?_
      exact (compLmul (ℓ i)).contDiff.contDiffAt.comp z (contDiffAt_infty.1 (contDiffAt_inv hz) n)
  intro f hf g z hz
  exact (contDiffAt_infty.2 fun n => key n f hf g z hz).contDiffWithinAt

end GlobalTheory.SmOfDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NodupIntShift
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

namespace GlobalTheory.RowRegAlg

theorem nodup_int_shift (R : Ranks) (S : Multiset ℂ) (hn : S.Nodup) (hi : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    S.Nodup ∧ ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ) + ((R.r : ℂ) - 1) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  refine ⟨hn, fun z hz => ?_⟩
  obtain ⟨n, rfl⟩ := hi z hz
  refine ⟨n - c, ?_⟩
  rw [hc]
  push_cast
  ring

theorem ralg_of_infG : ∀ (D : D7) (π : D.naut.CG D.R.r),
    (∀ τ : D.what₂.Tau, D.naut.infG π (embTau D τ) = hcSigma (D.hc τ) ∧
      D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z)) →
    D.naut.ralg π := by
  intro D π h
  rw [D.naut.ralg_def]
  intro φ
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = embTau D τ := hτ
    rw [e, (h τ).1]
    exact nodup_int_shift D.R _ (GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _) (hcSigma_int _)
  · have e : φ = embTauBar D τ := hτ
    rw [e, (h τ).2]
    refine nodup_int_shift D.R _ ((GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _).map neg_injective) fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨n, rfl⟩ := hcSigma_int _ y hy
    exact ⟨-n, by push_cast; ring⟩

end GlobalTheory.RowRegAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficient
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

namespace RapidCoef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * ‖toL A‖ * ‖toL B‖ := by
  have h : ∀ (C : Matrix (Fin a) (Fin a) (Cinf E)) i j, ‖C i j‖ ≤ ‖toL C‖ := fun C i j =>
    (norm_le_pi_norm (toL C i) j).trans (norm_le_pi_norm (toL C) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin a, ‖toL A‖ * ‖toL B‖ := Finset.sum_le_sum fun l _ =>
        (norm_mul_le _ _).trans (mul_le_mul (h A i l) (h B l j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem continuous_smul_adj : Continuous fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate) := by
  change Continuous fun q : Cinf E × Matrix (Fin a) (Fin a) (Cinf E) => q.1 • q.2.adjugate
  fun_prop

theorem continuous_conj (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun q : Lie E a × Lie E a => toL (Matrix.of q.1 * M * Matrix.of q.2) := by
  change Continuous fun q : Matrix (Fin a) (Fin a) (Cinf E) × Matrix (Fin a) (Fin a) (Cinf E) => q.1 * M * q.2
  fun_prop

theorem inv_val_eq (y : GL (Fin a) (Cinf E)) :
    (y⁻¹).val = (fun v => (y.val.det v)⁻¹) • y.val.adjugate := by
  symm
  apply Units.eq_inv_of_mul_eq_one_left
  rw [mul_smul_comm, Matrix.mul_adjugate, smul_smul]
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have : (fun v => (y.val.det v)⁻¹) * y.val.det = 1 := by
    funext v
    exact inv_mul_cancel₀ ((Pi.isUnit_iff.1 hu) v).ne_zero
  rw [this, one_smul]

end RapidCoef


open RapidCoef in
theorem isRapidInf_mul_adCoef : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  intro E _ _ _ a X _ ν k γ hr p
  obtain ⟨hk, hγ, hint⟩ := hr
  haveI : SecondCountableTopology (Lie E a) := inferInstance
  haveI : BorelSpace (Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Lie E a × Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Cinf E × Lie E a) := inferInstance
  have hA : Measurable fun x => toL (γ x).val := hγ
  have hdet : Measurable fun x => ((γ x).val).det := contDiff_det.continuous.measurable.comp hA
  have hc : Measurable fun x => (fun v => (((γ x).val).det v)⁻¹ : Cinf E) :=
    Measurable.of_eval fun v => ((measurable_pi_apply v).comp hdet).inv
  have hinv : Measurable fun x => toL (γ x)⁻¹.val := by
    have : (fun x => toL (γ x)⁻¹.val) =
        (fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate)) ∘
          fun x => ((fun v => (((γ x).val).det v)⁻¹ : Cinf E), toL (γ x).val) := by
      funext x; simp only [Function.comp_apply, inv_val_eq]; rfl
    rw [this]
    exact continuous_smul_adj.measurable.comp (hc.prodMk hA)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) (Cinf E), M = Matrix.of (lieBasis E a p.2) := ⟨_, rfl⟩
  have e : ∀ y : GL (Fin a) (Cinf E), adCoef y p = lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val)) :=
    fun y => by subst hM; rfl
  have hconj : Measurable fun x => toL ((γ x)⁻¹.val * M * (γ x).val) := by
    have h := (continuous_conj M).measurable.comp (hinv.prodMk hA)
    exact h
  have had : Measurable fun x => adCoef (γ x) p := by
    have h := (lieCoord E a p.1).continuous.measurable.comp hconj
    have h' : (fun x => adCoef (γ x) p) = fun x => lieCoord E a p.1 (toL ((γ x)⁻¹.val * M * (γ x).val)) :=
      funext fun x => e (γ x)
    rw [h']
    exact h
  have hh : Measurable fun x => height (γ x) := by
    unfold height
    exact (measurable_const.add hA.norm).add hinv.norm
  have hh1 : ∀ y : GL (Fin a) (Cinf E), 1 ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]
  have hA_le : ∀ y : GL (Fin a) (Cinf E), ‖toL y.val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have hI_le : ∀ y : GL (Fin a) (Cinf E), ‖toL (y⁻¹).val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖lieCoord E a p.1‖ * ((a : ℝ) * (a * ‖toL M‖)) := ⟨_, rfl⟩
  have hbd : ∀ y : GL (Fin a) (Cinf E), ‖adCoef y p‖ ≤ C * height y ^ 2 := fun y => by
    have h0 : 0 ≤ height y := zero_le_one.trans (hh1 y)
    have h1 : ‖toL ((y⁻¹).val * M * y.val)‖ ≤ a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ :=
      (norm_toL_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) (Nat.cast_nonneg _)) (norm_nonneg _))
    have h2 : a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ ≤ a * (a * height y * ‖toL M‖) * height y :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hI_le y) (Nat.cast_nonneg _)) (norm_nonneg _)) (Nat.cast_nonneg _))
        (hA_le y) (norm_nonneg _) (by positivity)
    rw [e]
    calc ‖lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val))‖ ≤ ‖lieCoord E a p.1‖ * ‖toL ((y⁻¹).val * M * y.val)‖ :=
          (lieCoord E a p.1).le_opNorm _
      _ ≤ ‖lieCoord E a p.1‖ * (a * (a * height y * ‖toL M‖) * height y) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = C * height y ^ 2 := by rw [hC]; ring
  refine ⟨hk.mul had, hγ, fun N => ?_⟩
  refine ((hint (N + 2)).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hk.mul had).norm.mul (hh.pow_const N)).aestronglyMeasurable
  · have hpos : 0 ≤ height (γ x) ^ N := pow_nonneg (zero_le_one.trans (hh1 _)) N
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos), norm_mul]
    calc ‖k x‖ * ‖adCoef (γ x) p‖ * height (γ x) ^ N
        ≤ ‖k x‖ * (C * height (γ x) ^ 2) * height (γ x) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)) hpos
      _ = C * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlace
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem map_blocks_of_map_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Aof M).map f = 1 ∧ (Bof M).map f = 0 ∧ (Cof M).map f = 0 := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Aof, blk, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, Sum.inl.injEq]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inr j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Bof, blk, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inr i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Cof, blk, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]

theorem map_Scof_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Scof M).map f = 1 := by
  obtain ⟨hA, hB, hC⟩ := map_blocks_of_map_eq_one f M h
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin b) (Fin c) R),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  rw [Scof, Matrix.map_sub _ (map_sub f), hmul, hmul, hA, hB, hC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.mkGL_Scof_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  intro E _ _ m r S x hx _ w hw
  have h1 := hx w hw
  set f := (pLoc E w).comp (pFin E)
  have hM : (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map f = 1 := by
    have := Units.ext_iff.mp h1
    simpa using this
  have hS := map_Scof_eq_one f _ hM
  by_cases hu : IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  · refine Units.ext ?_
    change ((mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      GL (Fin (m + 1)) (Ad E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map f = 1
    rw [coe_mkGL hu]
    exact hS
  · rw [mkGL, dite_eq_right hu, map_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds
section
namespace GlobalTheory

theorem unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality

end GlobalTheory
end

