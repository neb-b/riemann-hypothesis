module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Formalism.LocalToGlobal.Columns.MtAdWtIrr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsAtLevelsFixedPrincipalCongruenceTypePlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.MellinEntire

lemma min_inv_pos {t : ℝ} (ht : 0 < t) : 0 < min t t⁻¹ := lt_min ht (inv_pos.mpr ht)

lemma min_inv_le_one {t : ℝ} (ht : 0 < t) : min t t⁻¹ ≤ 1 := by
  rcases le_total t 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)

lemma le_inv_of_le_one' {t : ℝ} (ht : 0 < t) (h : t ≤ 1) : t ≤ t⁻¹ :=
  h.trans ((one_le_inv₀ ht).mpr h)

lemma inv_le_of_one_le' {t : ℝ} (h : 1 ≤ t) : t⁻¹ ≤ t :=
  (inv_le_one_of_one_le₀ h).trans h

lemma rpow_mul_min_pow_le {t σ : ℝ} {K : ℕ} (ht : 0 < t) (hσ : |σ| ≤ K) :
    t ^ σ * (min t t⁻¹) ^ K ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have h1 : t ^ σ ≤ t ^ (-(K:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [neg_abs_le σ])
    calc t ^ σ * t ^ K ≤ t ^ (-(K:ℝ)) * t ^ K := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have h1 : t ^ σ ≤ t ^ (K:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (le_trans (le_abs_self σ) hσ)
    calc t ^ σ * t⁻¹ ^ K ≤ t ^ (K:ℝ) * t⁻¹ ^ K := by gcongr
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]

lemma min_mul_abs_log_le {t : ℝ} (ht : 0 < t) : min t t⁻¹ * |Real.log t| ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have := Real.abs_log_mul_self_lt t ht h
    rw [abs_mul, abs_of_pos ht] at this
    linarith
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have := Real.abs_log_mul_self_lt t⁻¹ (inv_pos.mpr ht) (inv_le_one_of_one_le₀ h)
    rw [Real.log_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ht)] at this
    linarith

theorem integrable_and_differentiable {X : Type} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℂ) (T : X → ℝ)
    (hA : AEStronglyMeasurable A ν) (hT : Measurable T) (hTpos : ∀ x, 0 < T x)
    (hw : Integrable (fun x => min (T x) (T x)⁻¹) ν)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) :
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  have wpos : ∀ x, 0 < min (T x) (T x)⁻¹ := fun x => min_inv_pos (hTpos x)
  have wle : ∀ x, min (T x) (T x)⁻¹ ≤ 1 := fun x => min_inv_le_one (hTpos x)
  have hTc : Measurable fun x => ((T x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hT
  have meas : ∀ s : ℂ, AEStronglyMeasurable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν :=
    fun s => hA.mul (hTc.pow_const s).aestronglyMeasurable
  have bnd : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x (s : ℂ), |s.re| ≤ K →
      ‖A x * ((T x : ℝ) : ℂ) ^ s‖ ≤ C * (min (T x) (T x)⁻¹) ^ 2 := by
    intro K
    obtain ⟨C, hC⟩ := hdec (K + 2)
    refine ⟨|C|, abs_nonneg _, fun x s hs => ?_⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hTpos x)]
    have hA' : ‖A x‖ ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (wpos x).le _))
    have h2 := rpow_mul_min_pow_le (hTpos x) hs
    have h0 : 0 ≤ T x ^ s.re := Real.rpow_nonneg (hTpos x).le _
    calc ‖A x‖ * T x ^ s.re ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) * T x ^ s.re :=
          mul_le_mul_of_nonneg_right hA' h0
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 * (T x ^ s.re * (min (T x) (T x)⁻¹) ^ K) := by ring
      _ ≤ |C| * (min (T x) (T x)⁻¹) ^ 2 * 1 := by
          gcongr
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 := mul_one _
  have sq_le : ∀ x, (min (T x) (T x)⁻¹) ^ 2 ≤ min (T x) (T x)⁻¹ := fun x => by
    nlinarith [wpos x, wle x]
  refine ⟨fun s => ?_, fun s₀ => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := bnd ⌈|s.re|⌉₊
    refine Integrable.mono' (hw.const_mul C) (meas s) (ae_of_all _ fun x => ?_)
    exact (hC x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0)
  · obtain ⟨C, hC0, hC⟩ := bnd (⌈|s₀.re|⌉₊ + 1)
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ ((⌈|s₀.re|⌉₊ + 1 : ℕ) : ℝ) := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : |s.re| ≤ |s₀.re| + |s.re - s₀.re| := by
        have := abs_add_le s₀.re (s.re - s₀.re); simpa using this
      have h3 := Nat.le_ceil |s₀.re|
      push_cast
      linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s x => A x * ((T x : ℝ) : ℂ) ^ s)
      (F' := fun s x => A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ)))
      (x₀ := s₀) (bound := fun x => C * min (T x) (T x)⁻¹) (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => meas s) ((fun s => ?_ : ∀ s : ℂ,
        Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) s₀)
      (hA.mul ((hTc.pow_const s₀).mul (Complex.measurable_log.comp hTc)).aestronglyMeasurable)
      (ae_of_all _ fun x s hs => ?_) (hw.const_mul C)
      (ae_of_all _ fun x s _ => ?_)
    · exact key.2.differentiableAt
    · obtain ⟨C', hC0', hC'⟩ := bnd ⌈|s.re|⌉₊
      refine Integrable.mono' (hw.const_mul C') (meas s) (ae_of_all _ fun x => ?_)
      exact (hC' x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0')
    · show ‖A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ))‖ ≤ C * min (T x) (T x)⁻¹
      rw [← mul_assoc, norm_mul, ← Complex.ofReal_log (hTpos x).le, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := hC x s (hre s hs)
      have h2 := min_mul_abs_log_le (hTpos x)
      calc ‖A x * ((T x : ℝ) : ℂ) ^ s‖ * |Real.log (T x)|
          ≤ C * (min (T x) (T x)⁻¹) ^ 2 * |Real.log (T x)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = C * min (T x) (T x)⁻¹ * (min (T x) (T x)⁻¹ * |Real.log (T x)|) := by ring
        _ ≤ C * min (T x) (T x)⁻¹ * 1 := by
            gcongr
            exact mul_nonneg hC0 (wpos x).le
        _ = C * min (T x) (T x)⁻¹ := mul_one _
    · have hne : ((T x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hTpos x).ne'
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt.const_mul (A x)

end GlobalTheory.MellinEntire
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeRealRdIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem evK_eq_sum (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    ∃ (n : ℕ) (a : Fin n → NX.KB S i b) (x : Fin n → NX.FmK S ((j : ℕ) + 1)),
      evK YS v₀ hρ i j b t = ∑ k, ρ.e i b (a k) • evW YS v₀ j (Subtype.val (x k)) := by
  first
  | exact @_root_.GlobalTheory.EvaluationSum.evK_eq_sum
  | exact _root_.GlobalTheory.EvaluationSum.evK_eq_sum
  | (apply _root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSum.evK_eq_sum ..)

theorem mem_range_realRd_iff {ν : ℂ} (hν : ν ≠ 0) (g : GA D (Wc D j) → ℂ) :
    g ∈ Set.range (realRd YS v₀ hρ i j b ν) ↔
      ∃ (n : ℕ) (a : Fin n → NX.KB S i b) (x : Fin n → NX.FmK S ((j : ℕ) + 1)),
        ν • g = ∑ k, ρ.e i b (a k) • evW YS v₀ j (Subtype.val (x k)) := by
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨n, a, x, e⟩ := evK_eq_sum YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
    refine ⟨n, a, x, ?_⟩
    change ν • (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) = _
    rw [smul_inv_smul₀ hν, e]
  · rintro ⟨n, a, x, e⟩
    refine ⟨∑ k, (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a k ⊗ₜ[S.Ks] x k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [realRd_tmul, mul_smul]
    rw [← Finset.smul_sum, ← e, inv_smul_smul₀ hν]

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqProdSmul
section
open Matrix

namespace GlobalTheory.MulVecProduct

theorem mulVec_eq_prod_smul {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ}
    (h1 : Φ (1 : ι → GL (Fin n) ℂ) = (1 : Matrix κ κ ℂ))
    (hmul : ∀ (g h : ι → GL (Fin n) ℂ), Φ (g * h) = Φ g * Φ h)
    {v : κ → ℂ} {lam : ι → Fin n → ℤ}
    (hv : ∀ (τ : ι), GlobalTheory.AlgWtHW.IsBEig (fun (B : GL (Fin n) ℂ) ↦ Φ (Pi.mulSingle τ B)) v (lam τ))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ (τ : ι), Matrix.BlockTriangular (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) id) :
    Matrix.mulVec (Φ g) v =
      (∏ τ : ι, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
  classical
  have key : ∀ S : Finset ι, Φ (fun τ => if τ ∈ S then g τ else 1) *ᵥ v =
      (∏ τ ∈ S, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1 := by
        funext τ
        simp
      rw [h0, h1, Finset.prod_empty, one_smul, Matrix.one_mulVec]
    | insert a S ha ih =>
      have hsplit : (fun τ => if τ ∈ insert a S then g τ else 1) =
          Pi.mulSingle a (g a) * (fun τ => if τ ∈ S then g τ else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · simp [hτ]
      have ha' := (hv a).2 (g a) (hg a)
      simp only at ha'
      rw [hsplit, hmul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ha', smul_smul,
        Finset.prod_insert ha]
      congr 1
      ring
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset ι) then g τ else 1) = g := by
    funext τ
    simp
  have := key Finset.univ
  rw [hall] at this
  exact this

end GlobalTheory.MulVecProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory

theorem matrix_intertwiner_descends : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  intro K _ e Γ m p _ _ A B ⟨X, hX, hXc⟩
  letI := e.toAlgebra
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K ℂ, ℓ (X a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab ((Module.forall_dual_apply_eq_zero_iff K (X a b)).1 h)
  have h1 : ∀ (x : ℂ) (c : K), ℓ (x * e c) = ℓ x * c := by
    intro x c
    have : x * e c = c • x := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∀ (x : ℂ) (c : K), ℓ (e c * x) = c * ℓ x := by
    intro x c
    have : e c * x = c • x := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
  refine ⟨X.map ℓ, ?_, fun γ => ?_⟩
  · intro h
    apply hℓ
    have := congrFun (congrFun h a) b
    simpa using this
  · ext i j
    have key := congrArg (fun M => ℓ (M i j)) (hXc γ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, h1, h2] at key ⊢
    exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

theorem GlobalTheory.RawLift.vacFin_off : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hoffP
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hth, ?_⟩
  obtain ⟨hf₀, e, he, hthA⟩ := hL.thP.vP i t
  obtain ⟨ε, hε, rfl⟩ := hf
  have hoff : ∀ PP ∈ R.Pg ∪ R.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro PP hPP h0
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    obtain ⟨e', f', hp⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ PP
    obtain ⟨w, ε', hε', hf', hw⟩ := GlobalTheory.VacLat.place_of_primeIdem hp
    refine hoffP PP (Finset.mem_union.1 hPP) e' f' hp ?_
    rw [h0] at hw
    subst hw
    rw [hf', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hL.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hL.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA u (hz u hu) (hlat.2 e' he' u (hle hu) hh)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsAtLevelsFixedPrincipalCongruenceTypePlacesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsAtLevels_fixed_principalCongruence_typePlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∃ c : GAf D.host.E D.R.r, (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) ∧ ∀ (b : Bool), ∀ Tm ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))), Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) := by
  first | exact @GlobalTheory.RowLevConj.rows_fixed | exact GlobalTheory.RowLevConj.rows_fixed | (intros; apply GlobalTheory.RowLevConj.rows_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBKeep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT

variable {D : D7} (hE : IsEmpty D.nd.Loc) {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
  {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) (F : TwF T)

abbrev recE (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex) : TwNew D :=
  ⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩

abbrev recL (L : TwL T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))) :
    TwNew D :=
  ⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩

variable {hE Sp F} {L : TwL T} {ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))}
  {h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g}
  {th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex}
  {th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))}


set_option maxHeartbeats 4000000 in
def twFC (X : TwFrameC (recE hE Sp F ex h0 th).toD7) : TwFrameC (recL hE Sp F L ex h0 th').toD7 := { X with }


set_option maxHeartbeats 4000000 in
def expC (X : NExpTied (recE hE Sp F ex h0 th).toD7) : NExpTied (recL hE Sp F L ex h0 th').toD7 :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      letI := X.acgWt i j b
      letI : Module (FractionRing ((recL hE Sp F L ex h0 th').toD7.ntw.O i)) (X.Wt i j b) := X.modWt i j b
      { X.mtV i j b k Q ψ h1 h2 h with } }


set_option maxHeartbeats 4000000 in
theorem sideB_keep {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (B : SideB (recE hE Sp F ex h0 th).toD7 ((recE hE Sp F ex h0 th).cf cf) ((recE hE Sp F ex h0 th).row Rw) low Pq
      ((recE hE Sp F ex h0 th).rat S) hL eig θ)
    (chiI : ∀ s, L.abelian₂ s → NC.HC D.host.E)
    (hqs : ∀ i lam P, P ∉ T.S0 i →
      B.twF.iCq i (L.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(L.s2 i lam : ℝ) / 2) : ℝ) : ℂ))
    (hlam : ∀ s lam, NC.Read D.nd.plOm.1 (L.lamG s lam) (algebraMap (T.O s) (FractionRing (T.O s)))
      (B.chiD.embO s (L.sideL s lam)) (NC.complexEmbeddingRestrictedToSubfield D) (id (α := NC.HC D.host.E) (B.chiD.mu0 (L.jL s lam)) * id (α := NC.HC D.host.E) (B.chiD.del s) * (chiI s lam)⁻¹) 0) :
    Nonempty (SideB (recL hE Sp F L ex h0 th').toD7 ((recL hE Sp F L ex h0 th').cf cf) ((recL hE Sp F L ex h0 th').row Rw) low Pq
      ((recL hE Sp F L ex h0 th').rat S) hL eig θ) :=
  ⟨{ B with
      twF := twFC B.twF
      tw := { B.tw with qs_pos := hqs }
      chiD := { B.chiD with chiI := chiI }
      chi := { B.chi with lamG := hlam }
      exp := expC B.exp }⟩

end GlobalTheory.LamInstall
end
end

