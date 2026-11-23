module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def CuspBounded : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ →
      (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
        (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
          ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
      (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
          ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) →
      IsCuspFun V φ →
      ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ C : ℝ, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ C

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

open GlobalTheory.SmoothForms

theorem mul_norm_deriv_le {f f₁ f₂ : ℝ → ℂ} (h₁ : ∀ t, HasDerivAt f (f₁ t) t) (h₂ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    {h B : ℝ} (hh : 0 ≤ h) (hB : ∀ t ∈ Set.Icc 0 h, ‖f₂ t‖ ≤ B) :
    h * ‖f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * h := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hh⟩)
  have a1 : ∀ t ∈ Set.Icc 0 h, ‖f₁ t - f₁ 0‖ ≤ B * h := fun t ht => by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f₁) (f' := f₂) (a := 0) (b := h) (C := B)
      (fun s _ => (h₂ s).hasDerivWithinAt) (fun s hs => hB s ⟨hs.1, hs.2.le⟩) t ht
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0)
  have a2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => f t - t • f₁ 0)
    (f' := fun t => f₁ t - f₁ 0) (a := 0) (b := h) (C := B * h)
    (fun s _ => by
      have := ((h₁ s).sub ((hasDerivAt_id s).smul_const (f₁ 0))).hasDerivWithinAt (s := Set.Icc 0 h)
      rwa [one_smul] at this)
    (fun s hs => a1 s ⟨hs.1, hs.2.le⟩) h ⟨hh, le_rfl⟩
  have e : h • f₁ 0 = f h - f 0 - (f h - h • f₁ 0 - (f 0 - (0 : ℝ) • f₁ 0)) := by rw [zero_smul]; ring
  have a3 : ‖h • f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * (h - 0) := by
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) a2)
  rwa [norm_smul, Real.norm_of_nonneg hh, sub_zero] at a3

theorem decay_of_decay_of_growth {G : Type} [Group G] {q : G → ℝ} (hq : ∀ g, 1 ≤ q g) {a : ℝ → G} (a0 : a 0 = 1)
    (ha : ∀ s t, a (s + t) = a s * a t) {c : ℝ} (hc : ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1, q (g * a t) ≤ c * q g)
    {ψ ψ₁ ψ₂ : G → ℂ} (h₁ : ∀ g, HasDerivAt (fun t => ψ (g * a t)) (ψ₁ g) 0)
    (h₂ : ∀ g, HasDerivAt (fun t => ψ₁ (g * a t)) (ψ₂ g) 0)
    (hψ : ∀ M : ℕ, ∃ C : ℝ, ∀ g, ‖ψ g‖ * q g ^ M ≤ C) {N : ℕ} {B : ℝ} (hB : ∀ g, ‖ψ₂ g‖ ≤ B * q g ^ N) (M : ℕ) :
    ∃ C : ℝ, ∀ g, ‖ψ₁ g‖ * q g ^ M ≤ C := by
  have shift : ∀ {χ χ₁ : G → ℂ}, (∀ g, HasDerivAt (fun t => χ (g * a t)) (χ₁ g) 0) →
      ∀ g s, HasDerivAt (fun t => χ (g * a t)) (χ₁ (g * a s)) s := fun {χ χ₁} h g s => by
    have h1 : HasDerivAt (fun t => χ (g * a s * a t)) (χ₁ (g * a s)) (s - s) := by rw [sub_self]; exact h _
    have h2 := h1.comp_sub_const s s
    simpa only [mul_assoc, ← ha, add_sub_cancel] using h2
  obtain ⟨C, hC⟩ := hψ (N + M + M)
  refine ⟨|c| ^ (N + M + M) * C + C + |B| * |c| ^ N, fun g => ?_⟩
  have q0 : 0 < q g := zero_lt_one.trans_le (hq g)
  have p1 : 1 ≤ q g ^ (N + M) := one_le_pow₀ (hq g)
  set h := (q g ^ (N + M))⁻¹ with hh
  have h0 : 0 < h := by positivity
  have h1 : h ≤ 1 := inv_le_one_of_one_le₀ p1
  have key := mul_norm_deriv_le (shift h₁ g) (shift h₂ g) h0.le (B := |B| * (|c| * q g) ^ N) fun t ht =>
    (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (zero_le_one.trans (hq _))
      ((hc g t ⟨by linarith [ht.1], ht.2.trans h1⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self _) q0.le)) N)
      (pow_nonneg (zero_le_one.trans (hq _)) N) (abs_nonneg _))
  simp only [a0, mul_one] at key
  have b1 : q g ≤ |c| * q (g * a h) := by
    have := hc (g * a h) (-h) ⟨by linarith, by linarith⟩
    rw [mul_assoc, ← ha, add_neg_cancel, a0, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans (hq _)))
  have b2 : ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ |c| ^ (N + M + M) * C :=
    calc ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ ‖ψ (g * a h)‖ * (|c| * q (g * a h)) ^ (N + M + M) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ q0.le b1 _) (norm_nonneg _)
      _ = |c| ^ (N + M + M) * (‖ψ (g * a h)‖ * q (g * a h) ^ (N + M + M)) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  calc ‖ψ₁ g‖ * q g ^ M = h * ‖ψ₁ g‖ * q g ^ (N + M + M) := by rw [hh]; field_simp; ring
    _ ≤ (‖ψ (g * a h)‖ + ‖ψ g‖ + |B| * (|c| * q g) ^ N * h * h) * q g ^ (N + M + M) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = ‖ψ (g * a h)‖ * q g ^ (N + M + M) + ‖ψ g‖ * q g ^ (N + M + M) + |B| * |c| ^ N := by
        rw [hh]; field_simp; ring
    _ ≤ _ := add_le_add (add_le_add b2 (hC g)) le_rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_add_smul (R : RealPoints θ V) (X : LieInf V) (s t : ℝ) :
    expInf θ V ((s + t) • X : LieInf V) = expInf θ V (s • X : LieInf V) * expInf θ V (t • X : LieInf V) := by
  have he := isExpFam_expInf R
  refine R.2.2.1 _ (he _).1 _ (mul_mem (he _).1 (he _).1) fun τ => ?_
  rw [R.2.2.2.1, (he _).2, (he _).2, (he _).2]
  change NormedSpace.exp ((s + t) • (X τ).1) = NormedSpace.exp (s • (X τ).1) * NormedSpace.exp (t • (X τ).1)
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)]

theorem expInf_zero_smul (R : RealPoints θ V) (X : LieInf V) : expInf θ V ((0 : ℝ) • X : LieInf V) = 1 := by
  have := expInf_add_smul R X 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem continuous_infNorm_expInf (R : RealPoints θ V) (X : LieInf V) (τ : D.what₂.Tau) :
    Continuous fun t : ℝ => infNorm θ V τ (expInf θ V (t • X : LieInf V)) := by
  have h1 : Continuous fun t : ℝ => NormedSpace.exp (t • (X τ).1) := by
    have : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ _
    letI : NormedAlgebra ℚ (AlgInf V) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h0 : Continuous fun t : ℝ => (NormedSpace.exp (t • jInf V X) : AlgInf V) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have h3 : Continuous fun u : AlgInf V => u τ := continuous_apply τ
    exact (h3.comp h0).congr fun t => exp_algInf V _ τ
  have h2 : Continuous (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  refine (h2.comp h1).nnnorm.congr fun t => ?_
  rw [infNorm, (isExpFam_expInf R _).2]
  rfl

theorem exists_quotHeight_mul_expInf_le (R : RealPoints θ V) (X : LieInf V) : ∃ c : ℝ, ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
    (quotHeight θ V (g * expInf θ V (t • X : LieInf V)) : ℝ) ≤ c * quotHeight θ V g := by
  have hinv : ∀ t : ℝ, (expInf θ V (t • X : LieInf V))⁻¹ = expInf θ V ((-t) • X : LieInf V) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← expInf_add_smul R, add_neg_cancel, expInf_zero_smul R])
  have hcont : Continuous fun t : ℝ => ((∏ τ, infHt θ V τ (expInf θ V (t • X : LieInf V)) : NNReal) : ℝ) := by
    refine NNReal.continuous_coe.comp (continuous_finsetProd _ fun τ _ => ?_)
    simp only [infHt, hinv]
    exact continuous_const.max ((continuous_infNorm_expInf R X τ).max
      ((continuous_infNorm_expInf R X τ).comp continuous_neg))
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hcont.continuousOn
  refine ⟨2 * c, fun g t ht => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 := (quotHeight_le (θ := θ) (g * expInf θ V (t • X : LieInf V)) hγ).trans
    ((congrArg _ (mul_assoc _ _ _).symm).trans_le
      (HeightCoset.height_mul_le θ V (γ * g) _ (isExpFam_expInf R (t • X)).1))
  have h2 := NNReal.coe_le_coe.2 (h1.trans (mul_le_mul_left hle _))
  rw [NNReal.coe_mul, NNReal.coe_mul] at h2
  refine h2.trans ((mul_le_mul_of_nonneg_left (hc ⟨t, ht, rfl⟩) (by positivity)).trans_eq ?_)
  push_cast
  ring

theorem IsRapidDecay.wordDer (R : RealPoints θ V) {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hl : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hs : IsSmoothInf V (expInf θ V) φ)
    (hg : IsUnifModerate θ V (expInf θ V) φ) (l : List (LieInf V)) :
    IsRapidDecay θ V (wordDer V (expInf θ V) l φ) := by
  have sm : ∀ l : List (LieInf V), Sm (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) l φ) := fun l => by
    rw [show φ = (⟨φ, hs⟩ : SmF θ V).1 from rfl, wordDer_eq R]
    exact Subtype.prop _
  induction l with
  | nil => exact h
  | cons X l ih =>
    obtain ⟨N, hN⟩ := hg
    obtain ⟨B, hB⟩ := hN (X :: X :: l)
    obtain ⟨c, hc⟩ := exists_quotHeight_mul_expInf_le R X
    refine decay_of_decay_of_growth (q := fun g => (quotHeight θ V g : ℝ))
      (fun g => by exact_mod_cast one_le_quotHeight g) (a := fun t => expInf θ V (t • X : LieInf V))
      (expInf_zero_smul R X) (expInf_add_smul R X) hc
      (ψ₂ := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) (X :: X :: l) φ)
      (fun g => ((sm l).differentiableAt g X).hasDerivAt) (fun g => ((sm (X :: l)).differentiableAt g X).hasDerivAt)
      ih (N := N) (B := |B| * 2 ^ N) fun g => ?_
    obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
    have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
    rw [← wordDer_left (expInf θ V) (hl γ hγ) _ g, mul_assoc, ← mul_pow]
    exact (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))

theorem isRapidDecay_foldr_Rder (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) : IsRapidDecay θ V (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  have hg' := (growth_iff hθ R ha hs').1 hg
  obtain ⟨l', rfl⟩ := exists_sigma_list l hl
  rw [foldr_Rder_eq R]
  exact (hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' hg' hc).wordDer R ha.left hs' hg' _

theorem cuspBounded_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) : GlobalTheory.Published.CuspBounded :=
  fun _ _ hθ _ _ ha hs hg hc l hl => (isRapidDecay_foldr_Rder hP hθ ha hs hg hc l hl).bounded

theorem memLp_of_bounded {φ : GA D V → ℂ} (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (p : ENNReal) :
    MemLp φ p (μ.restrict 𝓕) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  obtain ⟨C, hC⟩ := hb
  exact MemLp.of_bound hφ.measurable.aestronglyMeasurable C (.of_forall hC)

theorem memLp_two_of_cuspBounded (hP : GlobalTheory.Published.CuspBounded) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : MemLp φ 2 (μ.restrict 𝓕) :=
  memLp_of_bounded ha.cont (hP D θ hθ V φ ha hs hg hc [] fun _ h => absurd h List.not_mem_nil) μ 𝓕 hμ h𝓕 2

end GlobalTheory.CuspDecay

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField GlobalTheory.Orb Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (conv)
open scoped Topology ContDiff Matrix

noncomputable section

namespace GlobalTheory

namespace Published

def DixmierMalliavinFactorisation : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (n : Type) [Fintype n] [DecidableEq n] (ι : G →* Matrix n n ℂ),
    Topology.IsClosedEmbedding (ι.toHomUnits : G → GL n ℂ) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∀ V ∈ 𝓝 (1 : G), ∀ f ∈ CcMat ι,
      ∃ (N : ℕ) (g h : Fin N → G → ℂ),
        (∀ i, g i ∈ CcMat ι ∧ h i ∈ CcMat ι ∧ tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
        f = ∑ i, conv μ (g i) (h i)

end Published

namespace SmoothFactor

theorem isClosedEmbedding_of_locallyCompact {H G : Type*} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {φ : H →* G} (h : Topology.IsEmbedding φ) :
    Topology.IsClosedEmbedding φ := by
  refine ⟨h, isClosed_of_closure_subset fun x hx => ?_⟩
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  rw [h.nhds_eq_comap] at hK1
  obtain ⟨U', hU', hUK⟩ := hK1
  obtain ⟨U, hUU, hU, h1⟩ := mem_nhds_iff.1 hU'
  have hx' : x ∈ φ.range.topologicalClosure := hx
  have hi : x⁻¹ ∈ closure (range φ) := φ.range.topologicalClosure.inv_mem hx'
  obtain ⟨_, hs, s, rfl⟩ := mem_closure_iff.1 hi _ (hU.preimage (continuous_mul_const x)) (by simpa using h1)
  have h2 : φ s * x ∈ closure (range φ) :=
    φ.range.topologicalClosure.mul_mem (φ.range.le_topologicalClosure ⟨s, rfl⟩) hx'
  have h3 : U ∩ range φ ⊆ φ '' K := by
    rintro _ ⟨hy, y, rfl⟩
    exact ⟨y, hUK (hUU hy), rfl⟩
  obtain ⟨k, -, e⟩ := closure_minimal h3 (hK.image h.continuous).isClosed (hU.inter_closure ⟨hs, h2⟩)
  exact ⟨s⁻¹ * k, by rw [map_mul, map_inv, e, inv_mul_cancel_left]⟩

theorem isClosedEmbedding_toHomUnits {H n : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ}
    (h : Topology.IsEmbedding (matCoord ι)) : Topology.IsClosedEmbedding (ι.toHomUnits : H → GL n ℂ) := by
  have hc : Continuous ι := h.continuous
  have h1 : Continuous (ι.toHomUnits : H → GL n ℂ) := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  exact isClosedEmbedding_of_locallyCompact (Topology.IsEmbedding.of_comp h1 Units.continuous_val h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


open Classical in
variable (σ) in
def infMat : GInf σ J →* Matrix (Fin n × Σ w : InfinitePlace F, EmbOver E w) (Fin n × Σ w : InfinitePlace F, EmbOver E w) ℂ :=
  (Matrix.blockDiagonalRingHom (Fin n) _ ℂ).toMonoidHom.comp
    (MonoidHom.pi fun t => (archMat σ J t.2).comp (projInfArch σ J t.1))


open Classical in
variable (σ) in
theorem ccInf_eq : CcInf σ J = CcMat (infMat σ J) := by
  refine le_antisymm (ccSmooth_le (p := fun (y : (Fin n × Σ w : InfinitePlace F, EmbOver E w) → (Fin n × Σ w : InfinitePlace F, EmbOver E w) → ℂ) w τ i j => y (i, ⟨w, τ⟩) (j, ⟨w, τ⟩)) (by fun_prop) fun g => ?_)
    (ccSmooth_le (p := fun (y : ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) (a b : Fin n × Σ w : InfinitePlace F, EmbOver E w) => if a.2 = b.2 then y a.2.1 a.2.2 a.1 b.1 else 0) ?_ fun _ => rfl)
  · funext w τ i j
    exact (Matrix.blockDiagonal_apply_eq (fun t : Σ w : InfinitePlace F, EmbOver E w =>
      archMat σ J t.2 (projInfArch σ J t.1 g)) i j ⟨w, τ⟩).symm
  · refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    split_ifs
    · exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id _) _) _) _
    · exact contDiff_const


open Classical in
theorem isEmbedding_infMat (h : IsCMExt F E σ) : Topology.IsEmbedding (matCoord (infMat σ J)) := by
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun _ => Classical.arbitrary _
  have h1 := (Topology.IsEmbedding.piMap fun w => isEmbedding_archMat J h (τ w)).comp
    (infContEquivPi σ J).toHomeomorph.isEmbedding
  have h2 : Continuous (matCoord (infMat σ J)) :=
    Continuous.matrix_blockDiagonal (continuous_pi fun t : Σ w : InfinitePlace F, EmbOver E w =>
      (continuous_archMat σ J t.2).comp (continuous_projInfArch σ J t.1))
  refine Topology.IsEmbedding.of_comp (g := fun (y : (Fin n × Σ w : InfinitePlace F, EmbOver E w) → (Fin n × Σ w : InfinitePlace F, EmbOver E w) → ℂ) w i j => y (i, ⟨w, τ w⟩) (j, ⟨w, τ w⟩)) h2 (by fun_prop) ?_
  convert h1 using 1
  funext g w i j
  exact Matrix.blockDiagonal_apply_eq (fun t : Σ w : InfinitePlace F, EmbOver E w =>
      archMat σ J t.2 (projInfArch σ J t.1 g)) i j ⟨w, τ w⟩

theorem exists_sum_conv_ccInf (hDM : Published.DixmierMalliavinFactorisation) (h : IsCMExt F E σ)
    (μ : Measure (GInf σ J)) [μ.IsHaarMeasure] {V : Set (GInf σ J)} (hV : V ∈ 𝓝 1) {f : GInf σ J → ℂ}
    (hf : f ∈ CcInf σ J) :
    ∃ (N : ℕ) (g h : Fin N → GInf σ J → ℂ),
      (∀ i, g i ∈ CcInf σ J ∧ h i ∈ CcInf σ J ∧ tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
      f = ∑ i, conv μ (g i) (h i) := by
  classical
  rw [ccInf_eq] at hf ⊢
  exact hDM _ _ _ (isClosedEmbedding_toHomUnits (isEmbedding_infMat J h)) μ V hV f hf

end SmoothFactor

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
section
noncomputable section

open scoped TensorProduct ContDiff
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published


open GlobalTheory.Grow in
def CuspDecayBound : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ A N : ℕ,
      ∃ (L : Finset (List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ),
        (∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧
        ∀ φ : GA D V → ℂ, IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) →
          (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
            (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
              ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
          (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
            ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) →
          IsCuspFun V φ →
          ∀ c : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) → ℝ,
            (∀ l ∈ L, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ c l * height V g ^ A) →
            ∀ g, ‖φ g‖ * quotHeight V g ^ N ≤ C * ∑ l ∈ L, c l

end GlobalTheory.Published

namespace GlobalTheory.Grow

open GlobalTheory.SmoothForms
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (IsUnifModerate IsSmoothInf)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_comparison (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) ≤ C * quotHeight V g ∧
      quotHeight V g ≤ C * (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) := by
  obtain ⟨C, hC, h⟩ := height_comparison V hθ
  refine ⟨C * 2, by positivity, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight V g
    rw [mul_assoc]
    exact (NNReal.coe_le_coe.2 (GlobalTheory.CuspDecay.quotHeight_le g hγ)).trans
      ((h _).1.trans (mul_le_mul_of_nonneg_left h2 hC.le))
  · obtain ⟨γ, hγ, h2⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
    rw [mul_assoc]
    exact (quotHeight_le V g hγ).trans ((h _).2.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hC.le))

theorem rapidDec_iff_isRapidDecay (hθ : IsInfFam θ) {φ : GA D V → ℂ} :
    RapidDec V φ ↔ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ Continuous φ ∧ GlobalTheory.CuspDecay.IsRapidDecay θ V φ := by
  obtain ⟨K, hK, h⟩ := quotHeight_comparison hθ V
  have key : ∀ {a b x C : ℝ} {N : ℕ}, 0 ≤ a → 0 ≤ x → a ≤ K * b → x * b ^ N ≤ C → x * a ^ N ≤ K ^ N * C :=
    fun {a b x C N} ha hx h1 h2 => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h1 N) hx).trans (by
      rw [mul_pow, mul_left_comm]; exact mul_le_mul_of_nonneg_left h2 (pow_pos hK N).le)
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun N => ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (NNReal.coe_nonneg _) (norm_nonneg _) (h g).1 (hC g)⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (quotHeight_pos V g).le (norm_nonneg _) (h g).2 (hC g)⟩

theorem unifModGrowth_of_isUnifModerate (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsUnifModerate θ V (expInf θ V) φ) : UnifModGrowth V θ φ := by
  obtain ⟨K, hK, hh⟩ := height_comparison V hθ
  obtain ⟨A, hA⟩ := h
  have key : ∀ ψ : GA D V → ℂ, (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ A) →
      ModGrowthExp V A ψ := by
    rintro ψ ⟨C, hC⟩
    refine ⟨|C| * K ^ A, fun g => (hC g).trans ?_⟩
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hh g).1 A)
      (pow_nonneg (NNReal.coe_nonneg _) A) (abs_nonneg _)
  refine ⟨A, fun l hl => key _ ?_⟩
  obtain ⟨l', hl'⟩ := exists_sigma_list l hl
  rw [hl', foldr_Rder_eq ((_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V)]
  exact hA _

theorem unifModGrowth_of_isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    UnifModGrowth V θ φ :=
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  unifModGrowth_of_isUnifModerate hθ ((growth_iff hθ R h.toIsAutFun ((smooth_iff R φ).1 h.smooth)).1 h.growth)

theorem cuspRapidDecay_of_bound (hP : GlobalTheory.Published.CuspDecayBound) : GlobalTheory.Published.CuspRapidDecay := by
  intro D θ hθ V e he φ ha hs hg hc
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  obtain rfl := eq_expInf R he
  obtain ⟨A, hA⟩ := unifModGrowth_of_isUnifModerate hθ hg
  obtain ⟨U, hU, hφ⟩ := ha.level
  refine ((rapidDec_iff_isRapidDecay hθ).1 ⟨ha.left, ha.cont, fun N => ?_⟩).2.2
  obtain ⟨L, C, hL, h⟩ := hP D θ hθ V U hU A N
  choose! c hc' using hA
  exact ⟨_, h φ ha hφ ((smooth_iff R φ).2 hs) (fun l hl => ⟨c l, hc' l hl⟩) hc c fun l hl => hc' l (hL l hl)⟩

theorem rapidDec_of_unifModGrowth (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  (rapidDec_iff_isRapidDecay hθ).2 ⟨ha.left, ha.cont,
    hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' ((growth_iff hθ R ha hs').1 (hg.growth hθ)) hc⟩

theorem rapidDec_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  rapidDec_of_unifModGrowth hP hθ h.toIsAutFun h.smooth (unifModGrowth_of_isAutFunSm hθ h) hc

theorem RapidDec.integrableOn_fundamentalDomain {Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : IntegrableOn Φ 𝓕 μ :=
  h.integrableOn (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne

theorem RapidDec.integrableOn_mul_of_le {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) {C : ℝ} {A : ℕ} (hf : ∀ g, ‖f g‖ ≤ C * quotHeight V g ^ A) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨B, hB⟩ := h.decay A
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  refine Integrable.of_bound (hm.mul h.continuous.aestronglyMeasurable) (|C| * B) (.of_forall fun g => ?_)
  have hq := (pow_pos (quotHeight_pos V g) A).le
  calc ‖(f * Φ) g‖ = ‖f g‖ * ‖Φ g‖ := norm_mul _ _
    _ ≤ |C| * quotHeight V g ^ A * ‖Φ g‖ :=
        mul_le_mul_of_nonneg_right ((hf g).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)) (norm_nonneg _)
    _ = |C| * (‖Φ g‖ * quotHeight V g ^ A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB g) (abs_nonneg C)

theorem RapidDec.integrableOn_modGrowth_mul {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hf : ModGrowth V f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨C, A, hC⟩ := hf
  exact h.integrableOn_mul_of_le hμ h𝓕 hm (norm_le_quotHeight_pow hl hC)

end GlobalTheory.Grow

end
end

