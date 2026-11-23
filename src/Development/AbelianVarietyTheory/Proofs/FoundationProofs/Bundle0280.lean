module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitian
section
noncomputable section
namespace GlobalTheory.CartanInt.HermChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

def herm {n : Type} (S : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ)

theorem herm_apply {n : Type} (S : n → n → ℝ) (i j : n) :
    herm S i j = (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ) := rfl

theorem herm_conjTranspose {n : Type} (S : n → n → ℝ) : (herm S)ᴴ = herm S := by
  ext i j
  rw [Matrix.conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; ring
  · simp only [Complex.star_def, Complex.conj_im]; ring

theorem continuous_herm_entry {X n : Type} [TopologicalSpace X] {f : X → n → n → ℝ}
    (hf : ∀ i j, Continuous fun x => f x i j) (i j : n) : Continuous fun x => herm (f x) i j := by
  have e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) +
      (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [herm_apply, Complex.mk_eq_add_mul_I]
  rw [e]
  have h1 := hf i j
  have h2 := hf j i
  fun_prop

theorem sum_norm_sq_herm_sub {n : Type} [Fintype n] (S T : n → n → ℝ) :
    ∑ i, ∑ j, ‖herm S i j - herm T i j‖ ^ 2 = ∑ i, ∑ j, (S i j - T i j) ^ 2 := by
  have h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 =
      (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem herm_re_add_im {n : Type} (H : n → n → ℂ) (hH : ∀ i j, star (H j i) = H i j) (i j : n) :
    herm (fun i j => (H i j).re + (H i j).im) i j = H i j := by
  have h1 := congrArg Complex.re (hH i j)
  have h2 := congrArg Complex.im (hH i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2
  rw [herm_apply]
  apply Complex.ext
  · show _ / (2 : ℝ) = _
    linarith
  · show _ / (2 : ℝ) = _
    linarith

theorem abs_re_add_im_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) : |z.re + z.im| ≤ 89 / 20 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖z‖ ≤ 3.1416 := hz.trans Real.pi_lt_d4.le
  have h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
  refine abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2
  nlinarith [sq_nonneg (z.re - z.im)]

theorem exists_chart : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q,
    Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧
    (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧
    ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) →
      ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  intro p q
  refine ⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0
    (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_,
    fun H hH hK hb => ?_⟩
  · refine continuous_matrix fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b
    · exact continuous_const
    · exact continuous_const
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b
  · simp only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))),
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]
    simp [Fintype.sum_sum_type]
  · have hs : ∀ a b, star (H b a) = H a b := fun a b => by
      rw [← Matrix.conjTranspose_apply, hH]
    refine ⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im)
      (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · exact herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b
    · rintro (x | x)
      · exact abs_re_add_im_le (hb _ _)
      · exact abs_re_add_im_le (hb _ _)

end GlobalTheory.CartanInt.HermChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

namespace GlobalTheory.CartanInt.ExpLocal

attribute [local instance] GlobalTheory.CompactDualExists.sumNormedAddCommGroup
  GlobalTheory.CompactDualExists.sumNormedSpace

theorem l1_eq_norm {n : Type} [Fintype n] (A : Matrix n n ℂ) : l1 A = ‖A‖ :=
  (GlobalTheory.CompactDualExists.sum_norm_def A).symm

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < r →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 21 * ‖Y‖ := by
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def (c := 1 / 21) (by norm_num)
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY => ?_⟩
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  exact h3

theorem exp_log_near_one : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  intro p q
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q)
  have hN := GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds p q r hr
  rw [GlobalTheory.UpqTopology.isInducing_mat.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hsub⟩ := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨min r ε, lt_min hr hε, fun Y hY => ?_, fun g hg => ?_⟩
  · rw [l1_eq_norm] at hY
    rw [l1_eq_norm, l1_eq_norm]
    have h1 := H Y (hY.trans_le (min_le_left _ _))
    have h2 := norm_le_norm_add_norm_sub' (NormedSpace.exp Y - 1) Y
    have h3 := norm_nonneg Y
    linarith
  · rw [l1_eq_norm] at hg
    have hg' : UpqT.mat g ∈ Metric.ball (UpqT.mat (1 : UpqT p q)) ε := by
      rw [mem_ball_iff_norm, mat_one]
      exact hg.trans_le (min_le_right _ _)
    obtain ⟨X, hX, hgX⟩ := hsub (show g ∈ UpqT.mat ⁻¹' T from hball hg')
    refine ⟨X, hgX, ?_⟩
    have hX' : l1 (X : Mat p q) < r := hX
    rw [l1_eq_norm] at hX'
    rw [l1_eq_norm, l1_eq_norm, hgX]
    have h1 := H X hX'
    have h2 := norm_le_norm_add_norm_sub (NormedSpace.exp (X : Mat p q) - 1) (X : Mat p q)
    linarith

end GlobalTheory.CartanInt.ExpLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantMeasureLowerBoundOfChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem invariant_measure_lower_bound_of_chart :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype ι] (mK : Measure G) [IsProbabilityMeasure mK] (K U : Set G) (θ : (ι → ℝ) → G) (T δ : ℝ), Continuous θ → IsClosed U → mK Kᶜ = 0 → (∀ R, Measure.map (fun x => θ R * x) mK = mK) → 0 < δ → 0 ≤ T → (∀ x ∈ K, ∃ R₀ : ι → ℝ, (∀ i, |R₀ i| ≤ T) ∧ ∀ R : ι → ℝ, (∀ i, |R i - R₀ i| ≤ δ) → (θ R)⁻¹ * x ∈ U) → ENNReal.ofReal ((δ / (T + δ)) ^ Fintype.card ι) ≤ mK U := by
  intro G ι _ _ _ _ _ _ _ mK _ K U θ T δ hθ hU hK hinv hδ hT hch
  have hTδ : 0 < T + δ := by linarith
  set Q : Set (ι → ℝ) := Metric.closedBall 0 (T + δ) with hQ
  set S : Set ((ι → ℝ) × G) := {p | (θ p.1)⁻¹ * p.2 ∈ U} with hS
  have hSc : IsClosed S := hU.preimage (by fun_prop : Continuous fun p : (ι → ℝ) × G => (θ p.1)⁻¹ * p.2)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hQv : volume Q = ENNReal.ofReal ((2 * (T + δ)) ^ Fintype.card ι) :=
    Real.volume_pi_closedBall _ hTδ.le
  have hsec : ∀ R, mK (Prod.mk R ⁻¹' S) = mK U := by
    intro R
    have hm : MeasurableSet (Prod.mk R ⁻¹' S) := measurable_prodMk_left hSm
    conv_lhs => rw [← hinv R]
    rw [Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [hS]
  have h1 : ((volume.restrict Q).prod mK) S = mK U * volume Q := by
    rw [Measure.prod_apply hSm]
    simp [hsec]
  have h2 : ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ≤ ((volume.restrict Q).prod mK) S := by
    rw [Measure.prod_apply_symm hSm]
    have hae : ∀ᵐ x ∂mK, x ∈ K := hK
    calc ENNReal.ofReal ((2 * δ) ^ Fintype.card ι)
        = ∫⁻ _x, ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ∂mK := by simp
      _ ≤ _ := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        obtain ⟨R₀, hR₀, hR⟩ := hch x hx
        have hm : MeasurableSet ((fun R => (R, x)) ⁻¹' S) := measurable_prodMk_right hSm
        rw [Measure.restrict_apply hm, ← Real.volume_pi_closedBall R₀ hδ.le]
        refine measure_mono fun R hRm => ?_
        have hd : ∀ i, |R i - R₀ i| ≤ δ := fun i => by
          have := (dist_pi_le_iff hδ.le).1 (Metric.mem_closedBall.1 hRm) i
          rwa [Real.dist_eq] at this
        refine ⟨hR R hd, ?_⟩
        rw [hQ, Metric.mem_closedBall, dist_pi_le_iff hTδ.le]
        intro i
        have h3 := abs_le.1 (hd i)
        have h4 := abs_le.1 (hR₀ i)
        rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  rw [h1, hQv] at h2
  have hpos : 0 < (2 * (T + δ)) ^ Fintype.card ι := by positivity
  have he : (δ / (T + δ)) ^ Fintype.card ι
      = (2 * δ) ^ Fintype.card ι / (2 * (T + δ)) ^ Fintype.card ι := by
    rw [← div_pow, mul_div_mul_left _ _ (two_ne_zero)]
  rw [he, ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_of_le_mul h2

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGK
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem irrU_of_dense_graded_irrGK :
    ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  intro p q T σ M j hinj hd hder hirr N k lam hfin hN _ hlam heig
  haveI := hirr.1
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hreal : ∀ Y ∈ upq p q, ∀ y, j y ∈ S → j (M.act Y y) ∈ S := by
    intro Y hY y hy
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder Y hY y)
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (inner ℂ w (j (M.act Y y))) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
      exact (Submodule.inner_left_of_mem_orthogonal (hinv _ _ hy) hw).symm
    exact h2.unique (hasDerivAt_const _ _)
  have hstab : ∀ Z, ∀ y ∈ S.comap j, M.act Z y ∈ S.comap j := by
    intro Z y hy
    obtain ⟨X, hX, Y, hY, rfl⟩ := GlobalTheory.FockTensor.exists_upq_add Z
    rw [Submodule.mem_comap] at hy ⊢
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact S.add_mem (hreal X hX y hy) (S.smul_mem _ (hreal Y hY y hy))
  rcases hirr.2 _ hstab with h | h
  · left
    have hperp : ∀ b ∈ Sᗮ, σ.π k b ∈ Sᗮ := by
      intro b hb
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [GlobalTheory.FockTensor.inner_pi_left]
      exact Submodule.inner_left_of_mem_orthogonal (hinv _ _ hu) hb
    have hdense : Dense ((⨆ m, (N m).map j : Submodule ℂ σ.H) : Set σ.H) := by
      rw [← Submodule.map_iSup, hN, Submodule.map_top]
      exact hd
    have hle : (⨆ m, (N m).map j : Submodule ℂ σ.H) ≤ Sᗮ := by
      refine iSup_le fun m => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := S.exists_add_mem_mem_orthogonal (j x)
      have he := heig m x hx
      rw [hab, map_add (f := _), smul_add] at he
      have hdiff : σ.π k a - lam m • a = lam m • b - σ.π k b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have h1 : σ.π k a - lam m • a ∈ S := S.sub_mem (hinv _ _ ha) (S.smul_mem _ ha)
      have h2 : σ.π k a - lam m • a ∈ Sᗮ := by
        rw [hdiff]
        exact Sᗮ.sub_mem (Sᗮ.smul_mem _ hb) (hperp b hb)
      have h3 : σ.π k a = lam m • a :=
        sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2))
      have h4 := GlobalTheory.mem_of_isometry_eigen_of_dense_iSup σ.H (σ.π k) (σ.isom k)
        (fun m => (N m).map j) lam hlam (fun m => by haveI := hfin m; infer_instance)
        (by rintro m _ ⟨x, hx, rfl⟩; exact heig m x hx) hdense m a h3
      obtain ⟨x', -, hx'⟩ := h4
      have h5 : x' ∈ S.comap j := by rw [Submodule.mem_comap, hx']; exact ha
      rw [h, Submodule.mem_bot] at h5
      rw [h5, map_zero] at hx'
      rw [hab, ← hx', zero_add]
      exact hb
    rw [← Submodule.orthogonal_eq_top_iff, eq_top_iff]
    intro v _
    exact closure_minimal hle S.isClosed_orthogonal (hdense v)
  · right
    rw [eq_top_iff]
    intro v _
    refine closure_minimal ?_ hS (hd v)
    rintro _ ⟨x, rfl⟩
    have : x ∈ S.comap j := by rw [h]; trivial
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedKFin

variable {p q : ℕ}

theorem kset_one (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    cases a <;> simp [sameBlock] at hab
  simp [Matrix.one_apply, this]

theorem kset_mul (T : GrpData p q) {g h : T.G} (hg : g ∈ T.Kset) (hh : h ∈ T.Kset) :
    g * h ∈ T.Kset := by
  intro a b hab
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := by
      cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
    rw [hh c b hcb, mul_zero]
  · rw [hg a c hac, zero_mul]

theorem map_stable (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q)
    (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    {g : T.G} (hg : g ∈ T.Kset) : ∀ x ∈ W.map j, σ.π g x ∈ W.map j := by
  have hcl := GlobalTheory.CoverKGen.kset_gen p q hpq T g hg
  suffices h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1
  clear hg
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨Y, ⟨hY, hKC⟩, rfl⟩ := hg
    have hf := GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)
    have hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY 1 (-1)
      rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at this
      exact (eq_inv_of_mul_eq_one_right this.symm).symm
    refine ⟨?_, ?_⟩
    · have := hf 1
      simpa only [one_smul] using this
    · rw [hinv]; exact hf (-1)
  | one => simp
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul]; exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 x hx)
  | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isHCMod_of_graded : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  intro p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig
  refine ⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨W, hWf, hv, hW⟩ := M.kfin v
    have hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · have hsup : (⨆ m, (N m).map j) = LinearMap.range j := by
      rw [← Submodule.map_iSup, htop, Submodule.map_top]
    have hle := GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k)
      (fun m => (N m).map j) lam hlam (fun m => inferInstance)
      (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy)
      (by rw [hsup]; exact hd)
      (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨g, rfl⟩ := hw
          refine Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩
          simp only [map_mul]
          rfl
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
    rw [hsup] at hle
    exact hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)

end GlobalTheory.GradedKFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotientStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralExpNegMulSumNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem integral_exp_neg_mul_norm_complex (b : ℝ) (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-(b * ‖z‖)) = 2 * Real.pi / b ^ 2 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) (b := b) le_rfl hb
  simp only [Real.rpow_one, neg_mul, div_one] at h
  rw [h]
  have h3 : Real.Gamma (2 + 1) = 2 := by
    have := Real.Gamma_nat_eq_factorial 2
    simpa [Nat.factorial] using this
  rw [h3, Real.rpow_neg hb.le, Real.rpow_two]
  field_simp

theorem lintegral_exp_neg_mul_sum_norm (p q : ℕ) (b : ℝ) (hb : 0 < b) :
    ∫⁻ B : Fin p → Fin q → ℂ, ENNReal.ofReal (Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖))) =
      ENNReal.ofReal ((2 * Real.pi / b ^ 2) ^ (p * q)) := by
  have h1 := integral_exp_neg_mul_norm_complex b hb
  have hne : (2 * Real.pi / b ^ 2) ≠ 0 := by positivity
  have hi : Integrable (fun z : ℂ => Real.exp (-(b * ‖z‖))) :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact hne)
  have hprod : ∀ B : Fin p → Fin q → ℂ, Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖)) =
      ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) := by
    intro B
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  have hrow : Integrable (fun v : Fin q → ℂ => ∏ j, Real.exp (-(b * ‖v j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖))) (fun _ => hi)
  have hall : Integrable (fun B : Fin p → Fin q → ℂ => ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖))) (fun _ => hrow)
  have hrowv : ∫ v : Fin q → ℂ, ∏ j, Real.exp (-(b * ‖v j‖)) = (2 * Real.pi / b ^ 2) ^ q := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖)))]
    simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hallv : ∫ B : Fin p → Fin q → ℂ, ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) =
      (2 * Real.pi / b ^ 2) ^ (p * q) := by
    rw [volume_pi, integral_fintype_prod_eq_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖)))]
    simp only [hrowv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm q p]
  simp only [hprod]
  rw [← hallv, ofReal_integral_eq_lintegral_ofReal hall]
  exact Filter.Eventually.of_forall fun B => by positivity

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanAStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullB_th0_mem_tr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | exact GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | (intros; apply GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan <;> assumption)
end

