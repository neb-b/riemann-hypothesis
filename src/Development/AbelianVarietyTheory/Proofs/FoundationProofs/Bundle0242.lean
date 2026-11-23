module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0228
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
section
open Filter Topology

namespace GlobalTheory.ProdThetaConj

theorem exists_ringHom_extend (R K : Type) [Field R] [Countable R] [Field K]
    (hK : Cardinal.mk K ≤ Cardinal.mk ℂ) (i : R →+* K) (j : R →+* ℂ) :
    ∃ s : K →+* ℂ, ∀ x, s (i x) = j x := by
  letI : Algebra R K := i.toAlgebra
  letI : Algebra R ℂ := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hct := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
    Cardinal.mk_le_aleph0 hC
  have hle : Cardinal.mk s ≤ Cardinal.mk t :=
    le_trans (Cardinal.mk_set_le s) (hct ▸ hK)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
  have hw : AlgebraicIndependent R (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let S := Algebra.adjoin R (Set.range ((↑) : s → K))
  let φ : S →ₐ[R] ℂ :=
    (MvPolynomial.aeval (((↑) : t → ℂ) ∘ e)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hs.1.aevalEquiv.symm.injective
  let _ : Algebra S ℂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul S ℂ := (faithfulSMul_iff_algebraMap_injective S ℂ).2 hφ
  have : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[R] ℂ := (IsAlgClosed.lift : K →ₐ[S] ℂ).restrictScalars R
  exact ⟨ψ.toRingHom, fun x => ψ.commutes x⟩

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem summable_prod_half_pow : Summable fun α : σ →₀ ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
  have h : Summable fun α : σ → ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
    classical
    refine summable_of_sum_le (c := ∏ _j : σ, (2 : ℝ)) (fun α => by positivity) fun u => ?_
    let n : ℕ := u.sup fun α => Finset.univ.sup α
    have hsub : u ⊆ Fintype.piFinset fun _ : σ => Finset.range (n + 1) := by
      intro α hα
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.le_sup (f := α) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun α => Finset.univ.sup α) hα)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : σ => Finset.range (n + 1)) (fun _ k => (1 / 2 : ℝ) ^ k)]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun _ _ => sum_geometric_two_le _
  exact h.comp_injective (i := fun α : σ →₀ ℕ => (α : σ → ℕ)) DFunLike.coe_injective

theorem tsum_of_entire {f : (σ → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0)
    (hc' : ∀ α, c α = MvPowerSeries.coeff α (GlobalTheory.taylor f)) (z : σ → ℂ) :
    ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j = f z := by
  have hb : ∀ R : ℝ, 0 < R → ∃ u : (σ →₀ ℕ) → ℝ, Summable u ∧ ∀ α, ∀ w ∈ Metric.ball (0 : σ → ℂ) R,
      ‖c α * ∏ j, w j ^ α j‖ ≤ u α := by
    intro R hR
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : σ → ℂ) (2 * R)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self (by positivity)))
    refine ⟨fun α => C * ∏ j, (1 / 2 : ℝ) ^ α j, summable_prod_half_pow.mul_left C, fun α w hw => ?_⟩
    have h1 := norm_pderivIter_le_of_differentiable (F := f) (a := 0) (r := fun _ => 2 * R) (M := C) α
      (fun _ => by positivity) (fun _ _ => by positivity) hf (fun y hy => hC y (by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
        intro k
        simpa using (hy k).le))
    rw [← hc, norm_mul, norm_prod, mul_div_assoc] at h1
    simp only [Complex.norm_natCast] at h1
    have h2 := le_of_mul_le_mul_left h1 (Finset.prod_pos fun k _ => by
      exact_mod_cast Nat.factorial_pos _)
    rw [norm_mul, norm_prod]
    calc ‖c α‖ * ∏ j, ‖w j ^ α j‖ ≤ (C / ∏ k, (2 * R) ^ α k) * ∏ j, R ^ α j := by
          refine mul_le_mul h2 (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_)
            (by positivity) (by positivity)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((norm_le_pi_norm w j).trans (mem_ball_zero_iff.1 hw).le) _
      _ = C * ∏ j, (1 / 2 : ℝ) ^ α j := by
          rw [div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← div_pow]
          congr 1
          field_simp
  have hsum : ∀ w : σ → ℂ, Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := fun w => by
    obtain ⟨u, hu, h⟩ := hb (‖w‖ + 1) (by positivity)
    exact Summable.of_norm_bounded hu fun α => h α w (by simp)
  have hd : DifferentiableOn ℂ (fun w : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, w j ^ α j) Set.univ := by
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun α => ?_) fun x _ => ?_
    · apply Differentiable.differentiableOn
      fun_prop
    · obtain ⟨u, hu, h⟩ := hb (‖x‖ + 1) (by positivity)
      exact ⟨_, Metric.isOpen_ball.mem_nhds (by simp), u, hu, h⟩
  have han := SCV.analyticOnNhd_of_differentiableOn isOpen_univ hd 0 (Set.mem_univ _)
  have hfa := SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  have heq := (taylor_eq_iff han hfa).1 (by
    ext α
    rw [← hc']
    exact ConjSeries.coeff_taylor_of_hasSum _ han (Eventually.of_forall fun w => (hsum w).hasSum) α
      (Nat.lt_succ_self _))
  exact SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hd hf.differentiableOn
    (Set.mem_univ 0) heq (Set.mem_univ z)

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

theorem tsum_taylor_mono (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (z : VC D N N') : ∑' α, Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z = F z := by
  let L := LinearMap.toContinuousLinearMap (GaussCauchy.curry D N N')
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext k
    exact (GaussCauchy.curry_single D N N' k).symm
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have h := tsum_of_entire (f := fun w => F (L w)) (hF.comp L.differentiable)
    (Formalism.MainNotions.TaylorLogMetric.taylor D F) (fun α => by
      have := GaussCauchy.factorial_mul_taylor D N N' F hF α
      rwa [Finsupp.prod_fintype _ _ (by simp)] at this)
    (fun α => by rw [ConjSeries.taylor_eq_coeff, hc, ← taylor_comp_clm L han])
    (fun k => z k.1 k.2.1 k.2.2)
  refine Eq.trans ?_ h
  refine tsum_congr fun α => ?_
  rw [mono, Finsupp.prod_fintype _ _ (by simp)]

theorem exists_endo_eq_cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {S : Set ℂ} (hS : S.Countable) :
    ∃ s : ℂ →+* ℂ, ∀ x ∈ S, x ∈ M → cj M ρ x = s x := by
  let R := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : R ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have : Countable R := by
    have h1 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
    simp only [sup_le_iff, le_refl, and_true]
    exact ⟨Cardinal.mk_le_aleph0, Cardinal.le_aleph0_iff_set_countable.2 h1⟩
  obtain ⟨s, hs⟩ := exists_ringHom_extend R ℂ le_rfl R.val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨s, fun x hx hM => ?_⟩
  have := hs ⟨x, IntermediateField.subset_adjoin ℚ _ ⟨hx, hM⟩⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos hM]
  exact this.symm

def ConjPair (D : D7) {N N' : ℕ} (s : ℂ →+* ℂ) (F F' : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ F' ∧
    MvPowerSeries.map s (taylorDir (coordV D) F) = taylorDir (coordV D) F'

variable {D : D7} {N N' : ℕ} {s : ℂ →+* ℂ}

theorem an0 {F : VC D N N' → ℂ} (h : Differentiable ℂ F) : AnalyticAt ℂ F 0 :=
  SCV.analyticOnNhd_of_differentiable h Set.univ 0 (Set.mem_univ _)

theorem ConjPair.taylor_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (α : Mono D N N') :
    s (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = Formalism.MainNotions.TaylorLogMetric.taylor D F' α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← h.2.2, MvPowerSeries.coeff_map]

theorem ConjPair.fnConj_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F')
    {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    (hs : ∀ α, cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = s (Formalism.MainNotions.TaylorLogMetric.taylor D F α)) :
    fnConj D M ρ F = F' := by
  funext z
  rw [← tsum_taylor_mono D h.2.1 z, fnConj]
  refine tsum_congr fun α => ?_
  rw [← h.taylor_eq, ← hs, cj]

theorem taylor_const_mul {F : VC D N N' → ℂ} (h : Differentiable ℂ F) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => a * F z) α = a * Formalism.MainNotions.TaylorLogMetric.taylor D F α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff]
  have := taylorDir_smul (coordV D) a (an0 h)
  rw [show (fun z => a * F z) = a • F from rfl, this, MvPowerSeries.coeff_smul]

theorem ConjPair.const_mul {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (a : ℂ) :
    ConjPair D s (fun z => a * F z) (fun z => s a * F' z) := by
  refine ⟨h.1.const_mul a, h.2.1.const_mul _, ?_⟩
  ext α
  rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff, ← ConjSeries.taylor_eq_coeff,
    taylor_const_mul h.1, taylor_const_mul h.2.1, map_mul, h.taylor_eq]

theorem ConjPair.sum {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∑ i, F i z) (fun z => ∑ i, F' i z) := by
  refine ⟨Differentiable.fun_sum fun i _ => (h i).1, Differentiable.fun_sum fun i _ => (h i).2.1, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [taylorDir_sum _ _ fun i _ => an0 (h i).1, taylorDir_sum _ _ fun i _ => an0 (h i).2.1, map_sum]
  exact Finset.sum_congr rfl fun i _ => (h i).2.2

theorem ConjPair.prod {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∏ i, F i z) (fun z => ∏ i, F' i z) := by
  have hp : ∀ G : κ → VC D N N' → ℂ, (∀ i, Differentiable ℂ (G i)) →
      Differentiable ℂ fun z => ∏ i, G i z := fun G hG z =>
    (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ => (hG i z).hasFDerivAt).differentiableAt
  refine ⟨hp _ fun i => (h i).1, hp _ fun i => (h i).2.1, ?_⟩
  rw [taylorDir_prod _ _ fun i _ => an0 (h i).1, taylorDir_prod _ _ fun i _ => an0 (h i).2.1, map_prod]
  exact Finset.prod_congr rfl fun i _ => (h i).2.2

theorem lineDerivList_comp_form {κ : Type*} (u : κ → VC D N N') (ℓ : VC D N N' →ₗ[ℂ] ℂ) (g : ℂ → ℂ)
    (l : List κ) : lineDerivList ℂ (l.map u) (fun z => g (ℓ z)) 0 =
      (l.map fun k => ℓ (u k)).prod * iteratedDeriv l.length g 0 := by
  rw [lineDerivList_comp_linearMap, List.map_map]
  have h1 := lineDerivList_map_smul (fun k => ℓ (u k)) (fun _ => (1 : ℂ)) l g
  have h2 := lineDerivList_replicate l.length (1 : ℂ) g 0 (0 : ℂ)
  simp only [smul_eq_mul, mul_one, List.map_const', zero_add] at h1 h2
  simp only [map_zero, Function.comp_def, h1, h2]

theorem ConjPair.comp_form {g g' : ℂ → ℂ} (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (hc : ∀ n, s (coef1 g n) = coef1 g' n) (ℓ ℓ' : VC D N N' →ₗ[ℂ] ℂ)
    (hℓ : ∀ k, s (ℓ (coordV D k)) = ℓ' (coordV D k)) :
    ConjPair D s (fun z => g (ℓ z)) (fun z => g' (ℓ' z)) := by
  have h1 : Differentiable ℂ fun z => g (ℓ z) :=
    hg.comp (LinearMap.toContinuousLinearMap ℓ).differentiable
  have h2 : Differentiable ℂ fun z => g' (ℓ' z) :=
    hg'.comp (LinearMap.toContinuousLinearMap ℓ').differentiable
  refine ⟨h1, h2, ?_⟩
  ext α
  have hd : ∀ n, s (iteratedDeriv n g 0) = iteratedDeriv n g' 0 := fun n => by
    have := hc n
    rw [coef1, coef1, map_div₀, map_natCast] at this
    exact (div_left_inj' (by exact_mod_cast n.factorial_ne_zero)).1 this
  rw [MvPowerSeries.coeff_map,
    coeff_taylorDir_eq_lineDerivList _ (an0 h1) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ (an0 h2) (Multiset.coe_toList _),
    lineDerivList_comp_form, lineDerivList_comp_form, map_mul, map_mul, map_inv₀, map_natCast, hd,
    map_list_prod, List.map_map]
  simp only [Function.comp_def, hℓ]

end GlobalTheory.ProdThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestKTypeOfIrreducibleGeneratedModule
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestType

open GlobalTheory.TensorHW

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def zc (p q : ℕ) : Mat p q :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => 0))

lemma zc_eq : zc p q = ∑ i : Fin p, Eab (Sum.inl i) (Sum.inl i) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [zc, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp [Finset.filter_eq']
  · rw [if_neg h, eq_comm]
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, rfl⟩
    exact h rfl

lemma act_zc (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) :
    act (zc p q) x = ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [zc_eq, map_sum, LinearMap.sum_apply]

lemma zc_comm {X : Mat p q} (hX : IsKC X) : zc p q * X = X * zc p q := by
  ext a b
  rw [zc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (.inl a) (.inr b) (by simp [sameBlock])]
  · simp [hX (.inr a) (.inl b) (by simp [sameBlock])]
  · simp

lemma kstable_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (t : ℂ) :
    KStable act (Module.End.eigenspace (act (zc p q)) t) := by
  intro X hX w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have h := hL (zc p q) X
  rw [zc_comm hX, sub_self, map_zero, eq_comm, sub_eq_zero] at h
  have h2 := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply] at h2
  rw [h2, hw, map_smul]

lemma kstable_inf {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V}
    (hA : KStable act A) (hB : KStable act B) : KStable act (A ⊓ B) :=
  fun X hX w hw => ⟨hA X hX w hw.1, hB X hX w hw.2⟩

lemma wt_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) :
    x ∈ Module.End.eigenspace (act (zc p q)) ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, act_zc]
  simp only [mem_wt.1 hx]
  rw [← Finset.sum_smul]
  push_cast
  rfl

lemma eig_le (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) :
    f.eigenspace t ≤ ⨆ m : ℕ, ⨆ _ : c + m = t, N m := by
  intro x hx
  have h1 : (⊤ : Submodule ℂ V) ≤ (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ⊔ ⨆ s, ⨆ _ : s ≠ t, f.eigenspace s := by
    rw [← hN]
    refine iSup_le fun m => ?_
    by_cases hm : c + m = t
    · exact le_sup_of_le_left (le_iSup₂_of_le m hm le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (c + m) hm (h m))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top : x ∈ ⊤))
  have ha' : a ∈ f.eigenspace t := by
    refine (iSup₂_le fun m hm => ?_ : (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ≤ f.eigenspace t) ha
    rw [← hm]; exact h m
  have hb' : b ∈ f.eigenspace t := by
    simpa using Submodule.sub_mem _ hx ha'
  have hd := Module.End.eigenspaces_iSupIndep f t
  have : b = 0 := (Submodule.disjoint_def.1 hd) b hb' hb
  simpa [this] using ha

lemma eig_mem (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) {x : V} (hx : x ∈ f.eigenspace t) (h0 : x ≠ 0) :
    ∃ m : ℕ, t = c + m ∧ x ∈ N m := by
  have h1 := eig_le f c N hN h t hx
  by_cases hm : ∃ m : ℕ, c + m = t
  · obtain ⟨m, rfl⟩ := hm
    refine ⟨m, rfl, (iSup₂_le fun k hk => ?_ : (⨆ k : ℕ, ⨆ _ : c + k = c + m, N k) ≤ N m) h1⟩
    have : k = m := by exact_mod_cast add_left_cancel hk
    rw [this]
  · refine absurd ?_ h0
    exact (iSup₂_le fun k hk => absurd ⟨k, hk⟩ hm : (⨆ k : ℕ, ⨆ _ : c + k = t, N k) ≤ ⊥) h1

lemma eig_unique {f : Module.End ℂ V} {s t : ℂ} {x : V} (hs : x ∈ f.eigenspace s)
    (ht : x ∈ f.eigenspace t) (h0 : x ≠ 0) : s = t := by
  rw [Module.End.mem_eigenspace_iff] at hs ht
  exact smul_left_injective ℂ h0 (hs.symm.trans ht)

def rk : Ix p q → ℕ := Sum.elim (fun i => i.1) (fun j => p + j.1)

lemma rk_inj : Function.Injective (rk : Ix p q → ℕ) := by
  rintro (a | a) (b | b) h <;> simp only [rk, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Fin.ext h]
  · have := a.2; omega
  · have := b.2; omega
  · rw [Fin.ext (add_left_cancel h)]

lemma same_equiv : Equivalence (sameBlock : Ix p q → Ix p q → Prop) := by
  refine ⟨same_refl, ?_, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [sameBlock]
  · rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]

lemma pos_of_rk {a b : Ix p q} (h : sameBlock a b) (hr : rk a < rk b) : posC a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, rk, posC]

lemma hw_irr {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {W : Submodule ℂ V}
    (hW : KStable act W) (hirr : ∀ N : Submodule ℂ V, N ≤ W → KStable act N → N = ⊥ ∨ N = W)
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ W) (hh : IsHW act μ v) :
    (∀ x ∈ W, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧
    ∀ (ν : Ix p q → ℚ), ∀ x ∈ W, x ≠ 0 → x ∈ wtSub act ν →
      ν = μ ∨ ∑ a, (rk a : ℚ) * μ a < ∑ a, (rk a : ℚ) * ν a := by
  obtain ⟨U, hvU, hS, hmin, h1, h2⟩ := GlobalTheory.ExtremalGen.exists_generated p q V act hL sameBlock same_equiv rk rk_inj μ v hh.2.1
    (fun a b hab hr => by
      have := hh.2.2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, SetLike.mem_coe] at this
      exact this a b (pos_of_rk hab hr))
  have hUW : U ≤ W := hmin W hv fun a b hab _ x hx => hW _ (isKC_Eab (same_equiv.symm hab)) x hx
  have hU : U = W := by
    refine (hirr U hUW fun X hX w hw => kc_ind act U w (fun a b hab => hS a b hab w hw) hX).resolve_left ?_
    rintro rfl
    exact hh.1 (by simpa using hvU)
  subst hU
  exact ⟨h1, h2⟩

theorem lowest : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V), IrrGK M → FiniteDimensional ℂ W → KStable M.act W → (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) → (∃ e ∈ W, IsHW M.act Λ e) → (∀ e ∈ W, KilledByLower M.act e) → genSub M.act (W : Set M.V) = ⊤ → IsLowestType M Λ W ∧ Module.finrank ℂ ↥(hwSub M.act Λ) = 1 ∧ ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = (((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) + m) • x := by
  intro p q M Λ W hM hfd hW hirr hex hlow hgen
  obtain ⟨e, heW, he⟩ := hex
  set c : ℂ := ((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) with hc
  have hWc : W ≤ Module.End.eigenspace (M.act (zc p q)) c := by
    rcases hirr _ inf_le_left (kstable_inf hW (kstable_eig M.lie c)) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h e ⟨heW, wt_eig he.2.1⟩) he.1
    · exact h.ge.trans inf_le_right
  obtain ⟨N, hN0, hNfd, hNtop, hN⟩ := GlobalTheory.FockGrade.exists_grading p q M.V M.act M.lie W c hfd hW hlow
    (fun x hx => by rw [← act_zc]; exact Module.End.mem_eigenspace_iff.1 (hWc hx))
  rw [hgen] at hNtop
  have hNe : ∀ m : ℕ, N m ≤ Module.End.eigenspace (M.act (zc p q)) (c + m) := fun m x hx => by
    rw [Module.End.mem_eigenspace_iff, act_zc]; exact hN m x hx
  have hcW : Module.End.eigenspace (M.act (zc p q)) c ≤ W := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact W.zero_mem
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe c hx h0
    have : m = 0 := by exact_mod_cast left_eq_add.1 hm
    rwa [this, hN0] at hxm
  have hline := hw_irr M.lie hW hirr heW he
  refine ⟨⟨hM, hfd, hW, hirr, ⟨e, heW, he⟩, fun x => ⟨fun hx => ⟨W, hfd, hx, hW, ?_⟩, ?_⟩, hlow, hgen, ?_⟩, ?_,
    N, hNfd, hNtop, hN⟩
  · intro ν w hw hh
    rcases hline.2 ν w hw hh.1 hh.2.1 with h | h
    · exact h
    rcases (hw_irr M.lie hW hirr hw hh).2 Λ e heW he.1 he.2.1 with h' | h'
    · exact h'.symm
    · exact absurd h (not_lt.2 h'.le)
  · rintro ⟨W', hfd', hx, hW', hall⟩
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act W' (fun a y hy => hW' _ (isKC_Eab (same_refl a)) y hy) x hx (M.wts x)
    refine (iSup_le fun μ y hy => ?_ : (⨆ μ : Ix p q → ℚ, W' ⊓ wtSub M.act μ) ≤ W) h1
    by_cases h0 : y = 0
    · rw [h0]; exact W.zero_mem
    have hy2 := wt_eig hy.2
    have := hfd'
    obtain ⟨ν, v, hv, hh⟩ := GlobalTheory.ExistsHW.exists_highestWeight p q M _
      (Submodule.finiteDimensional_of_le inf_le_left) (kstable_inf hW' (kstable_eig M.lie
        ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ)))
      (fun h => h0 ((Submodule.eq_bot_iff _).1 h y ⟨hy.1, hy2⟩))
    obtain rfl := hall ν v hv.1 hh
    have := eig_unique hv.2 (wt_eig hh.2.1) hh.1
    rw [this] at hy2
    exact hcW hy2
  · intro μ x h0 hx
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe _ (wt_eig hx) h0
    refine ⟨m, by rw [hc] at hm; exact_mod_cast hm, ?_, fun hxW => ?_⟩
    · rintro rfl
      rwa [hN0] at hxm
    · have := eig_unique (hWc hxW) (hNe m hxm) h0
      exact_mod_cast left_eq_add.1 this
  · have : hwSub M.act Λ = Submodule.span ℂ {e} := by
      refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 he.2)
      obtain ⟨a, rfl⟩ := hline.1 x (hcW (wt_eig hx.1)) hx.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    rw [this]
    exact finrank_span_singleton he.1

end GlobalTheory.LowestType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBound
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem extNorm_eq_nat_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  intro K _ _ _ ι _ n lam R hR hS
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hw : ∀ τ i, (lam τ).natW i ≤ ⌊R⌋₊ := by
    intro τ i
    have hn : 0 < n := Fin.pos i
    have h := hS τ i ⟨n - 1, by omega⟩
    have h2 : (lam τ).w i - (lam τ).w ⟨n - 1, by omega⟩ ≤ (⌊R⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hR0]
      exact Int.le_floor.mpr h
    unfold DomWeight.natW DomWeight.detShift
    rw [dite_eq_left hn]
    omega
  choose s hs0 hs1 hs2 using fun τ => _root_.GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat n (lam τ) ⌊R⌋₊ (hw τ)
  refine ⟨∏ τ, s τ, Finset.prod_pos fun τ _ => hs0 τ, ?_, ?_⟩
  · unfold extNorm
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun τ _ => hs2 τ K
  · rw [Nat.cast_prod, Real.log_prod (fun τ _ => by exact_mod_cast (hs0 τ).ne')]
    have hb := _root_.GlobalTheory.log_factorial_pow_mul_factorial_pow_le n ⌊R⌋₊ R hR (Nat.floor_le hR0)
    have h1 : ∀ τ, Real.log (s τ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := fun τ =>
      le_trans (Real.log_le_log (by exact_mod_cast hs0 τ) (by exact_mod_cast hs1 τ)) hb
    calc ∑ τ, Real.log (s τ) ≤ ∑ _τ : ι, 4 * (n : ℝ) * R * Real.log (n * R) :=
          Finset.sum_le_sum fun τ _ => h1 τ
      _ = bound (Fintype.card ι) n R := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold bound
          ring

end GlobalTheory
end

