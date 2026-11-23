module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBdM

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.DiscrHolds
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT

namespace PositivityTheory.KB.LocalOverlapAverage

theorem discr_holds : Discr := by
  unfold Discr
  intro L _ _ N K hK
  have hc : Continuous (fun γ : Sp L N => fun (w : InfinitePlace L) (i j : Fin N) =>
      ((γ w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) := by
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set S : Set (𝓞 L) := {x | ∀ w : InfinitePlace L, ‖w.embedding (x : L)‖ ≤ C} with hS
  have hSfin : S.Finite := by
    have h0 := Embeddings.finite_of_norm_le L ℂ C
    refine (h0.preimage (Set.injOn_of_injective (f := fun x : 𝓞 L => (x : L))
      RingOfIntegers.coe_injective)).subset ?_
    intro x hx
    refine ⟨RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
    have h1 := hx (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1
  have hT : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hSfin
  have hU : {A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) |
      (A : Matrix (Fin N) (Fin N) (𝓞 L)) ∈ Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S}.Finite :=
    hT.preimage (Set.injOn_of_injective Subtype.val_injective)
  refine (hU.image (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w))).subset ?_
  rintro γ ⟨⟨A, rfl⟩, hγK⟩
  refine ⟨A, ?_, rfl⟩
  intro i _ j _ w
  have h2 := hC _ hγK
  have h3 : ‖(fun (w : InfinitePlace L) (i j : Fin N) =>
      ((((MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w)) A) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) w i j‖ ≤ C :=
    (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ w).trans h2))
  exact h3

end PositivityTheory.KB.LocalOverlapAverage

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.MeasurableSetSimplex
section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actEq (x : Gp L N) : HS L N ≃L[ℝ] HS L N where
  toLinearEquiv :=
    { toFun := actL x
      invFun := actL x⁻¹
      map_add' := (actL x).map_add
      map_smul' := (actL x).map_smul
      left_inv := fun h => by rw [← actL_mul, inv_mul_cancel, actL_one]
      right_inv := fun h => by rw [← actL_mul, mul_inv_cancel, actL_one] }
  continuous_toFun := (actL x).continuous
  continuous_invFun := (actL x⁻¹).continuous

@[simp] theorem actEq_apply (x : Gp L N) (h : HS L N) : actEq x h = actL x h := rfl

theorem pos_convex : Convex ℝ (Pos L N) := by
  intro h hh k hk a b ha hb hab w
  rw [mat_add, mat_smul, mat_smul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hk w
  · exact ((hh w).smul ha').add_posSemidef ((hk w).posSemidef.smul hb)

theorem kset_sub {q : ℕ} (x : Fin (q + 1) → Gp L N) {B : Set (HS L N)} (hB : B ⊆ Pos L N) :
    Kset (fun j => actL (x j)) B ⊆ Pos L N := by
  rintro p ⟨τ, hτ0, hτ1, y, hy, rfl⟩
  exact pos_convex.sum_mem (fun j _ => hτ0 j) hτ1 fun j _ => actL_pos (x j) (hB (hy j))

theorem isCompact_kset {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ}
    (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B) : IsCompact (Kset A B) := by
  have hc : IsCompact ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (q + 1))) (isCompact_univ_pi fun _ => hB)
  have hcont : Continuous fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j) := by fun_prop
  have e : Kset A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j)) '' ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) := by
    ext p
    constructor
    · rintro ⟨τ, hτ0, hτ1, y, hy, rfl⟩
      exact ⟨(τ, y), ⟨⟨hτ0, hτ1⟩, fun j _ => hy j⟩, rfl⟩
    · rintro ⟨⟨τ, y⟩, ⟨⟨hτ0, hτ1⟩, hy⟩, rfl⟩
      exact ⟨τ, hτ0, hτ1, y, fun j => hy j (Set.mem_univ _), rfl⟩
  rw [e]
  exact hc.image hcont

theorem simplex_pos {q : ℕ} (y : Fin (q + 1) → HS L N) (hy : ∀ j, y j ∈ Pos L N) (t : Fin q → ℝ)
    (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) : y 0 + ∑ j, t j • (y j.succ - y 0) ∈ Pos L N := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  refine pos_convex.sum_mem (fun i _ => ?_) ?_ fun i _ => hy i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simpa only [Fin.cons_succ] using ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

theorem measurableSet_simplex (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  have : {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} =
      (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t
    simp
  rw [this]
  refine (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)).measurableSet

theorem intP_inv {q : ℕ} (ω : Form (HS L N) q) (g : Gp L N) (hg : FInv ω g)
    (y : Fin (q + 1) → Pos L N) : intP ω (fun j => g • y j) = intP ω y := by
  simp only [intP, intS]
  refine setIntegral_congr_fun (measurableSet_simplex q) fun t ht => ?_
  have hv : ∀ j, ((g • y j : Pos L N) : HS L N) = actL g (y j).1 := fun j => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv, ← map_sub, ← map_smul, ← map_sum, ← map_add (f := _)]
  have hp := simplex_pos (fun j => (y j).1) (fun j => (y j).2) t ht
  have := congrArg (fun f => f (fun j => (y j.succ).1 - (y 0).1)) (hg _ hp)
  simpa [Function.comp_def, map_sub] using this

theorem cont_actL_apply (v : HS L N) : Continuous fun x : Gp L N => actL x v := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : Gp L N => fun w i j =>
    ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat v w *
      ((x w)⁻¹ : GL (Fin N) ℂ)) i j
  refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
  have hi : Continuous fun x : Gp L N => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    Units.continuous_coe_inv.comp (continuous_apply w)
  exact ((hi.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hi).matrix_elem i j

theorem cont_actL : Continuous fun x : Gp L N => actL x :=
  continuous_clm_apply.2 fun v => cont_actL_apply v

theorem cont_fr {q : ℕ} (ω : Form (HS L N) q) (hω : ContinuousOn ω (Pos L N)) :
    Continuous (fr ω) := by
  have h1 : Continuous fun x : Gp L N => ω (actL x (one L N).1) :=
    hω.comp_continuous (cont_actL_apply _) fun x => actL_pos x (one L N).2
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp cont_actL).clm_apply h1

theorem cont_ofS : Continuous (ofS L N) :=
  continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

theorem fr_mul {q : ℕ} (ω : Form (HS L N) q) (g x : Gp L N) (hg : FInv ω g) :
    fr ω (g * x) = fr ω x := by
  ext v
  have h := congrArg (fun f => f (fun i => actL x (v i))) (hg _ (actL_pos x (one L N).2))
  simpa [fr, actL_mul, Function.comp_def] using h

theorem ofS_lat {γ : Sp L N} (hγ : γ ∈ latS L N) : ∃ A : Gm L N, ofS L N γ = emb L N A := by
  obtain ⟨A, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  ext i j
  rfl

theorem ball_pos : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (one L N).1 r ⊆ Pos L N := by
  classical
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N (one L N).1 (one L N).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun k hk w => ?_⟩
  have hk' := hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hk) (half_lt_self hε))
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨mat_herm k w, fun x hx => ?_⟩
  let z : VR L N := Pi.single w x
  have hz : z ≠ 0 := fun h => hx (by simpa [z] using congrFun h w)
  have h1 := hk' z
  have h2 : qR k z = (star x ⬝ᵥ (mat k w *ᵥ x)).re := by
    simp only [qR, z]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have h3 : 0 < c * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  rw [Complex.lt_def]
  refine ⟨by simp only [Complex.zero_re]; linarith, ?_⟩
  have h4 := (mat_herm k w).im_star_dotProduct_mulVec_self x
  simp only [Complex.zero_im]
  exact h4.symm

end PositivityTheory.KB.LocalOverlapAverage

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.Overlap
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.LocalOverlapAverage

theorem overlapG_holds : OverlapG := by
  intro G _ _ _ _ _ _ Γ _ μ _ D hD hfin K hK
  have hT : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hF := hfin (K * K⁻¹) hT
  refine ⟨hF.toFinset.card, ?_⟩
  intro f hf hinv
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsum : ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    calc ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
        = ∑' γ : Γ, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) := by
          refine tsum_congr fun γ => ?_
          by_cases h : (γ : G) ∈ K * K⁻¹
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (γ : G) ∈ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from ⟨γ.2, h⟩)]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (γ : G) ∉ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from fun h' => h h'.2)]
      _ ≤ ∑' g : G, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g :=
          (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
      _ = ∑ g ∈ hF.toFinset, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
          refine tsum_eq_sum fun g hg => ?_
          rw [Set.Finite.mem_toFinset] at hg
          exact Set.indicator_of_notMem hg _
      _ ≤ ∑ _g ∈ hF.toFinset, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun g _ => ?_
          unfold Set.indicator
          split_ifs <;> simp
      _ = (hF.toFinset.card : ℝ≥0∞) := by simp
  have hcount : ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    intro x
    by_cases hS : ∃ γ₀ : Γ, γ₀ • x ∈ K
    · obtain ⟨γ₀, h₀⟩ := hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
          ≤ ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀⁻¹ : Γ) : G) := by
            refine ENNReal.tsum_le_tsum fun γ => ?_
            by_cases hγ : γ • x ∈ K
            · have hmem : ((γ * γ₀⁻¹ : Γ) : G) ∈ K * K⁻¹ := by
                refine ⟨γ • x, hγ, (γ₀ • x)⁻¹, by rw [Set.mem_inv, inv_inv]; exact h₀, ?_⟩
                simp [Subgroup.smul_def, mul_assoc]
              rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
            · rw [Set.indicator_of_notMem hγ]
              simp
        _ = ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) :=
            (Equiv.mulRight γ₀⁻¹).tsum_eq (fun γ : Γ => (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G))
        _ ≤ _ := hsum
    · push_neg at hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = ∑' _γ : Γ, (0 : ℝ≥0∞) :=
            tsum_congr fun γ => Set.indicator_of_notMem (hS γ) _
        _ ≤ _ := by simp
  have hpt : ∀ γ : Γ, ∀ x : G, K.indicator f (γ • x)
      = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x := by
    intro γ x
    by_cases hx : γ • x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      simpa [Subgroup.smul_def] using hinv γ γ.2 x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hmeas : ∀ γ : Γ, Measurable fun x : G => K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x :=
    fun γ => ((measurable_const.indicator hKm).comp (measurable_const_smul γ)).mul hf
  calc ∫⁻ x in K, f x ∂μ = ∑' γ : Γ, ∫⁻ x in D, K.indicator f (γ • x) ∂μ := by
        rw [← lintegral_indicator hKm]
        exact hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := by
        simp_rw [hpt]
    _ = ∫⁻ x in D, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) * f x ∂μ := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in D, (hF.toFinset.card : ℝ≥0∞) * f x ∂μ :=
        lintegral_mono fun x => by gcongr; exact hcount x
    _ = (hF.toFinset.card : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := lintegral_const_mul _ hf

end PositivityTheory.KB.LocalOverlapAverage

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBd
section
namespace PositivityTheory.KB.LocalOverlapAverage

theorem simpBd_holds : SimpBd := by
  intro V _ _ _ _ _ μ _ q A B hB
  exact SimpM.main μ q A B hB

end PositivityTheory.KB.LocalOverlapAverage
end

