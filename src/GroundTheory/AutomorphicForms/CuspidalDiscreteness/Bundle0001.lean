module

public import Mathlib
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.MixedDifference

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.CuspidalDiscreteness.DiffBound
section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def unipBallMat (R : ℝ) : Set (ArchMatrix K n) := {A | ‖A - 1‖ ≤ R ∧ (A - 1) * (A - 1) = 0}

theorem isCompact_unipBallMat (R : ℝ) : IsCompact (unipBallMat (K := K) (n := n) R) := by
  refine (isCompact_closedBall (1 : ArchMatrix K n) R).of_isClosed_subset ?_ fun A hA => ?_
  · exact (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).inter
      (isClosed_eq ((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const))
        continuous_const)
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hA.1

theorem unipBallMat_subset_range (R : ℝ) :
    unipBallMat (K := K) (n := n) R ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  intro A hA
  refine ⟨⟨A, 2 - A, ?_, ?_⟩, rfl⟩
  · have := hA.2
    calc A * (2 - A) = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]
  · have := hA.2
    calc (2 - A) * A = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]

def unipBall (R : ℝ) : Set (ArchUnits K n) :=
  (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' unipBallMat R

theorem isCompact_unipBall (R : ℝ) : IsCompact (unipBall (K := K) (n := n) R) :=
  Units.isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_unipBallMat R)
    (unipBallMat_subset_range R)

theorem altPoint_mul_altPoint {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    (ε : Fin k → Bool) : altPoint Y ε * altPoint Y ε = 0 := by
  unfold altPoint
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs <;> simp [hY]

theorem norm_altPoint_le {k : ℕ} {Y : Fin k → ArchMatrix K n} {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R)
    (ε : Fin k → Bool) : ‖altPoint Y ε‖ ≤ k * R := by
  unfold altPoint
  calc ‖∑ i, if ε i then Y i else 0‖ ≤ ∑ i : Fin k, ‖if ε i then Y i else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, R := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hR i
        · rw [norm_zero]; exact (norm_nonneg _).trans (hR i)
    _ = k * R := by simp

theorem altPoint_neg_mul {k : ℕ} (Y : Fin k → ArchMatrix K n) (a : ArchMatrix K n)
    (ε : Fin k → Bool) : altPoint (fun i => -(Y i * a)) ε = -(altPoint Y ε * a) := by
  unfold altPoint
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem val_inv_eq_of_val_eq {C : ArchUnits K n} {W : ArchMatrix K n} (hW : W * W = 0)
    (hC : (C : ArchMatrix K n) = 1 + W) : ((C⁻¹ : ArchUnits K n) : ArchMatrix K n) = 1 - W := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hC]
  calc (1 + W) * (1 - W) = 1 - W * W := by noncomm_ring
    _ = 1 := by rw [hW, sub_zero]

section Diff

variable (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure] {β : ArchMatrix K n → ℝ}

theorem integrable_archConv_integrand (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) (C : ArchUnits K n)
    (w : normOneGL (K := K) (n := n)) :
    Integrable (fun A : ArchUnits K n =>
      (β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) * h ((archProj K n A)⁻¹ * w)) ν := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp
      (continuous_const.mul continuous_id)))).mul
      (h.continuous.comp ((continuous_archProj.inv).mul continuous_const))
  · refine HasCompactSupport.intro ((isCompact_unitsSupport hβc hβu).image
      (continuous_const_mul C⁻¹)) fun A hA => ?_
    have : ((C * A : ArchUnits K n) : ArchMatrix K n) ∉ tsupport β := fun h' =>
      hA ⟨C * A, h', by simp⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem sum_altSign_archConvFun_eq (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) {k : ℕ} {Y : Fin k → ArchMatrix K n}
    (hY : ∀ i j, Y i * Y j = 0) {C : (Fin k → Bool) → ArchUnits K n}
    (hC : ∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) (w : normOneGL (K := K) (n := n)) :
    ∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
  have hterm : ∀ ε, archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, (β ((A : ArchMatrix K n) + altPoint (fun i => -(Y i *
        (A : ArchMatrix K n))) ε) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
    intro ε
    rw [← map_inv, archConvFun_archProj_mul]
    refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]
  simp_rw [hterm, ← integral_const_mul]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [altSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  · intro ε _
    refine (Integrable.const_mul ?_ _)
    have := integrable_archConv_integrand ν hβ hβc hβu h (C ε)⁻¹ w
    refine this.congr (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]

theorem val_inv_mul_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {C : ArchUnits K n} {ε : Fin k → Bool} (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε)
    (A : ArchUnits K n) :
    ((C⁻¹ * A : ArchUnits K n) : ArchMatrix K n) =
      (A : ArchMatrix K n) + altPoint (fun i => -(Y i * (A : ArchMatrix K n))) ε := by
  rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) hC, altPoint_neg_mul,
    sub_mul, one_mul, sub_eq_add_neg]

theorem mem_unipBall_of_val_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R) {C : ArchUnits K n} {ε : Fin k → Bool}
    (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε) : C ∈ unipBall (k * R) := by
  refine ⟨?_, ?_⟩
  · rw [hC, add_sub_cancel_left]
    exact norm_altPoint_le hR ε
  · rw [hC, add_sub_cancel_left]
    exact altPoint_mul_altPoint hY ε

theorem exists_norm_sum_altSign_archConvFun_le (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ (C : (Fin k → Bool) → ArchUnits K n),
        (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : normOneGL (K := K) (n := n),
        ‖∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w)‖ ≤
          c * ∏ i, ‖Y i‖ := by
  obtain ⟨Bk, hBk⟩ := exists_norm_altSum_le hβ hβc k
  set S' := unipBall (K := K) (n := n) (k * R) *
    (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β
  have hS' : IsCompact S' := (isCompact_unipBall _).mul (isCompact_unitsSupport hβc hβu)
  obtain ⟨Rβ, hRβ⟩ := hS'.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  obtain ⟨Mh, hMh⟩ := h.continuous.bounded_above_of_compact_support h.hasCompactSupport
  set Bk' := max Bk 0
  set Rβ' := max Rβ 0
  set Mh' := max Mh 0
  refine ⟨Bk' * Rβ' ^ k * Mh' * ν.real S', fun Y hY hR C hC w => ?_⟩
  rw [sum_altSign_archConvFun_eq ν hβ.continuous hβc hβu h hY hC w]
  have hpt : ∀ A : ArchUnits K n, ‖((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
      (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w)‖ ≤
      S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A := by
    intro A
    by_cases hA : A ∈ S'
    · rw [indicator_of_mem hA, norm_mul, Complex.norm_real]
      refine mul_le_mul ?_ ((hMh _).trans (le_max_left _ _)) (norm_nonneg _) ?_
      · refine (hBk _ _).trans ?_
        have hA' : ‖(A : ArchMatrix K n)‖ ≤ Rβ' := (hRβ A hA).trans (le_max_left _ _)
        have hprod : ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ ≤ (∏ i, ‖Y i‖) * Rβ' ^ k := by
          rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_neg]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
        calc Bk * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖
            ≤ Bk' * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ Bk' * ((∏ i, ‖Y i‖) * Rβ' ^ k) :=
              mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
          _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k := by ring
      · exact mul_nonneg (mul_nonneg (le_max_right _ _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)) (pow_nonneg (le_max_right _ _) _)
    · rw [indicator_of_notMem hA]
      have hzero : altSum k β (fun i => -(Y i * (A : ArchMatrix K n))) (A : ArchMatrix K n) = 0 := by
        rw [altSum_eq_sum]
        refine Finset.sum_eq_zero fun ε _ => ?_
        rw [← val_inv_mul_eq hY (hC ε) A]
        by_cases hs : (((C ε)⁻¹ * A : ArchUnits K n) : ArchMatrix K n) ∈ tsupport β
        · exact absurd ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), _, hs, mul_inv_cancel_left _ _⟩ hA
        · rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]
      rw [hzero, Complex.ofReal_zero, zero_mul, norm_zero]
  calc ‖∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν‖
      ≤ ∫ A, S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A ∂ν :=
        norm_integral_le_of_norm_le ((integrableOn_const hS'.measure_lt_top.ne).integrable_indicator
          hS'.measurableSet) (Eventually.of_forall hpt)
    _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh' * ν.real S' := by
        rw [integral_indicator hS'.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ = Bk' * Rβ' ^ k * Mh' * ν.real S' * ∏ i, ‖Y i‖ := by ring

end Diff

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite
section
open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}


variable (K) in
theorem exists_natCast_mul_mem_of_mem_nhds {W : Set (FiniteAdeleRing (𝓞 K) K)}
    (hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      (M : FiniteAdeleRing (𝓞 K) K) * a ∈ W := by
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 K) K
  have hO : IsCompact (O : Set (FiniteAdeleRing (𝓞 K) K)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles K
  set N := {c : FiniteAdeleRing (𝓞 K) K | ∀ a ∈ (O : Set (FiniteAdeleRing (𝓞 K) K)), c * a ∈ W}
  have hN : N ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have h := (continuous_mul (M := FiniteAdeleRing (𝓞 K) K)).tendsto ((0 : FiniteAdeleRing (𝓞 K) K), a)
    rw [zero_mul] at h
    exact h hW
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hN
  set V' := V ∩ (fun v => -v) ⁻¹' V
  have hV' : V' ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := by
    refine inter_mem hV ?_
    have := (continuous_neg (G := FiniteAdeleRing (𝓞 K) K)).tendsto 0
    rw [neg_zero] at this
    exact this hV
  have hsub : ∀ v ∈ V', ∀ w ∈ V', v - w ∈ N := fun v hv w hw => by
    rw [sub_eq_add_neg]
    exact hVV v hv.1 (-w) hw.2
  obtain ⟨t, -, hcover⟩ := hO.elim_nhds_subcover (fun c => {y | y - c ∈ V'}) fun c _ => by
    have := (continuous_sub_right c).tendsto c
    rw [sub_self] at this
    exact this hV'
  have hmem : ∀ j : ℕ, ∃ c : t, (j : FiniteAdeleRing (𝓞 K) K) - c ∈ V' := by
    intro j
    have hj : (j : FiniteAdeleRing (𝓞 K) K) ∈ (O : Set (FiniteAdeleRing (𝓞 K) K)) :=
      natCast_mem O j
    obtain ⟨c, hc, hjc⟩ := mem_iUnion₂.1 (hcover hj)
    exact ⟨⟨c, hc⟩, hjc⟩
  choose f hf using hmem
  obtain ⟨j, j', hne, hjj⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (t.card + 1) => f i) (by simp)
  have key : ∀ i i' : Fin (t.card + 1), f i = f i' →
      ((i : ℕ) : FiniteAdeleRing (𝓞 K) K) - (i' : ℕ) ∈ N := by
    intro i i' h
    have h1 := hf i
    have h2 := hf i'
    rw [h] at h1
    have := hsub _ h1 _ h2
    rwa [sub_sub_sub_cancel_right] at this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(j' : ℕ) - j, Nat.sub_pos_of_lt hlt, fun a ha => ?_⟩
    rw [Nat.cast_sub hlt.le]
    exact key j' j hjj.symm a ha
  · refine ⟨(j : ℕ) - j', Nat.sub_pos_of_lt hlt, fun a ha => ?_⟩
    rw [Nat.cast_sub hlt.le]
    exact key j j' hjj a ha

theorem continuous_unipMatrix' {r : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    Continuous (unipMatrix : (UPos n r → R) → Matrix (Fin n) (Fin n) R) := by
  refine continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unipGL' {r : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (unipGL : (UPos n r → R) → GL (Fin n) R) :=
  Units.continuous_iff.2 ⟨continuous_unipMatrix', continuous_unipMatrix'.comp continuous_neg⟩

theorem adele_add_fst (p q : 𝔸[K]) : (p + q).1 = p.1 + q.1 := rfl

theorem adele_add_snd (p q : 𝔸[K]) : (p + q).2 = p.2 + q.2 := rfl

theorem adele_one_fst : (1 : 𝔸[K]).1 = 1 := rfl

theorem adele_one_snd : (1 : 𝔸[K]).2 = 1 := rfl

theorem adele_zero_fst : (0 : 𝔸[K]).1 = 0 := rfl

theorem adele_zero_snd : (0 : 𝔸[K]).2 = 0 := rfl

theorem prodEquiv_unipGL_fst {r : ℕ} (z : UPos n r → 𝔸[K]) (hz : ∀ p, (z p).1 = 0) :
    (AdelicGLn.prodEquiv K n (unipGL z)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_fst, coe_unipGL, Units.val_one]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rw [adele_add_fst]
  split_ifs with h1 h2 h2
  · rw [hz, adele_one_fst, add_zero]
  · rw [adele_one_fst, adele_zero_fst, add_zero]
  · rw [hz, adele_zero_fst, add_zero]
  · rw [adele_zero_fst, add_zero]

theorem prodEquiv_unipGL_snd {r : ℕ} (z : UPos n r → 𝔸[K]) :
    (AdelicGLn.prodEquiv K n (unipGL z)).2 = unipGL fun p => (z p).2 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_unipGL, coe_unipGL]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rw [adele_add_snd]
  split_ifs with h1 h2 h2
  · rw [adele_one_snd]
  · rw [adele_one_snd, adele_zero_snd]
  · rw [adele_zero_snd]
  · rw [adele_zero_snd]

theorem exists_natCast_conj_unipGL_mem (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) {ω : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := K) (n := n)), ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
        (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
          (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
        ∃ u : U, ((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k)⁻¹ :
            AdelicGLn.AdelicGL K n) * unipGL z * (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k) =
          finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := by
  classical

  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))
  have hU' : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U' := ⟨1, U.one_mem, rfl⟩

  set Cf : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n (p.1 * p.2)).2) ''
      (ω ×ˢ (GroundTheory.Automorphic.Reduction.maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)))
  have hCf : IsCompact Cf := (hω.prod isCompact_maxCompact).image
    (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp (continuous_fst.mul continuous_snd)))

  have hcont : Continuous fun q : (UPos n r → FiniteAdeleRing (𝓞 K) K) × AdelicGLn.FiniteAdelicGL K n =>
      q.2⁻¹ * unipGL q.1 * q.2 :=
    (continuous_snd.inv.mul (continuous_unipGL'.comp continuous_fst)).mul continuous_snd
  have hev : ∀ᶠ w in 𝓝 (0 : UPos n r → FiniteAdeleRing (𝓞 K) K), ∀ c ∈ Cf,
      c⁻¹ * unipGL w * c ∈ U' := by
    refine hCf.eventually_forall_of_forall_eventually fun c _ => ?_
    refine (hcont.tendsto ((0 : UPos n r → FiniteAdeleRing (𝓞 K) K), c)).eventually
      (hU'.mem_nhds ?_)
    simp only [unipGL_zero, mul_one, inv_mul_cancel]
    exact h1U'
  rw [nhds_pi] at hev
  have hev' : {w : UPos n r → FiniteAdeleRing (𝓞 K) K | ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'} ∈
      Filter.pi fun _ => 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := hev
  rw [Filter.mem_pi] at hev'
  obtain ⟨I, -, tt, htt, hIt⟩ := hev'
  obtain ⟨M, hM, hMW⟩ := exists_natCast_mul_mem_of_mem_nhds K (Filter.iInter_mem.2 htt)
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  set w : UPos n r → FiniteAdeleRing (𝓞 K) K := fun p => (z p).2
  have hw : w ∈ I.pi tt := fun p _ => by
    obtain ⟨a, ha, hza⟩ := hz2 p
    have := hMW a ha
    rw [mem_iInter] at this
    change (z p).2 ∈ tt p
    rw [hza]
    exact this p
  set c := (AdelicGLn.prodEquiv K n (b * k)).2
  have hc : c ∈ Cf := ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  obtain ⟨u, huU, hu⟩ := hIt hw c hc
  refine ⟨⟨u, huU⟩, ?_⟩
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv,
      prodEquiv_unipGL_fst z hz1, mul_one, inv_mul_cancel]
  · change _ = (u : AdelicGLn.FiniteAdelicGL K n)
    rw [hu, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv,
      prodEquiv_unipGL_snd]
    simp only [c, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd ρ hρ, mul_one]
    rfl

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

