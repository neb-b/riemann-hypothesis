module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodula
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TestFunctionLocallyInvariant
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.RowSmooth

theorem row_smooth : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  intro R _ _ _ T hT
  classical
  obtain ⟨V, hV, hVT⟩ := GlobalTheory.TestFn.unif_const (R × R) T hT
  have hC : IsCompact (tsupport T) := hT.2
  let φ : (R × R × R × R) → R × R → R × R := fun e v =>
    (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)
  have hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2) := by
    simp only [φ]; fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V := by
    refine hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_
    intro v _
    have h0 : φ 0 v = 0 := by simp [φ]
    have : V ∈ 𝓝 (φ (0 : R × R × R × R) v) := by rw [h0]; exact hV
    exact hφ.continuousAt (x := ((0 : R × R × R × R), v)) this
  obtain ⟨A₁, hA₁, S₁, hS₁, hsub₁⟩ := mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)
  obtain ⟨A₂, hA₂, S₂, hS₂, hsub₂⟩ := mem_nhds_prod_iff.mp hS₁
  obtain ⟨A₃, hA₃, A₄, hA₄, hsub₃⟩ := mem_nhds_prod_iff.mp hS₂
  set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def
  have hU₀ : U₀ ∈ 𝓝 (0 : R) := inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄
  have key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T,
      T (v + φ (a, b, c, d) v) = T v := by
    intro a b c d ha hb hc hd v hv
    have hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V} :=
      hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩
    exact hVT v _ (hmem v hv)
  refine ⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀
    (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩
  intro k hk c u
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 := hk 0 0
  have e01 := hk 0 1
  have e10 := hk 1 0
  have e11 := hk 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11
  by_cases hv : (c, u) ∈ tsupport T
  · have := key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext <;> simp <;> ring
  by_cases hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T
  · have := key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext
    · simp; linear_combination c * hdet
    · simp; linear_combination u * hdet
  · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

end GlobalTheory.RowSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionI
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mulVec_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

theorem norm_vecMul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (v : Fin n → F) (A : Matrix (Fin n) (Fin n) F) (hv : ∀ i, ‖v i‖ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (j : Fin n) : ‖(v ᵥ* A) j‖ ≤ 1 := by
  rw [Matrix.vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hv k) (norm_nonneg _) (hA k j)

def IsIntegral {F : Type} [NormedField F] {n : ℕ} (Y : Gl n F) : Prop :=
  (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1

theorem isIntegral_act {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ glO n F) {Y : Gl n F} (hY : IsIntegral Y) : IsIntegral (act k Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hY
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩
  · exact norm_mul_apply_le_one _ _
      (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j
  · exact norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i
  · exact norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i

theorem act_inv_act {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A *
        ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b
    rw [Units.inv_mul, Matrix.one_mulVec]
  · show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c
    rw [Units.inv_mul, Matrix.vecMul_one]

theorem unitG_act : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F),
    k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  intro F _ _ n k hk Y
  have hk' : k⁻¹ ∈ glO n F := (glOSub n F).inv_mem hk
  have key : IsIntegral (act k Y) ↔ IsIntegral Y :=
    ⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩
  have e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z := fun _ => rfl
  rw [e, e]
  by_cases h : IsIntegral Y
  · rw [Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h),
      Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')),
      Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]

end GlobalTheory.JR.GLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitGLift

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_apply_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_cl (Y : Gl r k) (a : Fin r) : full Y (Fin.castSucc a) (Fin.last r) = Y.2.1 a := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end GlobalTheory.JR.UnitGLift

namespace GlobalTheory.JR.UnitGLift

theorem norm_full_le_one_iff {F : Type} [NormedField F] {r : ℕ} (Z : Gl r F) :
    (∀ i j, ‖full Z i j‖ ≤ 1) ↔
      ((∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full_apply_cc] using h (Fin.castSucc i) (Fin.castSucc j)
    · simpa [full_apply_cl] using h (Fin.castSucc i) (Fin.last r)
    · simpa [full_apply_lc] using h (Fin.last r) (Fin.castSucc j)
    · simpa [full_apply_ll] using h (Fin.last r) (Fin.last r)
  · rintro ⟨h1, h2, h3, h4⟩ i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_ll] using h4
      | cast j => simpa [full_apply_lc] using h3 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_cl] using h2 i
      | cast j => simpa [full_apply_cc] using h1 i j

theorem norm_eL_le_one {F : Type} [NormedField F] {r : ℕ} (i : Fin (r + 1)) :
    ‖GlobalTheory.JR.Step.eL r F i‖ ≤ 1 := by
  unfold GlobalTheory.JR.Step.eL
  by_cases h : i = Fin.last r
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem unitG_lift : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 →
    unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  intro F _ r Z μ l hμ
  have hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)
  have hmem : GlobalTheory.JR.Step.lift Z μ l ∈
      {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔
      (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
        ∧ ‖l‖ ≤ 1) := by
    simp only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]
    rw [norm_full_le_one_iff]
    exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩
  unfold unitG
  by_cases hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
  · by_cases hl : ‖l‖ ≤ 1
    · rw [Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]
      simp
    · rw [Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]

end GlobalTheory.JR.UnitGLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ ch : Matrix.unitaryGroup (Fin r) E →* ℝ, Continuous ch → (∀ g, 0 < ch g) → ∀ g, ch g = 1) ∧ ∀ M : Meas r F E, (letI := M.mU; M.μU.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | exact GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | (intros; apply GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedInvolutionExtMapsIntegersToIntegersStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ x : K.O, ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  first | exact @GlobalTheory.UnitLemma.Unr.map_int | exact GlobalTheory.UnitLemma.Unr.map_int | (intros; apply GlobalTheory.UnitLemma.Unr.map_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNorm
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.EtaChar

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨π, hπm, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩ continuous_norm.continuousOn
  have hπ1 : ‖π‖ < 1 := by simpa using hπm
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x0, hx0, hx01⟩ := NormedField.exists_norm_lt_one F
  have hπ0 : 0 < ‖π‖ := lt_of_lt_of_le hx0 (hle x0 hx01)
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  set q := ‖π‖ with hq
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hqi : 1 < q⁻¹ := one_lt_inv₀ hπ0 |>.2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxp hqi
  have hqn : 0 < q ^ (n + 1) := zpow_pos hπ0 _
  have hz : ‖x * π ^ (n + 1)‖ = ‖x‖ * q ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hup : ‖x‖ * q ^ (n + 1) ≤ 1 := by
    calc ‖x‖ * q ^ (n + 1) ≤ q⁻¹ ^ (n + 1) * q ^ (n + 1) := mul_le_mul_of_nonneg_right hn2 hqn.le
      _ = 1 := by rw [_root_.inv_zpow, inv_mul_cancel₀ hqn.ne']
  have hlo : q < ‖x‖ * q ^ (n + 1) := by
    calc q = q⁻¹ ^ n * q ^ (n + 1) := by
            rw [_root_.inv_zpow, zpow_add_one₀ hπ0.ne', ← mul_assoc, inv_mul_cancel₀ (zpow_pos hπ0 n).ne', one_mul]
      _ < ‖x‖ * q ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hqn
  have heq : ‖x‖ * q ^ (n + 1) = 1 := by
    by_contra hne
    have := hle (x * π ^ (n + 1)) (by rw [hz]; exact lt_of_le_of_ne hup hne)
    rw [hz] at this
    linarith
  refine ⟨-(n + 1), ?_⟩
  rw [_root_.zpow_neg]; exact eq_inv_of_mul_eq_one_left heq

theorem eta_eq_one_iff {F : Type} [NormedField F] (x : F) : eta x = 1 ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    norm_num

theorem eta_eq_neg_one_iff {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    norm_num
  · simp [h]

theorem sq_iff_even {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ Even k := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ‖x‖ = 0 := by simpa using hy
      rw [hk] at this
      exact (zpow_pos h0 k).ne' this
    obtain ⟨j, hj⟩ := hall y hy0
    rw [hk, hj, ← zpow_natCast, ← _root_.zpow_mul] at hy
    have := zpow_right_injective₀ h0 h1.ne hy
    exact ⟨j, by rw [this]; push_cast; ring⟩
  · rintro ⟨j, rfl⟩
    refine ⟨π ^ j, ?_⟩
    rw [hk, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring

theorem eta_of_exp {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    eta x = if Even k then 1 else -1 := by
  have := sq_iff_even h0 h1 hall hk
  by_cases h : Even k
  · rw [(eta_eq_one_iff x).2 (this.2 h)]; simp [h]
  · rw [(eta_eq_neg_one_iff x).2 (fun h' => h (this.1 h'))]; simp [h]

theorem eta_mul (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) : eta (x * y) = eta x * eta y := by
  obtain ⟨π, h0, h1, hall⟩ := exists_unif F
  obtain ⟨k, hk⟩ := hall x hx
  obtain ⟨l, hl⟩ := hall y hy
  have hkl : ‖x * y‖ = ‖π‖ ^ (k + l) := by rw [norm_mul, hk, hl, zpow_add₀ h0.ne']
  rw [eta_of_exp h0 h1 hall hk, eta_of_exp h0 h1 hall hl, eta_of_exp h0 h1 hall hkl]
  by_cases ek : Even k <;> by_cases el : Even l <;> simp [ek, el, Int.even_add]

theorem eta_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have e : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  by_cases hh : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [(eta_eq_one_iff x).2 hh, (eta_eq_one_iff y).2 (e.1 hh)]
  · rw [(eta_eq_neg_one_iff x).2 hh, (eta_eq_neg_one_iff y).2 (fun h' => hh (e.2 h'))]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  refine ⟨fun x y hx hy => eta_mul F x y hx hy, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (eta_eq_one_iff x).2 ⟨1, by rw [hx, norm_one, one_pow]⟩
  · rw [eta_eq_one_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hx (norm_eq_zero.1 (by simpa using hy))
      obtain ⟨v, hv⟩ := _root_.GlobalTheory.NormUnits.norm_onto_units F E (x / y ^ 2) (by rw [norm_div, norm_pow, hy, div_self (by positivity)])
      refine ⟨v * algebraMap F E y, ?_⟩
      rw [star_mul', hU.star_fix y]
      calc v * algebraMap F E y * (star v * algebraMap F E y)
          = (v * star v) * algebraMap F E (y ^ 2) := by rw [map_pow]; ring
        _ = algebraMap F E x := by rw [hv, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := hU.unram v
      refine ⟨z, ?_⟩
      have := congrArg norm hv
      rw [norm_algebraMap', norm_mul, hU.norm_star, hz] at this
      rw [← this, sq]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
    have hmem : {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} ∈ 𝓝 x := by
      have : IsOpen {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
      exact this.mem_nhds (by simpa using hx)
    filter_upwards [hmem] with y hy
    apply eta_of_norm_eq
    have h2 : y.1 = x.1 + (y.1 - x.1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy), max_eq_left hy.le]

end GlobalTheory.EtaChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingleton
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dite_eq_left s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
end
end

