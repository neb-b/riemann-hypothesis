module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TaylorExpansionLocalCoordinates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NmatZeroMemBor
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.LeadJets

noncomputable section

theorem mem_multiLt {n a : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a ↔ ∑ k, α k < a := by
  simp [multiLt, Finset.Nat.mem_antidiagonalTuple]

def leadVal {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) (T a0 : ℕ)
    (cc : (Fin n → ℕ) → Fin δ → ℂ) : ℂ :=
  ∑ α ∈ multiLt n a0, ∑ k, cc α k * (∏ q, s q ^ α q) * w ^ (T - ∑ q, α q) * t k

theorem leadVal_add {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) {T a0 a : ℕ}
    (ha : a < a0) (ha0 : a0 ≤ T + 1) (cc dd : (Fin n → ℕ) → Fin δ → ℂ) (hw : w ≠ 0) :
    leadVal s w t T a0 (fun α k => cc α k + if ∑ q, α q = a then dd α k else 0) =
      leadVal s w t T a0 cc + ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
        (w ^ T * ∑ k, dd α k * t k) * ∏ k, (s k / w) ^ α k := by
  classical
  have hfil : (multiLt n a0).filter (fun α => ∑ q, α q = a) =
      Finset.Nat.antidiagonalTuple n a := by
    ext α
    simp only [Finset.mem_filter, mem_multiLt, Finset.Nat.mem_antidiagonalTuple]
    omega
  unfold leadVal
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlt := mem_multiLt.1 hα
  by_cases h : ∑ q, α q = a
  · simp only [if_pos h]
    have hm : (∏ q, s q ^ α q) = (∏ k, (s k / w) ^ α k) * w ^ (∑ q, α q) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_pow, div_mul_cancel₀ _ hw]
    have hT : w ^ (∑ q, α q) * w ^ (T - ∑ q, α q) = w ^ T := by
      rw [← pow_add]; congr 1; omega
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hm]
    linear_combination (dd α k * (∏ q, (s q / w) ^ α q) * t k) * hT
  · simp [h]

theorem leadVal_diffOn {n δ : ℕ} {U : Set (V n)} {s : V n → Fin n → ℂ} {w : V n → ℂ}
    {t : V n → Fin δ → ℂ} (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U)
    (hw : DifferentiableOn ℂ w U) (ht : ∀ k, DifferentiableOn ℂ (fun z => t z k) U)
    (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) :
    DifferentiableOn ℂ (fun z => leadVal (s z) (w z) (t z) T a0 cc) U := by
  unfold leadVal
  refine DifferentiableOn.fun_sum fun α _ => DifferentiableOn.fun_sum fun k _ => ?_
  refine (((differentiableOn_const _).mul ?_).mul (hw.pow _)).mul (ht k)
  refine Finset.induction_on (motive := fun F : Finset (Fin n) =>
    DifferentiableOn ℂ (fun z => ∏ q ∈ F, s z q ^ α q) U) Finset.univ ?_ fun q F hq ih => ?_
  · simpa using differentiableOn_const (1 : ℂ)
  · simp only [Finset.prod_insert hq]
    exact ((hs q).fun_pow _).mul ih

section Step

variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}

theorem step {T a0 a : ℕ} (ha : a < a0) (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j)
    (cc : (Fin n → ℕ) → Fin δ → ℂ)
    (hcc : ∀ j, (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ cc' : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc') =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
  classical
  set ζ : Fin m → V n → V n := fun j z => (WithLp.toLp 2 fun k => s j z k / w j z : V n) with hζdef
  have loc : ∀ j, ∃ U' : Set (V n), IsOpen U' ∧ (0 : V n) ∈ U' ∧ U' ⊆ U j ∧
      (∀ v ∈ U', w j v ≠ 0) ∧ DifferentiableOn ℂ (ζ j) U' ∧ ζ j 0 = 0 := by
    intro j
    refine ⟨U j ∩ w j ⁻¹' {0}ᶜ, (hw j).continuousOn.isOpen_inter_preimage (hU j)
      isOpen_compl_singleton, ⟨h0 j, hw0 j⟩, Set.inter_subset_left, fun v hv => hv.2, ?_, ?_⟩
    · refine differentiableOn_euclidean.2 fun k => ?_
      have hdiv : DifferentiableOn ℂ (fun v => s j v k * (w j v)⁻¹) (U j ∩ w j ⁻¹' {0}ᶜ) :=
        ((hs j k).mono Set.inter_subset_left).mul
          (((hw j).mono Set.inter_subset_left).inv fun v hv => hv.2)
      exact hdiv.congr fun v _ => by simp [hζdef, div_eq_mul_inv]
    · ext k
      simp [hζdef, hs0]
  have hb : ∀ j, ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => (f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) -
        ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    intro j
    obtain ⟨U', hUo, hxU, hUt, -, hζ, hζ0⟩ := loc j
    obtain ⟨b, hb⟩ := taylor_expansion_local_coordinates (a := a)
      (fun v => f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) (ζ j) U' 0 hUo hxU
      (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 cc)).mono hUt) hζ hζ0 (hcoord j)
      (by simpa only [sub_zero] using hcc j)
    exact ⟨b, by simpa only [sub_zero] using hb⟩
  choose bb hbb using hb
  choose dd hdd using fun α => hsurj (fun j => bb j α / w j 0 ^ T)
  refine ⟨fun α k => cc α k + if ∑ q, α q = a then dd α k else 0, fun j => ?_⟩
  obtain ⟨U', hUo, hxU, hUt, hUw, hζ, hζ0⟩ := loc j
  have hxt : U j ∈ 𝓝 (0 : V n) := (hU j).mem_nhds (h0 j)
  have hζO : (fun v => ζ j v) =O[𝓝 0] fun v => v := by
    have := (hζ.differentiableAt (hUo.mem_nhds hxU)).hasFDerivAt.isBigO_sub
    simpa only [hζ0, sub_zero] using this
  have hQ : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
      (fun v => ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ a := by
    intro α hα
    have hsum := Finset.Nat.mem_antidiagonalTuple.1 hα
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)).trans (hζO.norm_norm.pow a)
    calc ‖∏ k, ζ j v k ^ α k‖
        = ∏ k, ‖ζ j v k‖ ^ α k := by simp only [norm_prod, norm_pow]
      _ ≤ ∏ k, ‖ζ j v‖ ^ α k :=
          Finset.prod_le_prod₀ (fun k _ => by positivity)
            (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ _) _)
      _ = 1 * ‖‖ζ j v‖ ^ a‖ := by
          rw [Finset.prod_pow_eq_pow_sum, hsum, one_mul, norm_pow, norm_norm]
  have hφ : ∀ α, (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k)
        =O[𝓝 0] fun v => ‖v‖ ^ 1 := by
    intro α
    have hd : DifferentiableAt ℂ (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) 0 := by
      refine (differentiableAt_const _).sub ((((hw j).differentiableAt hxt).pow T).mul ?_)
      exact DifferentiableAt.fun_sum fun k _ => ((ht j k).differentiableAt hxt).const_mul _
    have h00 : bb j α - w j 0 ^ T * ∑ k, dd α k * t j 0 k = 0 := by
      rw [hdd α j, mul_div_cancel₀ _ (pow_ne_zero _ (hw0 j)), sub_self]
    have := hd.hasFDerivAt.isBigO_sub
    rw [h00] at this
    simp only [sub_zero] at this
    exact (this.trans (isBigO_refl _ _).norm_right).congr_right fun v => (pow_one _).symm
  have h2 : (fun v => ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
      (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
      =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    have hterm : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
        (fun v => (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) :=
      fun α hα => ((hφ α).mul (hQ α hα)).congr_right fun v => by ring
    exact (IsBigO.sum hterm).congr_left fun v => Finset.sum_apply _ _ _
  refine ((hbb j).add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hUo.mem_nhds hxU] with v hv
  beta_reduce
  rw [leadVal_add _ _ _ ha ha0 cc dd (hUw v hv)]
  simp only [hζdef, PiLp.toLp_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem jets {T a0 : ℕ} (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j) :
    ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a0 := by
  have key : ∀ a ≤ a0, ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨0, fun j => ?_⟩
      have hc := (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 0)).differentiableAt
        ((hU j).mem_nhds (h0 j))).continuousAt
      exact (hc.tendsto.isBigO_one ℝ).congr_right fun v => (pow_zero _).symm
    | succ a ih =>
      intro ha
      obtain ⟨cc, hcc⟩ := ih (by omega)
      exact step (by omega) ha0 hU h0 hf hw hs ht hw0 hs0 hcoord hsurj cc hcc
  exact key a0 le_rfl

end Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mat_nmat_zero {r : ℕ} (X : Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  by_cases h1 : b < a
  · simp [mat, nmat, h1, h1.ne']
    rfl
  · simp [mat, nmat, h1, Matrix.one_apply]

theorem cpt_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show (mat x0 τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x0 τ
  rw [mat_nmat_zero, Matrix.mul_one]
  rfl

theorem rmul_nmat_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : rmul x0 (nmat X 0) = x0 :=
  cpt_zero X x0

theorem nmat_zero_mem_Bor {r : ℕ} (X : Data E r) : nmat X 0 ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨by rw [mat_nmat_zero, Matrix.det_one]; exact one_ne_zero, fun a c h => ?_⟩
  have := congrFun (congrFun (mat_nmat_zero X τ) a) c
  rw [Matrix.one_apply_ne h.ne'] at this
  exact this

theorem lact_one {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

end

end GlobalTheory.LeadJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open scoped Matrix in
private theorem gram_mul_eq_transpose_mul_gram_mul_conj {F : Type} [Field F] {r : ℕ} (τ : F →+* ℂ)
    (G : Matrix (Fin r) (Fin r) F) (A g : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (A * g) = gᵀ * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G A * g.map (starRingEnd ℂ) := by
  simp only [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
    Matrix.mul_assoc]

open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℂ} (d : Fin r → ℂ) (hdiag : ∀ a c, c ≠ a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) =
      Matrix.diagonal fun a => ((Complex.normSq (B a a) : ℝ) : ℂ) * d a := by
  have hBd : B = Matrix.diagonal fun a => B a a := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j (Ne.symm hij)]
  rw [hBd]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  congr 1
  funext a
  rw [← Complex.mul_conj]
  ring

open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_eq_diagonal_iff {r : ℕ} {B : Matrix (Fin r) (Fin r) ℂ}
    {d : Fin r → ℂ} (hd : ∀ a, d a ≠ 0) (hdet : B.det ≠ 0) (hup : ∀ a c, c < a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) = Matrix.diagonal d ↔
      ∀ a, ‖B a a‖ = 1 ∧ ∀ c, c ≠ a → B a c = 0 := by
  constructor
  · intro h
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
    have htri : B.BlockTriangular id := fun i j hij => hup i j hij
    letI := B.invertibleOfIsUnitDet hunit
    have hinv : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular htri
    have h2 : Matrix.diagonal d * B.map (starRingEnd ℂ) = (B⁻¹)ᵀ * Matrix.diagonal d := by
      have h3 : (B⁻¹)ᵀ * (Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ)) =
          (B⁻¹)ᵀ * Matrix.diagonal d := by rw [h]
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
        Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one, Matrix.one_mul] at h3
    have hoff : ∀ a c, a < c → B a c = 0 := by
      intro a c hac
      have h4 := congrFun (congrFun h2 a) c
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hinv hac, zero_mul,
        Matrix.map_apply] at h4
      have h5 := (mul_eq_zero.1 h4).resolve_left (hd a)
      simpa using h5
    have hdiag : ∀ a c, c ≠ a → B a c = 0 := by
      intro a c hca
      rcases lt_or_gt_of_ne hca with hlt | hlt
      · exact hup a c hlt
      · exact hoff a c hlt
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d hdiag] at h
    intro a
    refine ⟨?_, hdiag a⟩
    have h6 := congrFun (congrFun h a) a
    simp only [Matrix.diagonal_apply_eq] at h6
    have h7 : ((Complex.normSq (B a a) : ℝ) : ℂ) = 1 :=
      mul_right_cancel₀ (hd a) (h6.trans (one_mul _).symm)
    have h8 : ‖B a a‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast h7
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h8
  · intro h
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d fun a c hca => (h a).2 c hca]
    congr 1
    funext a
    rw [Complex.normSq_eq_norm_sq, (h a).1]
    simp


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.isOrth_rmul_iff_unitary_diagonal :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r →
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ↔ ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0)) := by
  intro r X x b hx hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  simp only [Set.mem_setOf_eq] at hb
  have hd : ∀ a : Fin r, ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hprod : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := fun τ => rfl
  constructor
  · intro h τ
    have key := h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ] at key
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).1 key
  · intro h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).2 (h τ)

end GlobalTheory
end

