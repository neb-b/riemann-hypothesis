module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
section
open GlobalTheory.WeilM Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CoverSB

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) {g : X → ℂ}
    (hg : g ∈ SB X) : W.indicator g ∈ SB X := by
  classical
  refine ⟨?_, hg.2.mono fun x hx => by
    by_contra h; exact hx (by by_cases hxW : x ∈ W <;> simp [Set.indicator, hxW, Function.notMem_support.1 h])⟩
  have h1 : IsLocallyConstant (W.indicator (fun _ => (1 : ℂ))) :=
    (IsLocallyConstant.iff_isOpen_fiber).2 fun c => by
      by_cases h0 : c = 1 <;> by_cases h0' : c = 0
      · subst h0; simp at h0'
      · subst h0
        convert hW.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · subst h0'
        convert hW.compl.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · convert (isOpen_empty : IsOpen (∅ : Set X)) using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx, Ne.symm h0, Ne.symm h0']
  have e : W.indicator g = fun x => W.indicator (fun _ => (1 : ℂ)) x * g x := by
    funext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
  rw [e]
  exact h1.mul hg.1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isClopen_subset {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {U : Set (Matrix A D k)} (hU : IsOpen U) {x : Matrix A D k} (hx : x ∈ U) :
    ∃ V : Set (Matrix A D k), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  have h0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : Matrix A D k) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hx
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset h0
  have hBo := GlobalTheory.LocMod.Inhab.isOpen_box (Y := A) (Y' := D) a
  have hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box A D a : AddSubgroup (Matrix A D k)) : Set (Matrix A D k)) :=
    AddSubgroup.isClosed_of_isOpen _ hBo
  refine ⟨(fun y => y - x) ⁻¹' (GlobalTheory.LocMod.Inhab.box A D a : Set (Matrix A D k)),
    ⟨hBc.preimage (continuous_id.sub continuous_const), hBo.preimage (continuous_id.sub continuous_const)⟩,
    by simpa using (GlobalTheory.LocMod.Inhab.box A D a).zero_mem, fun y hy => ?_⟩
  have := ha _ hy
  simpa using this

end GlobalTheory.CoverSB

namespace GlobalTheory.CoverSB

theorem mem_span_of_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  intro k _ _ _ _ A D _ _ _ _ ι _ U hU f hf hcov
  set P := Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} with hP

  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hf.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support f) := by
    have := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  let p : Set (Matrix A D k) → Prop := fun T => ∃ W, IsClopen W ∧ T ⊆ W ∧
    ∀ g ∈ SB (Matrix A D k), Function.support g ⊆ W → g ∈ P
  have hp : p (Function.support f) := by
    refine hcpt.induction_on ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun g _ hg => ?_⟩
      have : g = 0 := by
        funext y; by_contra h; exact hg h
      rw [this]; exact P.zero_mem
    · rintro s t hst ⟨W, hW, htW, h⟩
      exact ⟨W, hW, hst.trans htW, h⟩
    · rintro s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩
      refine ⟨W₁ ∪ W₂, hW₁.union hW₂, Set.union_subset_union hs ht, fun g hg hsupp => ?_⟩
      rw [← Set.indicator_self_add_compl W₁ g]
      refine P.add_mem (h₁ _ (indicator_mem_SB hW₁ hg) Set.support_indicator_subset)
        (h₂ _ (indicator_mem_SB hW₁.compl hg) fun y hy => ?_)
      have hyc : y ∈ W₁ᶜ := Set.support_indicator_subset hy
      have hyg : y ∈ Function.support g := by
        by_contra h; exact hy (by simp [Set.indicator, hyc, Function.notMem_support.1 h])
      rcases hsupp hyg with h | h
      · exact absurd h hyc
      · exact h
    · intro x hx
      obtain ⟨i, hi⟩ := hcov x hx
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isClopen_subset (hU i) hi
      refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.isOpen.mem_nhds hxV), V, hV, subset_rfl, fun g hg hsupp => ?_⟩
      exact Submodule.subset_span ⟨hg, i, fun Y hY => hVU (hsupp hY)⟩
  obtain ⟨W, -, hW, h⟩ := hp
  exact h f hf hW

end GlobalTheory.CoverSB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
section
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

def rowRenum (e : A ≃ A') : Matrix A D k ≃ₜ Matrix A' D k where
  toFun Y := Y.submatrix e.symm id
  invFun Y' := Y'.submatrix e id
  left_inv Y := by ext i j; simp
  right_inv Y' := by ext i j; simp
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

theorem comp_rowRenum_mem_SB (e : A ≃ A') {f : Matrix A' D k → ℂ} (hf : f ∈ SB (Matrix A' D k)) :
    (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k) :=
  ⟨hf.1.comp_continuous (rowRenum (k := k) (D := D) e).continuous,
    hf.2.comp_homeomorph (rowRenum (k := k) (D := D) e)⟩

def glRenum (e : A ≃ A') : GL A' k →* GL A k :=
  Units.map (Matrix.reindexAlgEquiv k k e.symm).toMonoidHom

theorem glRenum_val (e : A ≃ A') (g : GL A' k) : (glRenum e g).val = g.val.submatrix e e := rfl

theorem gdet_glRenum (e : A ≃ A') (g : GL A' k) :
    GlobalTheory.SplitFlip.gdet (glRenum e g) = GlobalTheory.SplitFlip.gdet g := by
  ext
  simp [GlobalTheory.SplitFlip.gdet, glRenum_val, Matrix.det_submatrix_equiv_self]

theorem omB_comp_rowRenum (ν : kˣ →* ℂˣ) (e : A ≃ A') (g : GL A' k) (Ψ : Matrix A' D k → ℂ) :
    (fun Y : Matrix A D k => GlobalTheory.SplitFlip.omB ν ν g 1 Ψ (Y.submatrix e.symm id)) =
      GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ (Y.submatrix e.symm id)) := by
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, gdet_glRenum, Units.val_one, Matrix.mul_one]
  congr 1
  · simp
  · congr 1
    rw [glRenum_val]
    have hY : Y = (Y.submatrix e.symm id).submatrix e id := by ext; simp
    conv_rhs => rw [hY]
    rw [show (g.val.submatrix e e)ᵀ = (g.valᵀ).submatrix e e from rfl, Matrix.submatrix_mul_equiv]
    ext; simp

theorem rowRenum_SB_Nsp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν : kˣ →* ℂˣ) (e : A ≃ A'),
    (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧
    (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν,
      (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ ν e
  refine ⟨fun f hf => comp_rowRenum_mem_SB e hf, ?_⟩
  let L : (Matrix A' D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun Y : Matrix A D k => Y.submatrix e.symm id)
  have hle : Nsp k A' D ν ≤ (Nsp k A D ν).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    show L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ') ∈ Nsp k A D ν
    rw [map_sub]
    have h1 : L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ') =
        GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ' (Y.submatrix e.symm id)) :=
      omB_comp_rowRenum ν e g Ψ'
    rw [h1]
    exact sub_mem_Nsp ν (glRenum e g) (comp_rowRenum_mem_SB e hΨ')
  intro f hf
  exact hle hf

end GlobalTheory.RankStrata
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2Bound
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ k n
  obtain hd | ⟨m, hm⟩ : finrank ℝ E = 0 ∨ ∃ m, finrank ℝ E = m + 1 := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨finrank ℝ E - 1, by omega⟩
  · exact _root_.GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero μ hd k n
  obtain ⟨C5, hC5, h5⟩ := _root_.GlobalTheory.weighted_lintegral_sobolev_pointwise μ m hm
  obtain ⟨C6, hC6, h6⟩ := _root_.GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)) μ
  refine ⟨max (n + (m + 1)) (k + finrank ℝ E + 1), (C5 * C6).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f x
  set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ := iteratedFDeriv ℝ n f with hGdef
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := (f.smooth ⊤).iteratedFDeriv_right (by
    first
    | (rw [← WithTop.coe_natCast, ← WithTop.coe_add, top_add])
    | exact le_of_eq (by simp)
    | (norm_cast))
  have hdec : ∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0) := by
    intro j _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := tendsto_zero_iff_norm_tendsto_zero.1 (_root_.GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact f (n + j))
    simpa [G, _root_.GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv] using this
  have hcont : Continuous (iteratedFDeriv ℝ (m + 1) G) :=
    hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hn : ∀ z, ‖iteratedFDeriv ℝ (m + 1) G z‖ = ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖ :=
    fun z => _root_.GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv _ _ _ z
  have e1 := h5 G hG hdec k x
  have e2 := h6 _ hcont k
  simp only [hn] at e1 e2
  set a := ∫ z, (‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  set b := ∫ z, (‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  have ha : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal a :=
    (ofReal_integral_eq_lintegral_ofReal (_root_.GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have hb : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal b :=
    (ofReal_integral_eq_lintegral_ofReal (_root_.GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have ha0 : 0 ≤ a := integral_nonneg fun z => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun z => sq_nonneg _
  rw [ha, hb, ← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at e2
  have e3 : ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C5 * C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ)) := by
    calc _ ≤ _ := e1
      _ ≤ C5 * (C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ))) := by gcongr
      _ = _ := (mul_assoc _ _ _).symm
  have e4 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC5 hC6) ENNReal.ofReal_ne_top) e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← Real.sqrt_eq_rpow] at e4
  refine e4.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ENNReal.toReal_nonneg)

  set T : ℕ → ℕ → ℝ := fun i j => ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ
  have hT : ∀ i j, 0 ≤ T i j := fun i j => integral_nonneg fun z => sq_nonneg _
  set N := max (n + (m + 1)) (k + finrank ℝ E + 1)
  have hj : n + (m + 1) ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hrow : ∀ i, T i (n + (m + 1)) ≤ ∑ j ∈ Finset.range (N + 1), T i j := fun i =>
    Finset.single_le_sum (fun j _ => hT i j) hj
  calc a + b = T k (n + (m + 1)) + T (k + finrank ℝ E + 1) (n + (m + 1)) := rfl
    _ ≤ (∑ j ∈ Finset.range (N + 1), T k j) + ∑ j ∈ Finset.range (N + 1), T (k + finrank ℝ E + 1) j :=
        add_le_add (hrow _) (hrow _)
    _ ≤ ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), T i j :=
        Finset.add_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hT i j)
          (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 (by omega)) (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
section
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

def shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k :=
  fromRows Y.toRows₁ (Y.toRows₂ + c * Y.toRows₁)

def dil (t : k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k := fromRows Y.toRows₁ (t • Y.toRows₂)

def stack (Y₁ : Matrix R D k) (C : Matrix T R k) : Matrix (R ⊕ T) D k := fromRows Y₁ (C * Y₁)

def shearGL (c : Matrix T R k) : GL (R ⊕ T) k :=
  ⟨fromBlocks 1 cᵀ 0 1, fromBlocks 1 (-cᵀ) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

def dilGL (t : kˣ) : GL (R ⊕ T) k :=
  ⟨diagonal (Sum.elim 1 fun _ => (t : k)), diagonal (Sum.elim 1 fun _ => ((t⁻¹ : kˣ) : k)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp⟩

@[simp] theorem toRows₁_shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).toRows₁ = Y.toRows₁ := by
  simp [shear]

@[simp] theorem toRows₁_dil (t : k) (Y : Matrix (R ⊕ T) D k) : (dil t Y).toRows₁ = Y.toRows₁ := by
  simp [dil]

@[simp] theorem toRows₁_stack (Y₁ : Matrix R D k) (C : Matrix T R k) : (stack Y₁ C).toRows₁ = Y₁ := by
  simp [stack]

theorem submatrix_inl_eq (Y : Matrix (R ⊕ T) D k) (τ : R → D) :
    Y.submatrix Sum.inl τ = Y.toRows₁.submatrix id τ := rfl

theorem shear_stack (c : Matrix T R k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    shear c (stack Y₁ C) = stack Y₁ (C + c) := by
  simp [shear, stack, Matrix.add_mul]

theorem dil_stack (t : k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    dil t (stack Y₁ C) = stack Y₁ (t • C) := by
  simp [dil, stack, smul_mul]

theorem shear_sub_self (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    shear c Y - Y = fromRows 0 (c * Y.toRows₁) := by
  ext (i | i) j <;> simp [shear]

theorem shearGL_transpose_mul (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    (shearGL c).valᵀ * Y = shear c Y := by
  ext (i | i) j <;> simp [shearGL, shear, fromBlocks_transpose, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.one_apply, add_comm]

theorem dilGL_transpose_mul (t : kˣ) (Y : Matrix (R ⊕ T) D k) :
    (dilGL t : GL (R ⊕ T) k).valᵀ * Y = dil (t : k) Y := by
  ext (i | i) j <;> simp [dilGL, dil, diagonal_transpose, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem gdet_shearGL (c : Matrix T R k) : gdet (shearGL c) = 1 := by
  ext; simp [shearGL, gdet, det_fromBlocks_zero₂₁]

theorem gdet_dilGL (t : kˣ) : gdet (dilGL t : GL (R ⊕ T) k) = t ^ Fintype.card T := by
  ext; simp [dilGL, gdet, det_diagonal, Fintype.prod_sum_type]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omB_shearGL (ν : kˣ →* ℂˣ) (c : Matrix T R k) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (shearGL c) 1 Ψ Y = Ψ (shear c Y) := by
  simp [omB, gdet_shearGL, shearGL_transpose_mul]

theorem exists_apow_eq (x : kˣ) (n : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((n : ℂ) / 2) = r := by
  refine ⟨GlobalTheory.SplitWeil.nabs k x ^ ((n : ℝ) / 2), Real.rpow_pos_of_pos (nabs_pos x) _, ?_⟩
  rw [apow, Complex.ofReal_cpow (nabs_pos x).le]
  push_cast; rfl

theorem omB_dilGL (ν : kˣ →* ℂˣ) (t : kˣ) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (dilGL t : GL (R ⊕ T) k) 1 Ψ Y =
      (ν t : ℂ) ^ Fintype.card T * apow (t ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) * Ψ (dil (t : k) Y) := by
  simp [omB, gdet_dilGL, dilGL_transpose_mul]

end GlobalTheory.RankChart

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem out_mk_sub_mem {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x : H) :
    (((QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H).out : H) : G) - x ∈ L := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have := L.neg_mem h
  simpa [neg_add_eq_sub] using this

theorem mk_eq_mk_iff {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← L.neg_mem_iff]
  simp [neg_add_eq_sub]


open scoped Classical in
open Classical in
theorem sum_shift_out {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by
  split_ifs with hx
  · have key : ∀ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
        F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q =
          QuotientAddGroup.mk ((⟨x, hx⟩ : H) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [e]
      exact (hL (((⟨x, hx⟩ : H) + q.out : H) : G) _ (out_mk_sub_mem H L ((⟨x, hx⟩ : H) + q.out))).symm
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H))
      (fun q => F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G))
      (fun q => F ((q.out : H) : G)) fun q => rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    have := H.sub_mem (hH _ h) (q.out : H).2
    rw [add_sub_cancel_right] at this
    exact hx this


open scoped Classical in
open Classical in
theorem sum_ite_out {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by
  split_ifs with hx
  · rw [Finset.sum_eq_single (QuotientAddGroup.mk (⟨-x, H'.neg_mem hx⟩ : H'))]
    · rw [if_pos]
      have := out_mk_sub_mem H' H (⟨-x, H'.neg_mem hx⟩ : H')
      rwa [sub_neg_eq_add, add_comm] at this
    · intro q _ hq
      rw [if_neg]
      intro hmem
      apply hq
      rw [← QuotientAddGroup.out_eq' q, mk_eq_mk_iff]
      rwa [sub_neg_eq_add, add_comm]
    · simp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hmem
    have := H'.sub_mem (hHH' hmem) (q.out : H').2
    rw [add_sub_cancel_right] at this
    exact hx this

end GlobalTheory.RankChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompat
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_parFun : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ _ χ _ _ p hp w φ
  have hc : ∀ z, c (c z) = z := hE.invol
  have hp0 : (mat c p).toBlocks₂₁ = 0 := hp
  set A := (mat c p).toBlocks₁₁ with hA
  set B := (mat c p).toBlocks₁₂ with hB
  set D := (mat c p).toBlocks₂₂ with hD
  have key : ∀ x y : Matrix α ν E, fromCols x y * mat c p = fromCols (x * A) (x * B + y * D) := by
    intro x y
    conv_lhs => rw [← fromBlocks_toBlocks (mat c p)]
    rw [fromCols_mul_fromBlocks, hp0]
    simp [hA, hB, hD]
  have spl : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp

  have h1 : ∀ x y : Matrix α ν E, form c Q (fromCols (x * A) 0) (fromCols 0 (y * D)) = form c Q (fromCols x 0) (fromCols 0 y) := by
    intro x y
    have h := form_mul c Q p (fromCols x 0) (fromCols 0 y)
    change form c Q (fromCols x 0 * mat c p) (fromCols 0 y * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x * A) (x * B), form_add_left, form_right_right, add_zero] at h
    exact h

  have h2 : ∀ x x' : Matrix α ν E, form c Q (fromCols (x' * A) 0) (fromCols 0 (x * B)) = form c Q (fromCols (x * A) 0) (fromCols 0 (x' * B)) := by
    intro x x'
    have h := form_mul c Q p (fromCols x' 0) (fromCols x 0)
    change form c Q (fromCols x' 0 * mat c p) (fromCols x 0 * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x' * A) (x' * B), spl (x * A) (x * B), form_add_left, form_add_right, form_add_right,
      form_left_left, form_left_left, form_right_right, form_swap c hc hQ (fromCols (x * A) 0) (fromCols 0 (x' * B))] at h
    linear_combination h
  have hw : w * mat c p = fromCols (w.toCols₁ * A) (w.toCols₁ * B + w.toCols₂ * D) := by
    conv_lhs => rw [← fromCols_toCols w]
    exact key _ _
  funext x
  simp only [heisFun, parFun, pr, hw, toCols₁_fromCols, toCols₂_fromCols]
  rw [← hA, ← hB]
  have key2 : ∀ (a b c d : F) (s t : ℂ), a + b = c + d → ψ a * (s * (ψ b * t)) = s * (ψ c * (ψ d * t)) := by
    intro a b c d s t h
    rw [show ψ a * (s * (ψ b * t)) = s * (ψ (a + b) * t) by rw [AddChar.map_add_eq_mul]; ring, h,
      AddChar.map_add_eq_mul]
    ring
  rw [Matrix.add_mul x w.toCols₁ A, Matrix.add_mul x w.toCols₁ B]
  simp only [e1, e2, form_add_left, form_add_right, h1]
  rw [h2 x w.toCols₁]
  apply key2
  ring

end GlobalTheory.KSp
end

