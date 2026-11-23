module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrameStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_pos_le_latticeHeight_at_frame : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  first | exact @GlobalTheory.HeightLower.exists_pos_le_height | exact GlobalTheory.HeightLower.exists_pos_le_height | (intros; apply GlobalTheory.HeightLower.exists_pos_le_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTopStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_pos_le_latticeHeight_bot_top : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  first | exact @GlobalTheory.HeightEnds.exists_pos_le_bot_top | exact GlobalTheory.HeightEnds.exists_pos_le_bot_top | (intros; apply GlobalTheory.HeightEnds.exists_pos_le_bot_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSubspaceHeightGramDeterminant
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SubspaceHeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_gram_reindex {r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (A : Matrix (Fin r) (Fin r) ℂ) (f : ι → Fin r → ℂ) :
    ((A * (Matrix.of fun k a => f (e a) k))ᴴ * (A * (Matrix.of fun k a => f (e a) k))).det =
      ((A * (Matrix.of fun k a => f a k))ᴴ * (A * (Matrix.of fun k a => f a k))).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_height : (∀ (r : ℕ) (X : Data E r), ∃ d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ, (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X
  choose b hb hΛ hsp using GlobalTheory.LatBasis.exists_basis_mem r X
  refine ⟨fun x W => ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (b W))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (b W))).toAddSubgroup)) : ℝ)), ?_⟩
  intro x _ ι _ _ w hw hwΛ
  have hc : Module.finrank E (Submodule.span E (Set.range w)) = Fintype.card ι :=
    finrank_span_eq_card hw
  let e : Fin (Module.finrank E (Submodule.span E (Set.range w))) ≃ ι :=
    (Fintype.equivFinOfCardEq hc.symm).symm
  have hr : Set.range (fun a => w (e a)) = Set.range w := e.surjective.range_comp w
  have key := GlobalTheory.T.gramDet_div_index_eq_of_span_eq r X x _ (b (Submodule.span E (Set.range w))) (fun a => w (e a))
    (hb _) (hΛ _) (hw.comp e e.injective) (fun a => hwΛ _) (by rw [hr, hsp])
  refine key.trans ?_
  rw [hr]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact congrArg Complex.re (det_gram_reindex e _ (fun a k => τ.1 (w a k)))

end GlobalTheory.SubspaceHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeightsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.firstMinimum_lower_of_lineHeights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  first | exact @GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | exact GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | (intros; apply GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightSupInvariantUnderHermitianLatticeAut
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem height_sup_lact_invariant : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hmap⟩ := HeightInv.height_lact r X d hd γ hγ x hx
  have hinj : ∀ g : GL (Fin r) E,
      Function.Injective (g : Matrix (Fin r) (Fin r) E).mulVecLin := by
    intro g v w hvw
    have h := congrArg (fun u => ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) hvw
    simpa [Matrix.mulVec_mulVec] using h
  have hrank : ∀ (g : GL (Fin r) E) (W : Submodule E (Fin r → E)),
      Module.finrank E (W.map (g : Matrix (Fin r) (Fin r) E).mulVecLin) = Module.finrank E W :=
    fun g W => (Submodule.equivMapOfInjective _ (hinj g) W).finrank_eq.symm
  have hset : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} := by
    ext y
    constructor
    · rintro ⟨W', hW', rfl⟩
      refine ⟨W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW' ⊢
        rw [hrank, hW']
      · have hback : (W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin).map
            (γ : Matrix (Fin r) (Fin r) E).mulVecLin = W' := by
          rw [← Submodule.map_comp, ← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
        simp only
        rw [← hmap, hback]
    · rintro ⟨W, hW, rfl⟩
      refine ⟨W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW ⊢
        rw [hrank, hW]
      · simp only
        rw [hmap]
  have h1 := hα i hi (lact γ x) hx'
  rw [hset] at h1
  exact h1.unique (hα i hi x hx)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightContinuousOnFramesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.latticeHeight_continuousOn_frames : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  first | exact @GlobalTheory.HeightCont.height_continuousOn | exact GlobalTheory.HeightCont.height_continuousOn | (intros; apply GlobalTheory.HeightCont.height_continuousOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightUpdateFrameComponentStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.latticeHeight_update_frameComponent : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  first | exact @GlobalTheory.HeightStep.height_update | exact GlobalTheory.HeightStep.height_update | (intros; apply GlobalTheory.HeightStep.height_update <;> assumption)
end

