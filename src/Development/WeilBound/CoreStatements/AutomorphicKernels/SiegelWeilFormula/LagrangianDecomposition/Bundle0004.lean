module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameA
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SigSig
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig' (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])


variable (F) in
def spcOf {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Spc F E n := ⟨J, ⊤, fun _ => 1, fun _ => 1⟩

theorem toCols₁_wit {n : ℕ} (T : GL (Fin n) E) (a : E) :
    ∃ t : GL (Fin n) E, (GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit a T).1.toCols₁ = diagCols (Fin n) * t.1 := by
  have hd := GlobalTheory.ThK.Dbl.Frame.frame_diag (1 : GL (Fin n) E) T a
  refine ⟨1, ?_⟩
  ext i j
  have := congrFun (congrFun hd i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at this
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  simpa [Matrix.toCols₁] using this

omit [NumberField F] [NumberField E] in
theorem dbl_sym {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (hJ : ∀ i j, σ (J j i) = e₀ * J i j) :
    ((dbl J).map (σ : E →+* E))ᵀ = e₀ • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]

theorem eps_eq {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E}
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {e : E}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (e • 1) 0) (he : σ e = e) : e = e₀ := by
  have h := GlobalTheory.ThK.Dbl.Frame.gram_sym (σ : E →+* E) hc (dbl_sym hJ) b
  have hb' : bᵀ * dbl J * b.map (σ : E →+* E) = Matrix.fromBlocks 0 1 (e • 1) 0 := hb
  rw [hb'] at h
  have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simpa [Matrix.fromBlocks, he] using this

end PositivityTheory.SiegelWeilFormula.Ald.YFA

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def OpBox : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F)
    (dd : Darboux B (κ' ⊕ κ'')) (G : Type) [Group G] (act : G → W → W)
    (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    (∀ u v : κ'' → AF F, ∃ w, dd.e w = (Sum.elim (0 : κ' → AF F) u, Sum.elim (0 : κ' → AF F) v)) →
    ∀ x : G, (∀ w, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 → act x w = w) →
    ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
      (∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' (om x Ψ) = slice0 κ' κ'' (om x (boxFun (slice0 κ' κ'' Ψ) φ₀))) ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'',
        om x (boxFun φ' φ'') = boxFun (slice0 κ' κ'' (om x (boxFun φ' φ₀))) φ''

def SubSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W W' : Type) [AddCommGroup W] [Module (AF F) W] [AddCommGroup W']
    [Module (AF F) W'] (B : W → W → AF F) (B' : W' → W' → AF F) (dd : Darboux B (κ' ⊕ κ'')) (dd' : Darboux B' κ')
    (emb : W' → W), (∀ w', dd.e (emb w') = (Sum.elim (dd'.e w').1 0, Sum.elim (dd'.e w').2 0)) →
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (act : G → W → W)
    (act' : G' → W' → W') (j : G' →* G), Continuous j → (∀ g w', act (j g) (emb w') = emb (act' g w')) →
  ∀ (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)) (om' : G' →* Module.End ℂ ((κ' → AF F) → ℂ)),
    IsUSplitting (adeleClass F) ψ dd act om →
  ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
    (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
      ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤) →
    (∀ g, ∃ φ₁ ∈ schA F κ'', φ₁ 0 = 1 ∧
      (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
        ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ'' = ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'') ∧
      ∀ φ' ∈ schA F κ', om (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₁) →
    IsUSplitting (adeleClass F) ψ dd' act' om'

end PositivityTheory.SiegelWeilFormula.Ald

end
end

