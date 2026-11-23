module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartA
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem frQ_mul_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c w * (incM F c.1)ᵀ = w := by
  change (w * (incM F (c⁻¹).1)ᵀ) * (incM F c.1)ᵀ = w
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_of {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c (Q * (incM F c.1)ᵀ) = Q := by
  change (Q * (incM F c.1)ᵀ) * (incM F (c⁻¹).1)ᵀ = Q
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_injective {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) {w w' : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)}
    (e : frQ c w = frQ c w') : w = w' := by
  rw [← frQ_mul_frame c w, ← frQ_mul_frame c w', e]

theorem split_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    Q * (incM F c.1)ᵀ = Q.toCols₁ * (incM F c.1.toCols₁)ᵀ + Q.toCols₂ * (incM F c.1.toCols₂)ᵀ := by
  have e1 : incM F c.1 = Matrix.fromCols (incM F c.1.toCols₁) (incM F c.1.toCols₂) := by
    ext i j
    rcases j with j | j <;> rfl
  conv_lhs => rw [← Matrix.fromCols_toCols Q, e1, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

theorem adapted_e {m k : ℕ} {bs : Module.Basis (Fin 2) F E} {A : Spc F E m} {Y : Spc F E k} {c : GL (Fin k ⊕ Fin k) E}
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin k × Fin 2)}
    (hd : IsAdapted bs A Y c dd) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    dd.e w = (crdB bs (frQ c w).toCols₂, fun k => Bf σ A.J (frQ c w).toCols₁ (Ek bs k)) := by
  conv_lhs => rw [← frQ_mul_frame c w, split_frame]
  exact hd _ _

def embQ {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R) :
    Matrix (Fin m) (Fin N ⊕ Fin N) R :=
  (Matrix.fromCols Q (0 : Matrix (Fin m) (Fin 1 ⊕ Fin 1) R)).submatrix id (eB h)

theorem embQ_toCols₁ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₁ = ext0 h Q.toCols₁ := by
  ext a i
  rcases idx_cases h (Sum.inl i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp only [Sum.map_inl, Sum.inl.injEq] at hu
      subst hu
      simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inl (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inl u) from rfl, eB_map]
      simp [ext0, em0]
    · simp at hu
  · simp only [Sum.inl.injEq] at hu
    subst hu
    simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inl_last]
    simp [ext0, i0]
  · simp at hu

theorem embQ_toCols₂ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₂ = ext0 h Q.toCols₂ := by
  ext a i
  rcases idx_cases h (Sum.inr i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp at hu
    · simp only [Sum.map_inr, Sum.inr.injEq] at hu
      subst hu
      simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inr (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inr u) from rfl, eB_map]
      simp [ext0, em0]
  · simp at hu
  · simp only [Sum.inr.injEq] at hu
    subst hu
    simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inr_last]
    simp [ext0, i0]

theorem emb_eq {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : emb h b bd w = embQ h (frQ b w) * (incM F bd.1)ᵀ := by
  rw [split_frame, embQ_toCols₁, embQ_toCols₂, emb]
  rfl

theorem frQ_emb {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : frQ bd (emb h b bd w) = embQ h (frQ b w) := by
  rw [emb_eq, frQ_of]

theorem embQ_mul_blk {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : embQ h Q * (blk h M 1)ᵀ = embQ h (Q * Mᵀ) := by
  rw [blk_transpose]
  simp only [embQ, blk]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem frQ_mul_mat {m k : ℕ} {Y : Spc F E k} (c : GL (Fin k ⊕ Fin k) E) (x : G2 σ Y)
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (w * (x.1.1)ᵀ) = frQ c w * (inFrame c x)ᵀ := by
  have e : x.1.1 = incM F c.1 * inFrame c x * incM F (c⁻¹).1 := by
    rw [inFrame_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      incM_mul_inv, Matrix.mul_one]
  rw [frQ, frQ, e]
  simp only [Matrix.transpose_mul, ← Matrix.mul_assoc]
  change w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ * (incM F c.1)ᵀ * (incM F (c⁻¹).1)ᵀ =
    w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ
  rw [Matrix.mul_assoc _ (incM F c.1)ᵀ, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def SiegelSmall : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (om1 : d.G →* Module.End ℂ ((K1 d.m n → AF F) → ℂ)),
    IsSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) om1 →
    SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) d.B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))
      (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) d.χ (diagCols (Fin d.n)) om1 →
  ∀ φ₀ ∈ schA F (Fin d.m × Fin 2), φ₀ 0 = 1 →
  ∀ (om' : G2 σ Y →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ)),
    (∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀) →
    SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) d.B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J)) dd' d.χ (diagCols (Fin n)) om'

def SmallS : Prop := TAll → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (S1 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((K1 d.m n → AF F) → ℂ)) (S1' : ((K1 d.m n → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (C : ℂ), C ≠ 0 →
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (d.dd.e.symm w)) S1 S1' →
    (∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h)) →
  ∃ S' : UA σ d.A.J →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ),
    IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' ∧
    ∀ g, ∀ Φ ∈ schA F (Fin d.m × Fin n × Fin 2), ev0 _ (S' g Φ) = ev0 _ Φ

end PositivityTheory.SiegelWeilFormula.Ald

end
end

