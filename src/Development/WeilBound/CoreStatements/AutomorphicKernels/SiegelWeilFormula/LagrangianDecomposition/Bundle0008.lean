module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.EmbQMapApply
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem embQ_mul_left {m n N : ℕ} (h : n + 1 = N) (L : Matrix (Fin m) (Fin m) (AE F E))
    (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : L * embQ h Q = embQ h (L * Q) := by
  ext a c
  simp only [embQ, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases eB h c with x | x <;> simp [Matrix.mul_apply]

theorem embQ_map_apply {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R)
    (a : Fin m) (v : Fin n ⊕ Fin n) : embQ h Q a (Sum.map (em0 h) (em0 h) v) = Q a v := by
  simp [embQ, eB_map]

theorem frQ_left {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (L : Matrix (Fin m) (Fin m) (AE F E))
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (L * w) = L * frQ c w := by
  rw [frQ, frQ, Matrix.mul_assoc]

theorem chartFacts : ChartFacts := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h, (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix (Fin d.n ⊕ Fin d.n) _ (AE F E)) u v := by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelC
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cancel_l {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F (b⁻¹).1 * (incM F b.1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]

theorem cancel_l' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F b.1 * (incM F (b⁻¹).1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]

theorem cancel_r' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix κ ι (AE F E)) :
    X * incM F b.1 * incM F (b⁻¹).1 = X := by
  rw [Matrix.mul_assoc, incM_mul_inv, Matrix.mul_one]

theorem mat_of_inFrame {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    g.1.1 = incM F b.1 * inFrame b g * incM F (b⁻¹).1 := by
  rw [inFrame_eq]
  simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, Matrix.mul_one]

theorem diag_of_frame {n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (tb : GL (Fin n) E)
    (h : incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (tb⁻¹).1 := by
  rw [h, cancel_r']

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F t.1 * X * incM F (t⁻¹).1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_inv_mul, Matrix.det_one, one_mul]

theorem det_conj' {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F (t⁻¹).1 * X * incM F t.1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_mul_inv, Matrix.det_one, one_mul]

theorem jPar (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    {j : G2 σ Y →* d.G} (hj : IsJ d h b j) (p : G2 σ Y) (t : GL (Fin n) (AE F E))
    (hpt : p.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * t.1) :
    ∃ t' : GL (Fin d.n) (AE F E), (j p).1.1 * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * t'.1 ∧
      Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
  obtain ⟨tb, hTb⟩ := frame_fromRows hb
  obtain ⟨td, hTd⟩ := frame_fromRows d.ok.frame
  set P := inFrame b p with hPdef
  set R0 := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR0
  set R0N := Matrix.fromRows (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) with hR0N
  set A : Matrix (Fin n) (Fin n) (AE F E) := incM F (tb⁻¹).1 * t.1 * incM F tb.1 with hA
  have hDn := diag_of_frame b tb hTb
  have hDN := diag_of_frame d.b td hTd
  have hp := mat_of_inFrame b p
  have hP : P * R0 = R0 * A := by
    have e := hpt
    rw [hp, hDn] at e
    have e2 : incM F b.1 * (P * R0) * incM F (tb⁻¹).1 = incM F b.1 * (R0 * A) * incM F (tb⁻¹).1 := by
      rw [hA]
      calc incM F b.1 * (P * R0) * incM F (tb⁻¹).1
          = incM F b.1 * P * incM F (b⁻¹).1 * (incM F b.1 * R0 * incM F (tb⁻¹).1) := by
            simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
        _ = incM F b.1 * R0 * incM F (tb⁻¹).1 * t.1 := e
        _ = incM F b.1 * (R0 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1)) * incM F (tb⁻¹).1 := by
            simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one]
    have e3 := congrArg (fun X => incM F (b⁻¹).1 * X * incM F tb.1) e2
    simpa only [Matrix.mul_assoc, cancel_l, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one] using e3
  have hblk := blk_fromRows h P A hP
  have hjp : inFrame d.b (j p) = blk h P 1 := eq_blk h _ _ (hj.2.1 p) (hj.2.2 p)
  have hjm := mat_of_inFrame d.b (j p)
  rw [hjp] at hjm
  set blkA := (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (AE F E)).submatrix (eI h) (eI h)
    with hblkA
  set T : Matrix (Fin d.n) (Fin d.n) (AE F E) := incM F td.1 * blkA * incM F (td⁻¹).1 with hT
  have hdet : T.det = t.1.det := by
    rw [hT, det_conj, hblkA, det_blkA, hA, det_conj']
  have hu : IsUnit T.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  refine ⟨Matrix.nonsingInvUnit T hu, ?_, ?_⟩
  · show (j p).1.1 * _ = _ * T
    rw [hjm, hDN]
    calc incM F d.b.1 * blk h P 1 * incM F (d.b⁻¹).1 * (incM F d.b.1 * R0N * incM F (td⁻¹).1)
        = incM F d.b.1 * (blk h P 1 * R0N) * incM F (td⁻¹).1 := by simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
      _ = incM F d.b.1 * (R0N * blkA) * incM F (td⁻¹).1 := by rw [hblk]
      _ = incM F d.b.1 * R0N * incM F (td⁻¹).1 * T := by
          rw [hT]; simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet

end PositivityTheory.SiegelWeilFormula.Ald

end
end

