module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast
section
noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

def eI {N n : ℕ} (h : n + 1 = N) : Fin N ≃ Fin n ⊕ Fin 1 := (finCongr h.symm).trans finSumFinEquiv.symm

def eB {N n : ℕ} (h : n + 1 = N) : Fin N ⊕ Fin N ≃ (Fin n ⊕ Fin n) ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr (eI h) (eI h)).trans (Equiv.sumSumSumComm _ _ _ _)

theorem index_embedded_equiv {N n : ℕ} (h : n + 1 = N) (i : Fin n) : eI h (em0 h i) = Sum.inl i := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.em0 h i) = Fin.castAdd 1 i := Fin.ext rfl
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_castAdd]

theorem index_last_equiv {N n : ℕ} (h : n + 1 = N) : eI h (i0 h) = Sum.inr 0 := by
  have hi : finCongr h.symm (PositivityTheory.SiegelWeilFormula.Ald.i0 h) = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [PositivityTheory.SiegelWeilFormula.Ald.i0])
  rw [PositivityTheory.SiegelWeilFormula.Ald.eI, Equiv.trans_apply, hi, finSumFinEquiv_symm_apply_natAdd]

theorem eB_map {N n : ℕ} (h : n + 1 = N) (u : Fin n ⊕ Fin n) :
    eB h (Sum.map (em0 h) (em0 h) u) = Sum.inl u := by
  rcases u with a | a
  · show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _
    rw [PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]
    rfl
  · show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.em0 h a))) = _
    rw [PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv]
    rfl

theorem block_index_inl_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inl (i0 h)) = Sum.inr (Sum.inl 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

theorem block_index_inr_last {N n : ℕ} (h : n + 1 = N) : eB h (Sum.inr (i0 h)) = Sum.inr (Sum.inr 0) := by
  show Equiv.sumSumSumComm _ _ _ _ (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.eI h (PositivityTheory.SiegelWeilFormula.Ald.i0 h))) = _
  rw [PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv]
  rfl

theorem idx_cases {N n : ℕ} (h : n + 1 = N) (u : Fin N ⊕ Fin N) :
    (∃ u', u = Sum.map (em0 h) (em0 h) u') ∨ u = Sum.inl (i0 h) ∨ u = Sum.inr (i0 h) := by
  have key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h := by
    intro i
    by_cases hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inr hi
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi
      exact Or.inl ⟨j, rfl⟩
  rcases u with i | i <;> rcases key i with ⟨j, rfl⟩ | rfl
  · exact Or.inl ⟨Sum.inl j, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨Sum.inr j, rfl⟩
  · exact Or.inr (Or.inr rfl)

theorem eB_out {N n : ℕ} (h : n + 1 = N) (u : Fin N ⊕ Fin N) (hu : u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N))) :
    ∃ p, eB h u = Sum.inr p := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · exact ⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last h⟩
  · exact ⟨_, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last h⟩

variable {R : Type*}

def blk [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R :=
  (Matrix.fromBlocks M 0 0 P).submatrix (eB h) (eB h)

theorem blk_apply [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (u v : Fin N ⊕ Fin N) :
    blk h M P u v = Matrix.fromBlocks M 0 0 P (eB h u) (eB h v) := rfl

theorem blk_map_apply [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (u v : Fin n ⊕ Fin n) :
    blk h M P (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v) = M u v := by
  rw [PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.eB_map, PositivityTheory.SiegelWeilFormula.Ald.eB_map]
  rfl

theorem blk_sub [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = M :=
  Matrix.ext fun u v => PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply h M P u v

theorem blk_mul [NonUnitalNonAssocSemiring R] {N n : ℕ} (h : n + 1 = N) (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P P' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : blk h M P * blk h M' P' = blk h (M * M') (P * P') := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blk_one [Semiring R] {N n : ℕ} (h : n + 1 = N) : blk h (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) 1 = 1 := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blk_transpose [Zero R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : (blk h M P)ᵀ = blk h Mᵀ Pᵀ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem blk_map [Zero R] {S : Type*} [Zero S] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) (f : R → S) (hf : f 0 = 0) :
    (blk h M P).map f = blk h (M.map f) (P.map f) := by
  ext u v
  rw [Matrix.map_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply]
  rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with a | a <;> rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with b | b <;>
    simp [hf]

theorem blk_conjTranspose [AddMonoid R] [StarAddMonoid R] {N n : ℕ} (h : n + 1 = N)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (P : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (blk h M P)ᴴ = blk h Mᴴ Pᴴ := by
  simp [PositivityTheory.SiegelWeilFormula.Ald.blk, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem blk_inj [Zero R] {N n : ℕ} (h : n + 1 = N) {M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    {P P' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R} (e : blk h M P = blk h M' P') : M = M' ∧ P = P' := by
  constructor
  · ext i j
    have hij := congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl i)))
      ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inl j))
    simpa [PositivityTheory.SiegelWeilFormula.Ald.blk_apply] using hij
  · ext i j
    have hij := congrFun (congrFun e ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr i)))
      ((PositivityTheory.SiegelWeilFormula.Ald.eB h).symm (Sum.inr j))
    simpa [PositivityTheory.SiegelWeilFormula.Ald.blk_apply] using hij

theorem blk_eq_one_iff [Semiring R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    blk h M 1 = 1 ↔ M = 1 := by
  constructor
  · intro e
    exact (PositivityTheory.SiegelWeilFormula.Ald.blk_inj h (e.trans (PositivityTheory.SiegelWeilFormula.Ald.blk_one h).symm)).1
  · rintro rfl
    exact PositivityTheory.SiegelWeilFormula.Ald.blk_one h

theorem eq_blk [Semiring R] {N n : ℕ} (h : n + 1 = N) (X : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hin : X.submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = M)
    (hout : ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin N ⊕ Fin N)), ∀ v,
      X u v = (1 : Matrix _ _ R) u v ∧ X v u = (1 : Matrix _ _ R) v u) : X = blk h M 1 := by
  have hrow : ∀ u v, u ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) →
      X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v := by
    intro u v hu
    obtain ⟨p, hp⟩ := PositivityTheory.SiegelWeilFormula.Ald.eB_out h u hu
    rw [(hout u hu v).1, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]
    rcases PositivityTheory.SiegelWeilFormula.Ald.eB h v with q | q <;> rfl
  have hcol : ∀ u v, v ∈ ({Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.i0 h), Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.i0 h)} : Set (Fin N ⊕ Fin N)) →
      X u v = PositivityTheory.SiegelWeilFormula.Ald.blk h M 1 u v := by
    intro u v hv
    obtain ⟨p, hp⟩ := PositivityTheory.SiegelWeilFormula.Ald.eB_out h v hv
    rw [(hout v hv u).2, ← PositivityTheory.SiegelWeilFormula.Ald.blk_one h, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hp]
    rcases PositivityTheory.SiegelWeilFormula.Ald.eB h u with q | q <;> rfl
  ext u v
  rcases PositivityTheory.SiegelWeilFormula.Ald.idx_cases h u with ⟨u', rfl⟩ | hu | hu
  · rcases PositivityTheory.SiegelWeilFormula.Ald.idx_cases h v with ⟨v', rfl⟩ | hv | hv
    · rw [PositivityTheory.SiegelWeilFormula.Ald.blk_map_apply]
      exact congrFun (congrFun hin u') v'
    · exact hcol _ _ (by simp [hv])
    · exact hcol _ _ (by simp [hv])
  · exact hrow _ _ (by simp [hu])
  · exact hrow _ _ (by simp [hu])

theorem jepsR_blk [Semiring R] {N n : ℕ} (h : n + 1 = N) (c : R) :
    (Matrix.fromBlocks 0 1 (c • 1) 0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R) =
      blk h (Matrix.fromBlocks 0 1 (c • 1) 0) (Matrix.fromBlocks 0 1 (c • 1) 0) := by
  have hne : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.em0 h a ≠ PositivityTheory.SiegelWeilFormula.Ald.i0 h := fun a =>
    (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h _).2 ⟨a, rfl⟩
  have hne' : ∀ a : Fin n, PositivityTheory.SiegelWeilFormula.Ald.i0 h ≠ PositivityTheory.SiegelWeilFormula.Ald.em0 h a := fun a => (hne a).symm
  have hl : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inl (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inl a) :=
    fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)
  have hr : ∀ a, PositivityTheory.SiegelWeilFormula.Ald.eB h (Sum.inr (PositivityTheory.SiegelWeilFormula.Ald.em0 h a)) = Sum.inl (Sum.inr a) :=
    fun a => PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)
  have key : ∀ i : Fin N, (∃ j, i = PositivityTheory.SiegelWeilFormula.Ald.em0 h j) ∨ i = PositivityTheory.SiegelWeilFormula.Ald.i0 h := by
    intro i
    by_cases hi : i = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inr hi
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h i).1 hi
      exact Or.inl ⟨j, rfl⟩
  ext u v
  rcases u with i | i <;> rcases v with j | j <;> rcases key i with ⟨i, rfl⟩ | rfl <;>
    rcases key j with ⟨j, rfl⟩ | rfl <;>
    simp [PositivityTheory.SiegelWeilFormula.Ald.blk_apply, hl, hr, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last, Matrix.one_apply, hne, hne',
      (PositivityTheory.SiegelWeilFormula.Ald.em0_injective h).eq_iff]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def YFrame : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), SignOK d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε

def JEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, IsJ d h b j

def KStd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → IsJ d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)

def HgtPull : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b → IsJ d h b j → IsHgt (d.K.comap j) (d.a ∘ j)

def ModelEx : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → IsJ d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ Res d h b j dd om l

theorem ldEx_of_leaves (h1 : YFrame) (h2 : JEx) (h3 : KStd) (h4 : HgtPull) (h5 : ModelEx) : TAll → AuxiliaryPrimeFunction → LDEx := by
  intro hT hA F E _ _ _ _ _ σ d hd
  have h : d.n - 1 + 1 = d.n := by omega
  obtain ⟨Y, b, ε, hsign, hframe, hdb, hb⟩ := h1 F E σ d (d.n - 1) h (by omega)
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε hdb hb
  have hK := h3 F E σ d (d.n - 1) h Y b j hframe hj
  have hH := h4 F E σ d (d.n - 1) h Y b j (by omega) hsign hframe hj
  obtain ⟨κ, hκ, dd, om, S, l, hdbl, hres⟩ :=
    h5 hT hA F E σ d (d.n - 1) h Y b j (by omega) hsign hframe ⟨ε, hdb, hb⟩ hj
  exact ⟨{
      n := d.n - 1, Y := Y, κ := κ, fin := hκ, dd := dd, om := om, S := S, l := l, b := b
      K := d.K.comap j, a := d.a ∘ j
      ok := {
        good := d.ok.good, hm := d.ok.hm, hn := by omega, aniso := d.ok.aniso, sign := hsign
        hecke := d.ok.hecke, res := d.ok.res, dbl := hdbl, frame := hframe, stdK := hK, hgt := hH
        haar := d.ok.haar, dom := d.ok.dom }
      i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1
      j_in := hj.2.1, j_out := hj.2.2, res := hres }⟩

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) : AF F :=
  (Algebra.TensorProduct.basis (AF F) bs).repr (X k.1 k.2.1) k.2.2

def ev0 (κ : Type) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Ek {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (k : Fin m × Fin n × Fin 2) : Mx F E m n :=
  Matrix.single k.1 k.2.1 ((1 : AF F) ⊗ₜ[F] bs k.2.2)

def Bf {m n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (X Z : Mx F E m n) : AF F :=
  Algebra.trace (AF F) (AE F E) (Xᵀ * incM F J * Z.map (cA σ)).trace

def IsAdapted {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2)) : Prop :=
  ∀ Z X : Mx F E m n, dd.e (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (crdB bs X, fun k => Bf σ A.J Z (Ek bs k))

def SDarb : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), B.IsGood σ → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd ∧ ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : Fin m × Fin n × Fin 2 → F,
      dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

def SEv : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), B.IsGood σ → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∀ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd →
    ev0 (F := F) (Fin m × Fin n × Fin 2) ∈ (adeleClass F).adm (Fin m × Fin n × Fin 2) ∧
    (∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2),
      ev0 _ (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = ev0 _ Φ) ∧
    ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2), HasSum (fun y : Matrix (Fin m) (Fin n) E =>
      ev0 _ (dd.rho B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)

end PositivityTheory.SiegelWeilFormula.Ald

end
end

