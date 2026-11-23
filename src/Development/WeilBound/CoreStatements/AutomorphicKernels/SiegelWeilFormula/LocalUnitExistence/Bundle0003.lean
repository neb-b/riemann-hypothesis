module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0019
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] [NumberField E] in
theorem eps_one {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = 1 := by
  have hD : ((dbl J).map σ)ᵀ = dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose], Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

theorem eps_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = 1) : ε = 1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exact e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((-1 : ℤ) : E) = 1 := by exact_mod_cast h
      push_cast at h'
      linear_combination -h'
    exact two_ne_zero this

theorem exists_eigenvalueGLOne_eq_cuspidalLabel_gen {B : Base F E} (hB : B.IsGood σ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    stdEx_of frameConj hgtEx F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (UnitHermitianSpace.isHerm_unitSpc hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (UnitHermitianSpace.isHerm_unitSpc hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (UnitHermitianSpace.isHerm_unitSpc hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsSkewUnit
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sc1 {R : Type} [CommRing R] : Rˣ →* GL (Fin 1) R :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

omit [NumberField F] [NumberField E] in
theorem det_sc1 {R : Type} [CommRing R] (x : Rˣ) : Matrix.GeneralLinearGroup.det (sc1 x) = x := by
  ext
  simp [sc1, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

omit [NumberField F] [NumberField E] in
theorem map_det_bc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (γ : GL (Fin 1) R) :
    Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det γ) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc f γ) := by
  ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]
  rw [RingHom.map_det]
  rfl

theorem exists_skewUnit {B : Base F E} (hB : B.IsGood σ) :
    ∃ r : (AE F E)ˣ, cA σ (r : AE F E) = -(r : AE F E) ∧
      (∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v) ∧
      ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1 := by
  classical
  have hc := hB.cm
  obtain ⟨ξ, hξ, hσξ⟩ := UnitA.exists_xi hc
  obtain ⟨S, hS⟩ := UnitA.exists_S (F := F) ξ
  choose u hu1 hu2 hu3 using UnitA.exists_locUnit hB hξ hσξ
  let xv : ∀ v : Pl (F := F), (Fv F v ⊗[F] E)ˣ := fun v =>
    ⟨inclR (F := F) (Fv F v) ξ, inclR (F := F) (Fv F v) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let b : ∀ v : Pl (F := F), GL (Fin 1) (Fv F v ⊗[F] E) := fun v => if v ∈ S then sc1 (u v * (xv v)⁻¹) else 1
  have hb : ∀ v ∉ S, b v = 1 := fun v hv => if_neg hv
  let e : ∀ w : InfinitePlace F, w.Completion ⊗[F] E ≃+* ℂ := fun w =>
    RingEquiv.ofBijective (infEmb (B.emb w)) (infEmb_bijective hc (B.emb w))
  have hτ : ∀ w : InfinitePlace F, (B.emb w).1 ξ ≠ 0 := fun w => (map_ne_zero _).2 hξ
  let c : ∀ w : InfinitePlace F, GL (Fin 1) (w.Completion ⊗[F] E) := fun w =>
    sc1 (Units.map (e w).symm.toMonoidHom (Units.mk0 (Complex.I / (B.emb w).1 ξ) (div_ne_zero Complex.I_ne_zero (hτ w))))
  obtain ⟨γ, hγf, hγi⟩ := Frames.exists_GL_of_components S b hb c
  let X : (AE F E)ˣ := ⟨inclR (F := F) (AF F) ξ, inclR (F := F) (AF F) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let r : (AE F E)ˣ := Matrix.GeneralLinearGroup.det γ * X

  have hf : ∀ v, Units.map (compFin F E v).toMonoidHom r = if v ∈ S then u v else xv v := by
    intro v
    have hX : Units.map (compFin F E v).toMonoidHom X = xv v := Units.ext (UnitA.compFin_inclR v ξ)
    rw [map_mul, map_det_bc, hγf v, hX]
    by_cases hv : v ∈ S
    · simp only [b, if_pos hv, det_sc1, inv_mul_cancel_right]
    · simp only [b, if_neg hv, map_one, one_mul]
  have hfv : ∀ v, compFin F E v (r : AE F E) = ((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v]; rfl
  have hfi : ∀ v, compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) =
      (((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v, ← map_inv]; rfl

  have hi : ∀ w, infEmb (B.emb w) (compInf F E w (r : AE F E)) = Complex.I := by
    intro w
    have hX : Units.map (compInf F E w).toMonoidHom X = Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) :=
      Units.ext (UnitA.compInf_inclR w ξ)
    have h1 : Units.map (compInf F E w).toMonoidHom r = Matrix.GeneralLinearGroup.det (c w) *
        Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) := by
      rw [map_mul, map_det_bc, hγi w, hX]
    have h2 : compInf F E w (r : AE F E) = (e w).symm (Complex.I / (B.emb w).1 ξ) * inclR (F := F) w.Completion ξ := by
      have := congrArg Units.val h1
      simpa [c, det_sc1] using this
    rw [h2, map_mul]
    have h3 : infEmb (B.emb w) ((e w).symm (Complex.I / (B.emb w).1 ξ)) = Complex.I / (B.emb w).1 ξ :=
      (e w).apply_symm_apply _
    have h4 : infEmb (B.emb w) (inclR (F := F) w.Completion ξ) = (B.emb w).1 ξ := by
      change infEmb (B.emb w) ((1 : w.Completion) ⊗ₜ[F] ξ) = _
      rw [infEmb_tmul, map_one, one_mul]
    rw [h3, h4, div_mul_cancel₀ _ (hτ w)]
  refine ⟨r, ?_, fun v => ?_, fun w => ?_⟩
  ·
    have key : -(cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      refine GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) (fun v => ?_)
      · have hz : sigR w.Completion σ (compInf F E w (r : AE F E)) = -compInf F E w (r : AE F E) := by
          apply (e w).injective
          change infEmb (B.emb w) _ = infEmb (B.emb w) _
          rw [← infEmb_sigR hc, hi w, map_neg, hi w, Complex.conj_I]
        have hu : compInf F E w (r : AE F E) * compInf F E w ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compInf_cA, hz, neg_mul, neg_neg, hu]
      · have hz : sigR (Fv F v) σ (compFin F E v (r : AE F E)) = -compFin F E v (r : AE F E) := by
          rw [hfv v]
          by_cases hv : v ∈ S
          · simp only [if_pos hv]; exact hu3 v
          · simp only [if_neg hv, xv]
            rw [UnitA.sigR_inclR, hσξ, map_neg]
        have hu : compFin F E v (r : AE F E) * compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compFin_cA, hz, neg_mul, neg_neg, hu]
    have : cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) = -1 := by
      rw [← neg_neg (cA σ (r : AE F E) * _), key]
    calc cA σ (r : AE F E) = cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) * (r : AE F E) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = -(r : AE F E) := by rw [this, neg_one_mul]
  · rw [hfv v, hfi v]
    by_cases hv : v ∈ S
    · simp only [if_pos hv]; exact ⟨hu1 v, hu2 v⟩
    · simp only [if_neg hv]; exact hS v hv
  · change ‖infEmb (B.emb w) (compInf F E w (r : AE F E))‖ = 1
    rw [hi w, Complex.norm_I]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IncMInvmul
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

def incGL (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) b

theorem incGL_val (b : GL (Fin n ⊕ Fin n) E) : (incGL (F := F) b).1 = incM F b.1 := rfl

theorem incGL_inv (b : GL (Fin n ⊕ Fin n) E) : (incGL (F := F) b)⁻¹ = incGL b⁻¹ := (map_inv _ _).symm

theorem incM_tr {α β : Type} (X : Matrix α β E) : incM F Xᵀ = (incM F X)ᵀ := Matrix.transpose_map

theorem incM_cA {α β : Type} (X : Matrix α β E) : (incM F X).map (cA σ) = incM F (X.map σ) := by ext; rfl

theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext (i | i) (j | j) <;> simp [incM, dbl]

theorem incM_mulT {α β γ : Type} [Fintype β] (X : Matrix α β E) (Z : Matrix β γ E) :
    incM F (X * Z) = incM F X * incM F Z := Matrix.map_mul

theorem incM_invmul (b : GL (Fin n ⊕ Fin n) E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← incM_mulT, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_A {J : Matrix (Fin n) (Fin n) E} {b : GL (Fin n ⊕ Fin n) E} {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E}
    (h : b.1ᵀ * dbl J * b.1.map σ = G) :
    (incGL (F := F) b).1ᵀ * dbl (incM F J) * (incGL b).1.map (cA σ) = incM F G := by
  rw [incGL_val, incM_cA, ← incM_dbl, ← incM_tr, ← incM_mulT, ← incM_mulT, h]

def dgv (u : AE F E) : Fin n ⊕ Fin n → AE F E := Sum.elim (fun _ => u) (fun _ => 1)

def dgU (r : (AE F E)ˣ) : GL (Fin n ⊕ Fin n) (AE F E) where
  val := Matrix.diagonal (dgv (r : AE F E))
  inv := Matrix.diagonal (dgv ((r⁻¹ : (AE F E)ˣ) : AE F E))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp [dgv]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp [dgv]

theorem dgU_val (r : (AE F E)ˣ) : (dgU (n := n) r).1 = Matrix.diagonal (dgv (r : AE F E)) := rfl

theorem dgU_inv_val (r : (AE F E)ˣ) : ((dgU (n := n) r)⁻¹).1 = Matrix.diagonal (dgv ((r⁻¹ : (AE F E)ˣ) : AE F E)) := rfl

theorem dg_jeps (r : (AE F E)ˣ) (ε ε₀ : ℤˣ)
    (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E)) :
    (dgU (n := n) r).1ᵀ * incM F (Ald.jeps n ε) * (dgU r).1.map (cA σ) = (r : AE F E) • incM F (Ald.jeps n ε₀) := by
  rw [dgU_val, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _)]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [dgv, Ald.jeps, incM, Matrix.diagonal_mul, Matrix.mul_diagonal, hij] <;> rw [hr, mul_comm]

def MU (b b₀ : GL (Fin n ⊕ Fin n) E) (r : (AE F E)ˣ) : GL (Fin n ⊕ Fin n) (AE F E) := incGL b * dgU r * incGL b₀⁻¹

theorem MU_gram {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E} {ε ε₀ : ℤˣ}
    (he : b.1ᵀ * dbl Y.J * b.1.map σ = Ald.jeps n ε) (he₀ : b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n ε₀)
    (r : (AE F E)ˣ) (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E)) :
    (MU b b₀ r).1ᵀ * dbl (incM F Y.J) * (MU b b₀ r).1.map (cA σ) = (r : AE F E) • dbl (incM F Y₀.J) := by
  have h1 := gram_A (F := F) he
  have h0 := gram_inv (cA σ) (incGL (F := F) b₀) (gram_A (F := F) he₀)
  rw [incGL_inv] at h0
  simp only [MU, Units.val_mul, Matrix.transpose_mul, map_mul_c]
  calc (incGL b₀⁻¹).1ᵀ * ((dgU r).1ᵀ * (incGL b).1ᵀ) * dbl (incM F Y.J) *
        ((incGL b).1.map (cA σ) * (dgU r).1.map (cA σ) * (incGL b₀⁻¹).1.map (cA σ)) =
      (incGL b₀⁻¹).1ᵀ * ((dgU r).1ᵀ * ((incGL b).1ᵀ * dbl (incM F Y.J) * (incGL b).1.map (cA σ)) * (dgU r).1.map (cA σ)) *
        (incGL b₀⁻¹).1.map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, dg_jeps r ε ε₀ hr, Matrix.mul_smul, Matrix.smul_mul, h0]

theorem inFrame_cj {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E} (r : (AE F E)ˣ)
    (hM : (MU b b₀ r).1ᵀ * dbl (incM F Y.J) * (MU b b₀ r).1.map (cA σ) = (r : AE F E) • dbl (incM F Y₀.J))
    (z : G2 σ Y₀) :
    inFrame b (cj (cA σ) (MU b b₀ r) (r : AE F E) hM z : G2 σ Y) = (dgU r).1 * inFrame b₀ z * ((dgU r)⁻¹).1 := by
  show incM F (b⁻¹).1 * (MU b b₀ r * z.1 * (MU b b₀ r)⁻¹).1 * incM F b.1 =
    (dgU r).1 * (incM F (b₀⁻¹).1 * z.1.1 * incM F b₀.1) * ((dgU r)⁻¹).1
  simp only [MU, mul_inv_rev, incGL_inv, inv_inv, Units.val_mul, incGL_val]
  simp only [Matrix.mul_assoc]
  rw [incM_invmul, Matrix.mul_one, ← Matrix.mul_assoc (incM F (b⁻¹).1), incM_invmul, Matrix.one_mul]

theorem dg_entry (r : (AE F E)ˣ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (i j : Fin n ⊕ Fin n) :
    ((dgU r).1 * X * ((dgU r)⁻¹).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) i j = dgv (r : AE F E) i * X i j * dgv ((r⁻¹ : (AE F E)ˣ) : AE F E) j := by
  rw [dgU_val, dgU_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dg_fin (r : (AE F E)ˣ)
    (hrf : ∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : ∀ i j, finOne F • X i j ∈ intHat F E) (i j : Fin n ⊕ Fin n) :
    finOne F • ((dgU r).1 * X * ((dgU r)⁻¹).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) i j ∈ intHat F E := by
  rw [dg_entry]
  refine (Frame.mem_intHat _).2 fun v => ?_
  have hx := (Frame.mem_intHat _).1 (hX i j) v
  rw [map_mul, map_mul]
  refine mul_mem (mul_mem ?_ hx) ?_
  · rcases i with i | i
    · exact (hrf v).1
    · simp only [dgv, Sum.elim_inr, map_one]; exact one_mem _
  · rcases j with j | j
    · exact (hrf v).2
    · simp only [dgv, Sum.elim_inr, map_one]; exact one_mem _

theorem dg_arch (r : (AE F E)ˣ) (π : AE F E →+* ℂ) (hri : ‖π (r : AE F E)‖ = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : X.map π * (X.map π)ᴴ = 1) :
    ((dgU r).1 * X * ((dgU r)⁻¹).1).map π * (((dgU r).1 * X * ((dgU r)⁻¹).1).map π)ᴴ = 1 := by
  have h0 : π (r : AE F E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hri; exact zero_ne_one hri
  have h2 : star (π (r : AE F E)) * π (r : AE F E) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hri]; simp
  have hinv : π ((r⁻¹ : (AE F E)ˣ) : AE F E) = star (π (r : AE F E)) := by
    have h1 : π (r : AE F E) * π ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact mul_left_cancel₀ h0 (h1.trans (by rw [mul_comm]; exact h2.symm))
  have e : ((dgU r).1 * X * ((dgU r)⁻¹).1).map π =
      Matrix.diagonal (fun i => π (dgv (r : AE F E) i)) * X.map π * Matrix.diagonal (star fun i => π (dgv (r : AE F E) i)) := by
    rw [Matrix.map_mul, Matrix.map_mul, dgU_val, dgU_inv_val, Matrix.diagonal_map (map_zero π),
      Matrix.diagonal_map (map_zero π)]
    congr 2
    funext i
    rcases i with i | i
    · simp only [dgv, Sum.elim_inl, Pi.star_apply, hinv]
    · simp [dgv]
  rw [e]
  refine diag_unitary _ (fun i => ?_) _ hX
  rcases i with i | i
  · exact h2
  · simp [dgv]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

