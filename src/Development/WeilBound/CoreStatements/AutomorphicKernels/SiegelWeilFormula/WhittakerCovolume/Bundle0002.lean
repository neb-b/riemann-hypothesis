module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.FrameSignEqHermitianSign
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem rel_sigma_sigma (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ) : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem rel_cA_incM {a b : Type} (X : Matrix a b E) : (incM F X).map (cA σ) = incM F (X.map σ) := by
  ext i j
  simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]

theorem rel_frame (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : d.G) :
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 * (inFrame d.b y).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (incM_mul_inv d) hM
  rw [← hF]
  exact this

theorem rel_nA_cond (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (β : nA σ d.Y d.b) :
    β.1ᵀ + ((ε : ℤ) : AE F E) • β.1.map (cA σ) = 0 := by
  obtain ⟨β, hβ⟩ := β
  show βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0
  induction hβ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hx
    have h := rel_frame d ε hε y
    rw [hy] at h
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.fromBlocks_inj] at h
    rw [add_comm]
    have h4 := h.2.2.2
    rw [Matrix.smul_mul, Matrix.one_mul] at h4
    exact h4
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.transpose_add, Matrix.map_add _ (map_add (cA σ)), smul_add]
    calc _ = (xᵀ + ((ε : ℤ) : AE F E) • x.map (cA σ)) + (yᵀ + ((ε : ℤ) : AE F E) • y.map (cA σ)) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  | neg x _ hx =>
    rw [Matrix.transpose_neg, Matrix.map_neg _ (map_neg (cA σ)), smul_neg, ← neg_add, hx, neg_zero]

theorem frame_sign_eq_hermitian_sign (d : SD σ) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (c : E)
    (hc : d.Y.J.map σ = c • d.Y.Jᵀ) (i : Fin d.n) : ((ε : ℤ) : E) = c := by
  have hD : (dbl d.Y.J).map σ = c • (dbl d.Y.J)ᵀ := by
    simp only [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, hc,
      Matrix.map_neg _ (map_neg σ), Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.transpose_neg,
      smul_zero, smul_neg]
  have hbb : (d.b.1.map σ).map σ = d.b.1 := by
    ext i j
    simp [hσ]
  have h1 := congrArg σ.mapMatrix hε
  simp only [map_mul, AlgHom.mapMatrix_apply, hD, hbb] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.transpose_map] at h2
  rw [← Matrix.mul_assoc, hε] at h2
  have := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl i)
  simp [Matrix.fromBlocks_map] at this
  have hε2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc ((ε : ℤ) : E) = ((ε : ℤ) : E) * (c * ((ε : ℤ) : E)) := by rw [this, mul_one]
    _ = c * (((ε : ℤ) : E) * ((ε : ℤ) : E)) := by ring
    _ = c := by rw [hε2, mul_one]

theorem rel_sign (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((∀ i j, σ (d.Y.J j i) = -d.Y.J i j) → ε = -1) ∧ ((∀ i j, σ (d.Y.J j i) = d.Y.J i j) → ε = 1) := by
  have hσ := rel_sigma_sigma d.ok.good.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  constructor
  · intro h
    have := frame_sign_eq_hermitian_sign d hσ ε hε (-1) (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
  · intro h
    have := frame_sign_eq_hermitian_sign d hσ ε hε 1 (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))

theorem rel_anti (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ η : E, η ≠ 0 ∧ σ η = -η := by
  have hσ := rel_sigma_sigma h
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    have := h.2.1
    let w : InfinitePlace E := Classical.arbitrary _
    have hw : w.IsComplex := NumberField.IsTotallyComplex.isComplex w
    rw [NumberField.InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext y
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← h.2.2.2, hc]
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hσ, neg_sub]

theorem rel_eta (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ∃ η : E, η ≠ 0 ∧ σ η = -(((ε : ℤ) : E) * η) ∧ ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j := by
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := (rel_sign d ε hε).1 hY
    subst he
    refine ⟨1, one_ne_zero, by simp, fun i j => by simp [hA.herm i j]⟩
  · have he := (rel_sign d ε hε).2 hY
    subst he
    obtain ⟨η, hη, hση⟩ := rel_anti d.ok.good.cm
    refine ⟨η, hη, by simp [hση], fun i j => ?_⟩
    rw [map_mul, hση, hA.skew i j, neg_mul_neg]

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (E) in
def OE (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, z = a ⊗ₜ[F] (o : E)}


variable (E) in
def lat (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.pi Set.univ fun _ => OE E v

def latM (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) :
    AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  (lat E v n).map M.mulVecLin.toAddMonoidHom

theorem par_topleft (d : SD σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t.1 * incM F tb.1 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := incM_inv_mul d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inl i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq] using this

theorem sigR_eq_cA (z : AE F E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem inFrame_form (d : SD σ) (y : d.G) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (∃ ε : ℤˣ, C' = ((ε : ℤ) : AE F E) • 1) ∧
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (inFrame d.b y).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨((ε : ℤ) : AE F E) • 1, ⟨ε, rfl⟩, ?_⟩
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (incM_mul_inv d) hM
  rw [← hF]
  exact this

theorem levi_tu (d : SD σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) :
    t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨C', -, h⟩ := inFrame_form d x
  rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1

theorem frame_iwa (d : SD σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := parabolic_lower_block_zero d p t' hp
  obtain ⟨tb, htl⟩ := par_topleft d p t' hp
  set A := (inFrame d.b p).toBlocks₁₁ with hA
  set B := (inFrame d.b p).toBlocks₁₂ with hB
  set D₀ := (inFrame d.b p).toBlocks₂₂ with hD₀
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨C', ⟨ε, hC'⟩, hform⟩ := inFrame_form d p
  rw [hPb, hC'] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    have := congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
    simpa [smul_smul, hεε] using this
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
    exact this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  refine ⟨hDu.unit, k, hk, ?_, ?_, ?_⟩
  · rw [d.ok.hgt.val p t' hp k hk]
    have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
      rw [htl, Matrix.det_mul, Matrix.det_mul]
      have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
        rw [← Matrix.det_mul]
        have e : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
          simp only [incM, ← Matrix.map_mul, Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        rw [e, Matrix.det_one]
      simp only [Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination (t'.1.det) * hinv
    have hU : Matrix.GeneralLinearGroup.det hDu.unit *
        GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
      ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
        GlobalTheory.Doubling.conjUnit, Units.coe_map]
      change D₀.det * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ t'.1.det = 1
      rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]
      exact hdet
    have := congrArg (GlobalTheory.Doubling.absE F E) hU
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
    have hpos : (0 : ℝ≥0) < GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit) := by
      rcases eq_or_ne (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit)) 0 with h | h
      · rw [h, zero_mul] at this; exact absurd this zero_ne_one
      · exact pos_iff_ne_zero.2 h
    rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]
  · rw [inFrame_mul, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
  · rw [inFrame_mul, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]

theorem bottom_rows (d : SD σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : nA σ d.Y d.b → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : nA σ d.Y d.b) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [inFrame_mul, inFrame_mul, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]

theorem bottom_onto {S : Type} [CommRing S] (O : Subring S) {n : Type} [Fintype n] [DecidableEq n]
    (k k' : Matrix (n ⊕ n) (n ⊕ n) S) (hkk : k * k' = 1) (hk : ∀ i j, k i j ∈ O) (hk' : ∀ i j, k' i j ∈ O) (y : n → S)
    (hy : ∀ i, y i ∈ O) : ∃ y₁ y₂ : n → S, (∀ i, y₁ i ∈ O) ∧ (∀ i, y₂ i ∈ O) ∧
      k.toBlocks₂₁.mulVec y₁ + k.toBlocks₂₂.mulVec y₂ = y := by
  classical
  set z := k'.mulVec (Sum.elim (0 : n → S) y) with hz
  have hzO : ∀ j, z j ∈ O := fun j => by
    simp only [hz, Matrix.mulVec, dotProduct]
    exact O.sum_mem fun c _ => O.mul_mem (hk' j c) (by cases c <;> simp [hy, O.zero_mem])
  refine ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), fun i => hzO _, fun i => hzO _, ?_⟩
  have hkz : k.mulVec z = Sum.elim (0 : n → S) y := by rw [hz, Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
  funext i
  have := congrFun hkz (Sum.inr i)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inr] at this
  simpa [Matrix.mulVec, dotProduct, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] using this

end PositivityTheory.SiegelWeilFormula.KWhit.Ht

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasND
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_det_of_hasSig {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin m := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin m) (Fin m) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hd : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
      Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  intro h0
  apply hd
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]

theorem meas_detA (d : SD σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact meas_det_of_hasSig (hA.sig w)
    · have h := meas_det_of_hasSig (hA.sig w)
      rw [Matrix.det_smul] at h
      intro h0; exact h (by rw [h0, mul_zero])
  intro h0
  apply key
  have hm := RingHom.map_det (d.B.emb w).1 d.A.J
  rw [RingHom.mapMatrix_apply, h0, map_zero] at hm
  exact hm.symm

theorem meas_hermND' (d : SD σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hh j i
  · rw [Jd, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hη) (meas_detA d)

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

def RelAlg : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : SD σ), ∃ (η : E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n),
    η ≠ 0 ∧ (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) ∧
    (∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0 → y = 0) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) ∧
    ∀ T : nF σ d.Y d.b, IsND T → ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ ∧
      (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0

def SdEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J →
  ∀ ψ : AddChar (AF F) ℂ, HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ M J (AF F) ψ n μ) ∧ ∃ ν, HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) ψ n ν

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

