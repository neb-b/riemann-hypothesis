module

public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsLocUnit
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_xi (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_cases hx : ∃ x : E, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push Not at hx
    exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx] at this
      exact this.symm
    have := h.2.1
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) (InfinitePlace.isReal_mk_iff.2 hr)

omit [NumberField E] in
theorem compFin_cA (v : Pl (F := F)) (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compInf_cA (w : InfinitePlace F) (z : AE F E) :
    compInf F E w (cA σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compFin_inclR (v : Pl (F := F)) (x : E) : compFin F E v (inclR (AF F) x) = inclR (Fv F v) x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem compInf_inclR (w : InfinitePlace F) (x : E) : compInf F E w (inclR (AF F) x) = inclR w.Completion x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : w.Completion) ⊗ₜ[F] x
  simp

omit [NumberField F] [NumberField E] in
theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := rfl

theorem exists_S (ξ : E) : ∃ S : Finset (Pl (F := F)), ∀ v ∉ S,
    inclR (Fv F v) ξ ∈ intLoc F E v ∧ inclR (Fv F v) ξ⁻¹ ∈ intLoc F E v := by
  have h := (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ).and (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ⁻¹)
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1.mem, hv.2.mem⟩

theorem exists_locUnit {B : Base F E} (hB : B.IsGood σ) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl (F := F)) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ sigR (Fv F v) σ u = -(u : Fv F v ⊗[F] E) := by
  have hc := hB.cm
  rcases (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v :
    Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w) with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · set e := splitAlgEquiv hc τ
    have hu : e.symm (1, -1) * e.symm (1, -1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul, neg_mul_neg, mul_one]
      exact map_one _
    let u : (Fv F v ⊗[F] E)ˣ := ⟨e.symm (1, -1), e.symm (1, -1), hu, hu⟩
    have hm : e.symm (1, -1) ∈ intLoc F E v := (mem_intLoc_iff_split hc τ).2
      ⟨by rw [splitProj_symm]; exact one_mem _, by rw [splitProj_comp_symm]; exact neg_mem (one_mem _)⟩
    refine ⟨u, hm, hm, ?_⟩
    apply e.injective
    change e (sigR (Fv F v) σ (e.symm (1, -1))) = e (-(e.symm (1, -1)))
    rw [splitAlgEquiv_sigR, map_neg, AlgEquiv.apply_symm_apply]
    simp
  · have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hv0 : w.valuation E ξ ≠ 0 := (Valuation.ne_zero_iff _).2 hξ
    set m := WithZero.log (w.valuation E ξ)
    set z : E := algebraMap F E (π ^ m) * ξ with hzdef
    have hz : w.valuation E z = 1 := by
      rw [hzdef, map_mul, GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hw, map_zpow₀, hπ,
        ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp [m]
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hz; exact zero_ne_one hz
    have hint : ∀ y : E, w.valuation E y = 1 → inclR (Fv F v) y ∈ intLoc F E v := by
      intro y hy
      rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      change GlobalTheory.LFun.toCompl h ((1 : Fv F v) ⊗ₜ[F] y) ∈ _
      rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
      change _ ∈ HeightOneSpectrum.adicCompletionIntegers E w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y
      exact (this.trans hy).le
    have h1 : inclR (F := F) (Fv F v) z * inclR (F := F) (Fv F v) z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
    have h2 : inclR (F := F) (Fv F v) z⁻¹ * inclR (F := F) (Fv F v) z = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    refine ⟨⟨inclR (Fv F v) z, inclR (Fv F v) z⁻¹, h1, h2⟩, hint z hz, hint z⁻¹ (by rw [map_inv₀, hz, inv_one]), ?_⟩
    change sigR (Fv F v) σ (inclR (Fv F v) z) = -inclR (Fv F v) z
    rw [sigR_inclR, hzdef, map_mul, AlgHom.commutes, hσξ, mul_neg, map_neg]

end PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.GramInvSmul
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

set_option linter.unusedSectionVars false

section Generic

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι] (c : S →ₐ[R] S)

theorem map_mul_c (A B : Matrix ι ι S) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul

theorem gram_inv {H J : Matrix ι ι S} (M : GL ι S) (hM : M.1ᵀ * H * M.1.map c = J) :
    (M⁻¹).1ᵀ * J * (M⁻¹).1.map c = H := by
  subst hM
  have h1 : (M⁻¹).1ᵀ * M.1ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : M.1.map c * (M⁻¹).1.map c = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c c, Units.mul_inv]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  calc (M⁻¹).1ᵀ * (M.1ᵀ * H * M.1.map c) * (M⁻¹).1.map c
      = ((M⁻¹).1ᵀ * M.1ᵀ) * H * (M.1.map c * (M⁻¹).1.map c) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem conj_mem {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) {y : GL ι S}
    (hy : y ∈ UG c H₀) : M * y * M⁻¹ ∈ UG c H := by
  have hy' : (y : Matrix ι ι S)ᵀ * H₀ * (y : Matrix ι ι S).map c = H₀ := hy
  have hmid : (y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c
      = M.1ᵀ * H * M.1.map c := by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, hy']
  have key : (M⁻¹).1ᵀ * ((y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c)
      * (M⁻¹).1.map c = H := by
    rw [hmid]
    exact PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M rfl
  show ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S)ᵀ * H * ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S).map c = H
  simp only [Units.val_mul, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c]
  simpa only [Matrix.mul_assoc] using key

theorem gram_inv_smul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : Sˣ) (hM : M.1ᵀ * H * M.1.map c = (s : S) • H₀) :
    (M⁻¹).1ᵀ * H₀ * (M⁻¹).1.map c = ((s⁻¹ : Sˣ) : S) • H := by
  have h := PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M hM
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  rw [← h, smul_smul, Units.inv_mul, one_smul]

def cj {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) : UG c H :=
  ⟨M * z.1 * M⁻¹, conj_mem c M s hM z.2⟩

theorem cj_val {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    (cj c M s hM z).1 = M * z.1 * M⁻¹ := rfl

theorem cj_mul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z z' : UG c H₀) :
    cj c M s hM (z * z') = cj c M s hM z * cj c M s hM z' := by
  apply Subtype.ext
  show M * ((z : GL ι S) * (z' : GL ι S)) * M⁻¹ = (M * (z : GL ι S) * M⁻¹) * (M * (z' : GL ι S) * M⁻¹)
  group

theorem cj_inv {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    cj c M s hM z⁻¹ = (cj c M s hM z)⁻¹ := by
  apply Subtype.ext
  show M * (z : GL ι S)⁻¹ * M⁻¹ = (M * (z : GL ι S) * M⁻¹)⁻¹
  group

end Generic

section Unitary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_unitary (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1) (X : Matrix ι ι ℂ) (hX : X * Xᴴ = 1) :
    (Matrix.diagonal d * X * Matrix.diagonal (star d)) * (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ = 1 := by
  have h1 : Matrix.diagonal (star d) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd i
  have h2 : Matrix.diagonal d * Matrix.diagonal (star d) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hd i
  have e : (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ
      = Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_star, Matrix.mul_assoc]
  rw [e]
  calc Matrix.diagonal d * X * Matrix.diagonal (star d) * (Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)))
      = Matrix.diagonal d * X * (Matrix.diagonal (star d) * Matrix.diagonal d) * Xᴴ * Matrix.diagonal (star d) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal d * Matrix.diagonal (star d) := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc (Matrix.diagonal d) X, hX, Matrix.mul_one]
    _ = 1 := h2

end Unitary

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

