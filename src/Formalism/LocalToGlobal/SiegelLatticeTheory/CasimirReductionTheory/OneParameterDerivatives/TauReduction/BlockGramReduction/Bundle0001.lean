module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.DetGramNonneg
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

variable (I : AutInst)

def cmat (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  Matrix.of fun i a => coordV I x v (b a) i

theorem gramV_eq (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (cmat I x v b)ᴴ * cmat I x v b := by
  ext a c
  simp [gramV, cmat, Matrix.mul_apply, Matrix.conjTranspose_apply]

def subOfEq {x x' : I.GA} (h : latSet I x' = latSet I x) (s : Sub I x) : Sub I x' where
  j := s.j
  j_pos := s.j_pos
  b := s.b
  b_ind := s.b_ind
  B := s.B
  B_lat := by rw [h]; exact s.B_lat
  b_mem := s.b_mem
  B_span := s.B_span

theorem det_gram_nonneg (h5 : GramDistortionBound) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (hj : 1 ≤ j)
    (b : Fin j → Fin I.n → I.E) : 0 ≤ (gramV I x v b).det.re := by
  rw [gramV_eq]
  open scoped ComplexOrder in
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1

theorem ht_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ ht I s := by
  unfold ht
  exact div_nonneg (Finset.prod_nonneg fun v _ => det_gram_nonneg I h5 x v s.j_pos s.b) (Nat.cast_nonneg _)

theorem size_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ size I s := by
  unfold Size.size
  exact Real.rpow_nonneg (ht_nonneg I h5 s) _

theorem size_subOfEq_le (h5 : GramDistortionBound) {x x' : I.GA} (hlat : latSet I x' = latSet I x)
    (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (hY : ∀ v u, coordV I x' v u = Y v *ᵥ coordV I x v u) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(Y v *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2) (s : Sub I x) :
    size I (subOfEq I hlat s) ≤ c ^ Fintype.card (InfinitePlace I.F) * size I s := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcm : ∀ v, cmat I x' v s.b = Y v * cmat I x v s.b := by
    intro v
    ext i a
    simp [cmat, hY, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hdet : ∀ v, (gramV I x' v s.b).det.re ≤ c ^ s.j * (gramV I x v s.b).det.re := by
    intro v
    rw [gramV_eq, gramV_eq, hcm]
    refine (h5 I.n s.j (Y v) (cmat I x v s.b) 0 c le_rfl (fun w => ⟨?_, hb v w⟩)).2
    rw [zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hht : ht I (subOfEq I hlat s) ≤ (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s := by
    unfold ht
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc ∏ v, (gramV I x' v (subOfEq I hlat s).b).det.re
        ≤ ∏ v : InfinitePlace I.F, c ^ s.j * (gramV I x v s.b).det.re :=
          Finset.prod_le_prod₀ (fun v _ => det_gram_nonneg I h5 x' v s.j_pos s.b) (fun v _ => hdet v)
      _ = (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ∏ v, (gramV I x v s.b).det.re := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have he : 0 ≤ 1 / (2 * (I.f : ℝ) * (s.j : ℝ)) := by positivity
  have hexp : ((s.j * Fintype.card (InfinitePlace I.F) : ℕ) : ℝ) * (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ (Fintype.card (InfinitePlace I.F) : ℝ) := by
    have hj : (1 : ℝ) ≤ s.j := by exact_mod_cast s.j_pos
    rcases Nat.eq_zero_or_pos I.f with hf | hf
    · simp [hf]
    · have hf' : (1 : ℝ) ≤ I.f := by exact_mod_cast hf
      rw [Nat.cast_mul, mul_one_div, div_le_iff₀ (by positivity)]
      have hP : (0 : ℝ) ≤ Fintype.card (InfinitePlace I.F) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hP (by linarith : (0 : ℝ) ≤ s.j)) (by linarith : (0 : ℝ) ≤ 2 * (I.f : ℝ) - 1)]
  unfold Size.size
  show ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) ≤ _
  calc ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.rpow_le_rpow (ht_nonneg I h5 _) hht he
    _ = ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F)) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) *
          ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.mul_rpow (by positivity) (ht_nonneg I h5 s)
    _ ≤ c ^ Fintype.card (InfinitePlace I.F) * ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ht_nonneg I h5 s) _)
        rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hc0, ← Real.rpow_natCast c]
        exact Real.rpow_le_rpow_of_exponent_le hc hexp

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.EmbeddingLinearIndependent
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix Module
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem complex_embedding_cases (I : AutInst) (σ : I.E →+* ℂ) :
    ∃ v, σ = I.φ v ∨ σ = (starRingEnd ℂ).comp (I.φ v) := by
  classical
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := σ.comp (algebraMap I.F I.E)
  let v : InfinitePlace I.F := InfinitePlace.mk ψ
  have hreal : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal v)
  have hemb : v.embedding = ψ := InfinitePlace.embedding_mk_eq_of_isReal hreal
  have hagree : ∀ x : I.F, σ (algebraMap I.F I.E x) = I.φ v (algebraMap I.F I.E x) := by
    intro x
    rw [I.φ_over, hemb]
    rfl
  have hF : ∀ t : I.E, star t = t → σ t = I.φ v t := by
    intro t ht
    obtain ⟨x, rfl⟩ := (I.cm.fixed t).mp ht
    exact hagree x
  have key : ∀ a : I.E, σ a = I.φ v a ∨ σ a = starRingEnd ℂ (I.φ v a) := by
    intro a
    have ht := hF (a + star a) (by rw [star_add, star_star, add_comm])
    have hm := hF (a * star a) (by rw [star_mul, star_star])
    rw [map_add (f := _), map_add (f := _)] at ht
    rw [map_mul, map_mul] at hm
    have hprod : (σ a - I.φ v a) * (σ a - I.φ v (star a)) = 0 := by
      linear_combination (σ a) * ht - hm
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      rw [sub_eq_zero.mp h]
      exact I.cm.cmUnram.2.1 (I.φ v) a
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon v
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ I.φ v a := by
    by_contra h
    push_neg at h
    exact h1 (RingHom.ext h)
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ starRingEnd ℂ (I.φ v b) := by
    by_contra h
    push_neg at h
    exact h2 (RingHom.ext h)
  have ha' := (key a).resolve_left ha
  have hb' := (key b).resolve_right hb
  rcases key (a + b) with h | h
  · apply ha
    rw [map_add (f := _), map_add (f := _)] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    linear_combination h - ha'

theorem embedding_linear_independent (I : AutInst) :
    LinearIndependent ℝ (fun i : Free.ChooseBasisIndex ℤ (𝓞 I.E) =>
      fun v : InfinitePlace I.F => I.φ v (integralBasis I.E i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = Fintype.card (I.E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e).det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis I.E) e
    rw [h0] at h1
    exact Algebra.discr_not_zero_of_basis ℚ (integralBasis I.E)
      ((map_eq_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).mp (by rw [h1]; ring))
  have hall : ∀ σ : I.E →+* ℂ, ∑ i, (g i : ℂ) * σ (integralBasis I.E i) = 0 := by
    intro σ
    obtain ⟨v, hv | hv⟩ := complex_embedding_cases I σ
    · have := congrFun hg v
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul] at this
      rw [hv]
      exact this
    · have := congrArg (starRingEnd ℂ) (congrFun hg v)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul, map_sum, map_mul,
        Complex.conj_ofReal, map_zero] at this
      rw [hv]
      simp only [RingHom.coe_comp, Function.comp_apply]
      exact this
  have hvec : (fun i => (g i : ℂ)) ᵥ* Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm,
      Matrix.of_apply, Pi.zero_apply]
    exact hall (e j).toRingHom
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  have hi := congrFun h0 i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

theorem card_infinite_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h]
  rfl

theorem card_integral_basis (I : AutInst) : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = 2 * I.f := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank,
    ← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show Module.finrank ℚ I.F * 2 = 2 * Module.finrank ℚ I.F
  ring

theorem finrank_places_complex (I : AutInst) : finrank ℝ (InfinitePlace I.F → ℂ) = 2 * I.f := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_infinite_places, smul_eq_mul]
  ring

def embeddingBasis (I : AutInst) : Basis (Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (InfinitePlace I.F → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (embedding_linear_independent I)
    (by rw [card_integral_basis, finrank_places_complex])

theorem embeddingBasis_apply (I : AutInst) (i : Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    embeddingBasis I i = fun v => I.φ v (integralBasis I.E i) := by
  unfold embeddingBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

def complexToEuclidean {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : Fin 2 × ι ≃ Fin d) :
    (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((Complex.basisOneI.smulTower (Pi.basisFun ℂ ι)).reindex e).equivFun.trans
    (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv.symm


open scoped MatrixOrder in
theorem gram_factor_invertible {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (hC : Function.Injective C.mulVec) :
    ∃ R : Matrix (Fin j) (Fin j) ℂ, Cᴴ * C = Rᴴ * R ∧ R.det ≠ 0 := by
  have hpd : (Cᴴ * C).PosDef := Matrix.PosDef.conjTranspose_mul_self C hC
  have h0 : 0 ≤ Cᴴ * C := Matrix.nonneg_iff_posSemidef.mpr hpd.posSemidef
  refine ⟨CFC.sqrt (Cᴴ * C), ?_, ?_⟩
  · have hsa : (CFC.sqrt (Cᴴ * C))ᴴ = CFC.sqrt (Cᴴ * C) := by
      have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq
      rwa [Matrix.star_eq_conjTranspose] at this
    rw [hsa, CFC.sqrt_mul_sqrt_self _ h0]
  · intro hdet
    have hd : (Cᴴ * C).det ≠ 0 := (hpd.posSemidef.posDef_iff_det_ne_zero).mp hpd
    rw [← CFC.sqrt_mul_sqrt_self _ h0, Matrix.det_mul, hdet, zero_mul] at hd
    exact hd rfl

theorem norm_sq_eq_of_gram_eq {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (R : Matrix (Fin j) (Fin j) ℂ)
    (h : Cᴴ * C = Rᴴ * R) (z : Fin j → ℂ) :
    ∑ i, ‖(C *ᵥ z) i‖ ^ 2 = ∑ k, ‖(R *ᵥ z) k‖ ^ 2 := by
  have key : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin j) ℂ),
      ((∑ i, ‖(M *ᵥ z) i‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ ((Mᴴ * M) *ᵥ z) := by
    intro m _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  apply Complex.ofReal_injective
  rw [key C, key R, h]

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ExistsMulMulConjTransposeEqOne
section
set_option autoImplicit false

noncomputable section

open Matrix

open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

theorem re_star_dotProduct_self {m : ℕ} (z : Fin m → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem star_dotProduct_gram {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (z : Fin k → ℂ) :
    star z ⬝ᵥ ((Aᴴ * A) *ᵥ z) = star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem det_bounds_of_rayleigh {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) (hM : M.IsHermitian) (a b : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2) :
    ∃ μ : ℝ, M.det = μ ∧ a ^ j ≤ μ ∧ μ ≤ b ^ j := by
  have key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b := by
    intro i
    set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def
    have hnorm : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have h1 := (hM.eigenvectorBasis).norm_eq_one i
      rw [EuclideanSpace.norm_eq] at h1
      have h2 := congrArg (fun t : ℝ => t ^ 2) h1
      simp only [one_pow] at h2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    have e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i := by
      rw [hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul,
        ← hv_def, re_star_dotProduct_self, hnorm, mul_one]
    have := h v
    rw [e, hnorm, mul_one, mul_one] at this
    exact this
  refine ⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩
  · rw [hM.det_eq_prod_eigenvalues]
    norm_cast
  · calc a ^ j = ∏ _i : Fin j, a := by simp
      _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => (key i).1)
  · calc ∏ i, hM.eigenvalues i ≤ ∏ _i : Fin j, b :=
          Finset.prod_le_prod₀ (fun i _ => ha.trans (key i).1) (fun i _ => (key i).2)
      _ = b ^ j := by simp

theorem exists_mul_mul_conjTranspose_eq_one {j : ℕ} {G : Matrix (Fin j) (Fin j) ℂ} (hG : G.PosDef) :
    ∃ S : Matrix (Fin j) (Fin j) ℂ, S * G * Sᴴ = 1 := by
  have hH := hG.isHermitian
  set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def
  have hU : star U * U = 1 := by simp [U]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hG.eigenvalues_pos
  refine ⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩
  rw [show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ =
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) *
      (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ by rw [← hspec]]
  rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
  have hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt (hpos i).le
  have h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    rw [show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹
        = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']
  simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at h2
  simpa using h2

theorem det_gram_mul_eq_zero {n j : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ)
    (hd : (Cᴴ * C).det = 0) : ((Y * C)ᴴ * (Y * C)).det = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hCz : C *ᵥ z = 0 := by
    have h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
    rw [star_dotProduct_gram] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨z, hz0, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem t5 : GramDistortionBound := by
  intro n j Y C a b ha hY
  by_cases hd : (Cᴴ * C).det = 0
  · rw [hd, det_gram_mul_eq_zero Y C hd]
    simp
  have hPS : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hPD : (Cᴴ * C).PosDef := hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨S, hS⟩ := exists_mul_mul_conjTranspose_eq_one hPD
  set V := C * Sᴴ with hV_def
  have hV : Vᴴ * V = 1 := by
    rw [hV_def, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]
    exact hS
  set M := (Y * V)ᴴ * (Y * V) with hM_def
  have hMH : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2 := by
      rw [hM_def, star_dotProduct_gram, re_star_dotProduct_self]
    have e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
      rw [← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]
    have := hY (V *ᵥ z)
    rw [Matrix.mulVec_mulVec, e2] at this
    rw [e1]
    exact this
  obtain ⟨μ, hμ, h1, h2⟩ := det_bounds_of_rayleigh M hMH a b ha hray
  have hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ := by
    simp only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1 := by
    rw [← det_mul, ← det_mul, hS, det_one]
  have hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det := by
    calc ((Y * C)ᴴ * (Y * C)).det
        = ((Y * C)ᴴ * (Y * C)).det * (S.det * (Cᴴ * C).det * Sᴴ.det) := by rw [hdet1, mul_one]
      _ = (S.det * ((Y * C)ᴴ * (Y * C)).det * Sᴴ.det) * (Cᴴ * C).det := by ring
      _ = μ * (Cᴴ * C).det := by rw [← det_mul, ← det_mul, ← hMeq, hμ]
  have hG0 := hPS.det_nonneg
  rw [Complex.nonneg_iff] at hG0
  have hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re := by
    rw [hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact ⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Imports
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
end
end

