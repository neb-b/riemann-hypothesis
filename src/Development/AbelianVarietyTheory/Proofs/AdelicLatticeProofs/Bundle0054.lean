module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicOfIndefinite
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.UTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.herm_diagonal_self {r : ℕ} (g u : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) u u = ∑ i, u i * g i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (u i) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, diagonal_apply, mul_ite, ite_mul]


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.exists_isotropic_diagonal {n : ℕ} (hn : 3 ≤ n) {g : Fin n → E}
    (hg : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ ∃ j, (τ (g j)).re < 0) :
    ∃ z : Fin n → E, z ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) z z = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hiso : _root_.GlobalTheory.LocalQuad.HermClass.Isotropy := fun F _ _ ι _ a h5 ha hsgn =>
    _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt F a h5 ha hsgn
  have hsign : ∀ τ : E →+* ℂ, ∃ k : Fin m, 0 < (τ (g k.succ)).re ↔ 0 < (τ (-g 0)).re := by
    intro τ
    obtain ⟨⟨i, hi⟩, j, hj⟩ := hs τ
    have h0 : (τ (g 0)).re ≠ 0 := _root_.GlobalTheory.LocalQuad.HermClass.re_ne_zero τ (hg 0) (hg0 0)
    rw [map_neg, Complex.neg_re]
    by_cases hpos : 0 < (τ (g 0)).re
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact absurd hj (not_lt.2 hpos.le)
      · exact ⟨k, iff_of_false (not_lt.2 hj.le) (by linarith)⟩
    · have hneg : (τ (g 0)).re < 0 := lt_of_le_of_ne (not_lt.1 hpos) h0
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · exact absurd hi hpos
      · exact ⟨k, iff_of_true hi (by linarith)⟩
  have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (-g 0) = -g 0 := by
    show IsCMField.complexConj E (-g 0) = -g 0
    rw [map_neg]
    exact congrArg Neg.neg (hg 0)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_represent hiso (r := m) (by omega)
    (g := fun k => g k.succ) (fun k => hg _) (fun k => hg0 _) hc (neg_ne_zero.2 (hg0 0)) hsign
  refine ⟨Fin.cons 1 w, fun h => one_ne_zero (α := E) (by simpa using congr_fun h 0), ?_⟩
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self] at hw ⊢
  rw [Fin.sum_univ_succ]
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, h1, mul_one]
  rw [hw]
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_eq_dotProduct_mulVec_cc {r : ℕ} (H : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm H x y = x ⬝ᵥ (H *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_mulVec_mulVec' {r : ℕ} (G P : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ u) (P *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) u v := by
  have hc : (fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((P *ᵥ v) b)) = P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (v b) := by
    ext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul]
  rw [herm_eq_dotProduct_mulVec_cc, herm_eq_dotProduct_mulVec_cc, hc, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec u, vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma re_mul_cc_eq_normSq_mul_re (τ : E →+* ℂ) (y d : E) :
    (τ (y * d * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y)).re = Complex.normSq (τ y) * (τ d).re := by
  rw [map_mul, map_mul, _root_.GlobalTheory.Published.embedding_cc, mul_right_comm, Complex.mul_conj,
    Complex.re_ofReal_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_pos_of_herm_diagonal_re_pos {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : 0 < (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re) : ∃ i, 0 < (τ (d i)).re := by
  by_contra h
  push_neg at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonpos fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_neg_of_herm_diagonal_re_neg {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re < 0) : ∃ i, (τ (d i)).re < 0 := by
  by_contra h
  push_neg at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonneg fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (h i)


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.exists_isotropic_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), (∀ a, σ a = IsCMField.complexConj E a) → _root_.GlobalTheory.UTrans.IsHerm σ G → 3 ≤ n → (∀ τ : E →+* ℂ, (∃ x, 0 < (τ (_root_.GlobalTheory.UTrans.hf σ G x x)).re) ∧ ∃ y, (τ (_root_.GlobalTheory.UTrans.hf σ G y y)).re < 0) → ∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf σ G z z = 0 := by
  intro E _ _ _ n σ G hσ hG hn hs
  have hf : ∀ x y, _root_.GlobalTheory.UTrans.hf σ G x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro x y
    simp only [_root_.GlobalTheory.UTrans.hf, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hσ]
    rfl
  have hGc : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hG.herm a b, hσ]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := _root_.GlobalTheory.HermDiag.exists_congr_diagonal_herm hGc
  have hPinv : ∀ x, P *ᵥ (P⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), one_mulVec]
  have hform : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ y) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y := fun y => by
    rw [herm_mulVec_mulVec', hPd]
  suffices ∃ y, y ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y = 0 by
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨P *ᵥ y, fun h => hy (eq_zero_of_mulVec_eq_zero hP h), by rw [hf, hform, hy0]⟩
  by_cases hd0 : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hd0
    refine ⟨Pi.single i 1, fun h => one_ne_zero (α := E) (by simpa using congr_fun h i), ?_⟩
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  · push_neg at hd0
    refine _root_.GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hd0 fun τ => ?_
    obtain ⟨⟨x, hx⟩, y, hy⟩ := hs τ
    rw [hf, ← hPinv x, hform] at hx
    rw [hf, ← hPinv y, hform] at hy
    exact ⟨exists_re_pos_of_herm_diagonal_re_pos τ d _ hx, exists_re_neg_of_herm_diagonal_re_neg τ d _ hy⟩

end GlobalTheory.UTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.landherr_and_landherrSt :
    _root_.GlobalTheory.Published.Landherr ∧ _root_.GlobalTheory.Published.LandherrSt :=
  ⟨_root_.GlobalTheory.LocalQuad.landherr_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt,
    _root_.GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt⟩

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankTwo
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_basis_one_sqrt_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E]
    [Algebra F E] (h : Module.finrank F E = 2) :
    ∃ (e : Module.Basis (Fin 2) F E) (δ : F), δ ≠ 0 ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap F E δ := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hr : 1 < Module.rank F E := by
    rw [← Module.finrank_eq_rank, h]; norm_num
  obtain ⟨s, hs⟩ := exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = s := by simp [b]
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by
    refine ⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)] := by
    rw [LinearIndependent.pair_iff] at hs ⊢
    intro x y hxy
    have := hs (x - y * (q / 2)) y (by
      rw [← hxy]; simp only [Algebra.smul_def, map_sub, map_mul]; ring)
    obtain ⟨h1, rfl⟩ := this
    exact ⟨by simpa using h1, rfl⟩
  have hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2))
      = algebraMap F E (p + (q / 2) ^ 2) := by
    have hq : algebraMap F E q = 2 * algebraMap F E (q / 2) := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul]; congr 1; ring
    rw [map_add (f := _), map_pow]
    rw [hq] at hpq
    linear_combination hpq
  refine ⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_,
    by simp, by simpa using hsq⟩
  intro h0
  rw [h0, map_zero, mul_self_eq_zero] at hsq
  exact ht.ne_zero 1 (by simpa using hsq)

theorem TNorm.exists_sq_sub {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : Module.Basis (Fin 2) F E) (h0 : e 0 = 1) {δ : F} (h1 : e 1 * e 1 = algebraMap F E δ)
    (L : Type) [Field L] [Algebra F L] {x : F} (h : TNorm F E L x) :
    ∃ a b : L, algebraMap F L x = a ^ 2 - algebraMap F L δ * b ^ 2 := by
  obtain ⟨z, hz⟩ := h
  let e' := Algebra.TensorProduct.basis L e
  refine ⟨e'.repr z 0, e'.repr z 1, ?_⟩
  rw [← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e'
    (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ)
    (by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' δ).symm)]
  congr 1
  conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]

theorem np_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  intro F E _ _ _ _ _ h x hx hloc
  obtain ⟨e, δ, hδ, h0, h1⟩ := exists_basis_one_sqrt_of_finrank_two h
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F δ x hδ hx
    (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra))
    (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))
  exact ⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegree
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tNorm_baseChange_of_ringHom (F F' E E' K K' : Type) [Field F] [Field F'] [Field E]
    [Field E'] [Algebra F F'] [Algebra F E] [Algebra F' E'] [Algebra E E'] [Algebra F E']
    [IsScalarTower F F' E'] [IsScalarTower F E E'] [Algebra.IsPushout F F' E E']
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field K'] [Algebra F' K'] (φ : K →+* K')
    (hφ : ∀ x : F, φ (algebraMap F K x) = algebraMap F' K' (algebraMap F F' x)) (x : F)
    (h : TNorm F E K x) : TNorm F' E' K' (algebraMap F F' x) := by
  letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra
  haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y₀, hy₀⟩ := h
  let ψ : K →ₐ[F] K' := { φ with commutes' := hφ }
  let y : K' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀
  have hy : Algebra.norm K' y = algebraMap F K' x := by
    rw [tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]
  let e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E :=
    Algebra.TensorProduct.cancelBaseChange F F' K' K' E
  let e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E' :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')
  refine ⟨(e₁.symm.trans e₂) y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]

theorem exists_norm_eq_of_coprime_pow {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {m n : ℕ} (hc : Nat.Coprime m n) {x : F} (hx : x ≠ 0) {a b : E}
    (ha : Algebra.norm F a = x ^ m) (hb : Algebra.norm F b = x ^ n) :
    ∃ y : E, Algebra.norm F y = x := by
  refine ⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩
  rw [map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]
  simp

theorem np_of_odd_prime_degree : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E],
    p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ hp h2 hd x hx hl
  obtain ⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩ :=
    exists_pushout_primitiveRoot p F E hp h2 hd
  have hl' : LocNorm F' E' (algebraMap F F' x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w
      exact tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)
    · exfalso
      let ψ : F' →+* ℂ := Complex.ofRealHom.comp (algebraMap F' ℝ)
      apply IsTotallyComplex.complexEmbedding_not_isReal ψ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      simp [ψ]
  obtain ⟨b, hb⟩ :=
    np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'
  have h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F' := by
    rw [Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]
  have h3 : Algebra.norm F (algebraMap F E x) = x ^ p := by
    rw [Algebra.norm_algebraMap, hd]
  exact exists_norm_eq_of_coprime_pow hc hx h1 h3

end GlobalTheory.CNorm
end

