module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

noncomputable section

namespace GlobalTheory.RealPar.DerivedAdjoint

variable {p q : ℕ}

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal_apply, eq_comm] <;> split_ifs <;> simp

theorem Jm_mul_Jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp

theorem Jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_diag, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  rcases i with i | i <;> simp

theorem adjZ_adjZ (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  unfold adjZ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  simp only [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]

theorem adjZ_add (X Y : Mat p q) : adjZ (X + Y) = adjZ X + adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjZ_sub (X Y : Mat p q) : adjZ (X - Y) = adjZ X - adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem adjZ_smul (c : ℂ) (X : Mat p q) : adjZ (c • X) = star c • adjZ X := by
  unfold adjZ
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_upq_of_adjZ {X : Mat p q} (h : adjZ X = -X) : X ∈ upq p q := by
  unfold upq
  show Xᴴ * Jm p q + Jm p q * X = 0
  have key : Jm p q * adjZ X = Xᴴ * Jm p q := by
    unfold adjZ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  rw [← key, h, Matrix.mul_neg, neg_add_cancel]

theorem inner_map (T : GrpData p q) (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  exact (LinearIsometry.mk (πU.π g).toLinearMap (πU.isom g)).inner_map_map x y

theorem derived_adjoint : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) := by
  intro p q T πU M j hd

  have skew : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = - inner ℂ (j x) (j (M.act Y y)) := by
    intro Y hY x y
    have h1 := (hd Y hY x).inner ℂ (hd Y hY y)
    have hconst : (fun t : ℝ => inner ℂ (πU.π (T.expt (t • Y)) (j x)) (πU.π (T.expt (t • Y)) (j y)))
        = fun _ => inner ℂ (j x) (j y) := by
      funext t
      exact inner_map T πU _ (j x) (j y)
    rw [hconst] at h1
    have h0 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (j x) (j y)))
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0

  have adj_of_mem : ∀ Y ∈ upq p q, adjZ Y = -Y := by
    intro Y hY
    have hY' : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    have e : Yᴴ * Jm p q = -(Jm p q * Y) := eq_neg_of_add_eq_zero_left hY'
    unfold adjZ
    rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have base : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Y) y)) := by
    intro Y hY x y
    rw [adj_of_mem Y hY, map_neg, LinearMap.neg_apply, map_neg, inner_neg_right]
    exact skew Y hY x y

  intro Z x y
  obtain ⟨A, hA⟩ : ∃ A : Mat p q, A = (1 / 2 : ℂ) • (Z - adjZ Z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Mat p q, B = (-Complex.I / 2) • (Z + adjZ Z) := ⟨_, rfl⟩
  have hc : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by
    apply Complex.ext <;> simp
  have hZ : Z = A + Complex.I • B := by
    rw [hA, hB, smul_smul, hc]
    module
  have hAm : A ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hA, adjZ_smul, adjZ_sub, adjZ_adjZ, hs1]
    module
  have hBm : B ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hB, adjZ_smul, adjZ_add, adjZ_adjZ, hs2]
    module
  rw [hZ]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adjZ_add, adjZ_smul, base A hAm,
    base B hBm, starRingEnd_apply]

end GlobalTheory.RealPar.DerivedAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestType
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.LowestType

theorem two_le_of_not_sameBlock {p q : ℕ} {a b : Ix p q} (h : ¬ sameBlock a b) : 2 ≤ p + q := by
  unfold sameBlock at h
  rcases a with i | i <;> rcases b with j | j
  · exact (h trivial).elim
  · have hi := i.pos
    have hj := j.pos
    omega
  · have hi := i.pos
    have hj := j.pos
    omega
  · exact (h trivial).elim

theorem gapGt_of_cube {p q : ℕ} {lam : Ix p q → ℚ} (hg : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    {h : ℝ} (hh : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) → h ≤ ((p + q : ℕ) : ℝ) ^ 3) : GapGt lam h := by
  unfold GapGt at hg ⊢
  intro a b hab
  have h2 : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast two_le_of_not_sameBlock hab
  exact lt_of_le_of_lt (hh h2) (hg a b hab)

private lemma cube_div_add_one_le_cube_and_sub_one_le {n : ℝ} (h2 : 2 ≤ n) : n ^ 3 / 24 + 1 ≤ n ^ 3 ∧ n - 1 ≤ n ^ 3 := by

  have hp : 0 ≤ n * (n - 1) * (n + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have e : n * (n - 1) * (n + 1) = n ^ 3 - n := by ring
  constructor <;> linarith

theorem embeds_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  intro hQ7 hQ8 p q lam hlam hgap A B u v hu hv hcu hcv hirr

  have g1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).1)
  have g2 : GapGt lam (((p + q : ℕ) : ℝ) - 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).2)
  obtain ⟨⟨e, he, hcomm, heu, -⟩, -⟩ :=
    _root_.GlobalTheory.LowGen.gen_iso_of_lowest_type hQ7 hQ8 p q lam hlam g1 g2 A B u v hu hv hcu hcv hirr
  exact ⟨e, he, heu, hcomm⟩

end GlobalTheory.LowestType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfPositiveCoeffOrthogonalEmbeddings
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.PosTrace

section Abstract

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem sum_inner_nonneg {ι : Type} [Fintype ι] (e : OrthonormalBasis ι ℂ E) (A B : E →ₗ[ℂ] E)
    (hA : ∀ w, (0 : ℂ) ≤ inner ℂ w (A w)) (hB : ∀ w, (0 : ℂ) ≤ inner ℂ w (B w)) :
    (0 : ℂ) ≤ ∑ j, inner ℂ (B (e j)) (A (e j)) := by
  have sym : ∀ T : E →ₗ[ℂ] E, (∀ w, (0 : ℂ) ≤ inner ℂ w (T w)) → T.IsSymmetric := by
    intro T hT
    refine (LinearMap.isSymmetric_iff_inner_map_self_real T).2 fun v => ?_
    have hr : (starRingEnd ℂ) (inner ℂ v (T v)) = inner ℂ v (T v) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 (hT v)).2.symm
    rw [inner_conj_symm v (T v), ← inner_conj_symm (T v) v, hr]
  have sA := sym A hA
  have sB := sym B hB
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ E = n := ⟨_, rfl⟩
  obtain ⟨f, μ, hfA⟩ : ∃ (f : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℝ),
      ∀ k, A (f k) = (μ k : ℂ) • f k := ⟨_, _, sA.apply_eigenvectorBasis hn⟩
  have hμ : ∀ k, (0 : ℂ) ≤ (μ k : ℂ) := by
    intro k
    have h := hA (f k)
    rw [hfA, inner_smul_right, inner_self_eq_norm_sq_to_K, f.orthonormal.1 k] at h
    simpa using h
  have step : ∀ j, inner ℂ (B (e j)) (A (e j)) =
      ∑ k, (μ k : ℂ) * (inner ℂ (f k) (e j) * inner ℂ (e j) (B (f k))) := by
    intro j
    rw [← f.sum_inner_mul_inner (B (e j)) (A (e j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sA (f k) (e j), hfA, inner_smul_left, Complex.conj_ofReal, sB (e j) (f k)]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_comm]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [← Finset.mul_sum, e.sum_inner_mul_inner]
  exact mul_nonneg (hμ k) (hB (f k))

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

theorem exists_adj (J : E →ₗ[ℂ] H₁) : ∃ D : H₁ →ₗ[ℂ] E, ∀ x a, inner ℂ x (D a) = inner ℂ (J x) a := by
  refine ⟨(ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap J)).toLinearMap, fun x a => ?_⟩
  exact ContinuousLinearMap.adjoint_inner_right _ x a

omit [FiniteDimensional ℂ E] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem sum_eq_adj {ι : Type} [Fintype ι] (e : OrthonormalBasis ι ℂ E) (J₁ : E →ₗ[ℂ] H₁) (J₂ : E →ₗ[ℂ] H₂)
    (D₁ : H₁ →ₗ[ℂ] E) (D₂ : H₂ →ₗ[ℂ] E) (h₁ : ∀ x a, inner ℂ x (D₁ a) = inner ℂ (J₁ x) a)
    (h₂ : ∀ x a, inner ℂ x (D₂ a) = inner ℂ (J₂ x) a) (a : H₁) (b : H₂) :
    ∑ i, inner ℂ (J₁ (e i)) a * star (inner ℂ (J₂ (e i)) b) = inner ℂ (D₂ b) (D₁ a) := by
  rw [← e.sum_inner_mul_inner (D₂ b) (D₁ a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have k1 := h₁ (e i) a
  have k2 := h₂ (e i) b
  rw [← k1, ← k2, ← inner_conj_symm (e i) (D₂ b), Complex.star_def, Complex.conj_conj, mul_comm]

end Abstract

theorem inner_pi {p q : ℕ} {T : GrpData p q} (π : URep T) (g : T.G) (a b : π.H) :
    inner ℂ (π.π g a) (π.π g b) = inner ℂ a b := (LinearMap.norm_map_iff_inner_map_map (π.π g)).1 (π.6 g) a b

theorem isometric_case (p q : ℕ) (T : GrpData p q)
    (hG : ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) (π₁ π₂ : URep T)
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗᵢ[ℂ] π₂.H)
    (hK : ∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w')
    (h₁ : ∀ Y ∈ pR p q, ∀ w, (0 : ℂ) ≤ inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w)))
    (h₂ : ∀ Y ∈ pR p q, ∀ w, (0 : ℂ) ≤ inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w)))
    (hI : ∀ x y u w : E, Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) *
        star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧
      ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) :
    j₁ = 0 := by
  obtain ⟨D₁, hD₁⟩ := exists_adj j₁
  obtain ⟨D₂, hD₂⟩ := exists_adj j₂.toLinearMap
  have hD₂' : ∀ x a, inner ℂ x (D₂ a) = inner ℂ (j₂ x) a := hD₂
  let ob := stdOrthonormalBasis ℂ E
  have hsum : ∀ (e : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (a : π₁.H) (b : π₂.H),
      ∑ i, inner ℂ (j₁ (e i)) a * star (inner ℂ (j₂ (e i)) b) = inner ℂ (D₂ b) (D₁ a) :=
    fun e a b => sum_eq_adj e j₁ j₂.toLinearMap D₁ D₂ hD₁ hD₂ a b
  have hmul₁ : ∀ g g' x, π₁.π (g * g') x = π₁.π g (π₁.π g' x) := fun g g' x => by
    rw [map_mul]; rfl
  have hmul₂ : ∀ g g' x, π₂.π (g * g') x = π₂.π g (π₂.π g' x) := fun g g' x => by
    rw [map_mul]; rfl
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : T.G → ℂ, ∀ g, Φ g =
      ∑ l, inner ℂ (D₂ (π₂.π g (j₂ (ob l)))) (D₁ (π₁.π g (j₁ (ob l)))) := ⟨_, fun _ => rfl⟩
  have hΦ2 : ∀ g, Φ g = ∑ l, ∑ i, inner ℂ (j₁ (ob i)) (π₁.π g (j₁ (ob l))) *
      star (inner ℂ (j₂ (ob i)) (π₂.π g (j₂ (ob l)))) := fun g => by
    rw [hΦ]
    exact Finset.sum_congr rfl fun l _ => (hsum ob _ _).symm

  have hfb : ∀ k ∈ T.Kset, ∃ f : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∀ i, π₁.π k (j₁ (f i)) = j₁ (ob i) ∧ π₂.π k (j₂ (f i)) = j₂ (ob i) := by
    intro k hk
    choose c hc using hK k hk
    have hc2 : ∀ w, j₂ (c w) = π₂.π k (j₂ w) := fun w => (hc w).2.symm
    let cl : E →ₗ[ℂ] E :=
      { toFun := c
        map_add' := fun x y => j₂.injective (by simp only [map_add (f := _), hc2])
        map_smul' := fun a x => j₂.injective (by simp only [map_smul, hc2, RingHom.id_apply]) }
    have hcn : ∀ w, ‖cl w‖ = ‖w‖ := fun w => by
      have e1 := j₂.norm_map (c w)
      have e2 := π₂.6 k (j₂ w)
      have e3 := j₂.norm_map w
      rw [hc2] at e1
      exact e1.symm.trans (e2.trans e3)
    let ci : E →ₗᵢ[ℂ] E := ⟨cl, hcn⟩
    have hs : Function.Surjective cl := (LinearMap.injective_iff_surjective (f := cl)).1 ci.injective
    let κ := LinearIsometryEquiv.ofSurjective ci hs
    refine ⟨ob.map κ.symm, fun i => ?_⟩
    have hk : c (κ.symm (ob i)) = ob i := κ.apply_symm_apply (ob i)
    rw [OrthonormalBasis.map_apply, (hc _).1, (hc _).2, hk]
    exact ⟨rfl, rfl⟩
  have hkh : ∀ k ∈ T.Kset, ∀ h, Φ (k * h) = Φ h := by
    intro k hk h
    obtain ⟨f, hf⟩ := hfb k hk
    rw [hΦ, hΦ]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hsum ob, ← hsum f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hf i).1, ← (hf i).2, hmul₁, hmul₂, inner_pi, inner_pi]
  have hpos : ∀ Y ∈ pR p q, 0 ≤ Φ (T.expt Y) := by
    intro Y hY
    rw [hΦ]
    refine sum_inner_nonneg ob (D₁ ∘ₗ (π₁.π (T.expt Y)).toLinearMap ∘ₗ j₁)
      (D₂ ∘ₗ (π₂.π (T.expt Y)).toLinearMap ∘ₗ j₂.toLinearMap) (fun w => ?_) (fun w => ?_)
    · show (0 : ℂ) ≤ inner ℂ w (D₁ (π₁.π (T.expt Y) (j₁ w)))
      rw [hD₁]
      exact h₁ Y hY w
    · show (0 : ℂ) ≤ inner ℂ w (D₂ (π₂.π (T.expt Y) (j₂ w)))
      rw [hD₂']
      exact h₂ Y hY w
  have hnn : ∀ g, 0 ≤ Φ g := by
    intro g
    obtain ⟨k, hk, Y, hY, rfl⟩ := hG g
    rw [hkh k hk]
    exact hpos Y hY
  have hcont : Continuous Φ := by
    rw [show Φ = _ from funext hΦ2]
    refine continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun i _ => ?_
    exact (continuous_const.inner (π₁.7 _)).mul (continuous_const.inner (π₂.7 _)).star
  have hΦi : MeasureTheory.Integrable Φ T.haar := by
    rw [show Φ = _ from funext hΦ2]
    exact MeasureTheory.integrable_finsetSum _ fun l _ =>
      MeasureTheory.integrable_finsetSum _ fun i _ => (hI _ _ _ _).1
  have hint : ∫ g, Φ g ∂T.haar = 0 := by
    simp_rw [hΦ2]
    rw [MeasureTheory.integral_finsetSum _ fun l _ =>
      MeasureTheory.integrable_finsetSum _ fun i _ => (hI _ _ _ _).1]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [MeasureTheory.integral_finsetSum _ fun i _ => (hI _ _ _ _).1]
    exact Finset.sum_eq_zero fun i _ => (hI _ _ _ _).2
  have hz : (fun g => RCLike.re (Φ g)) = 0 := by
    have h0 : ∫ g, RCLike.re (Φ g) ∂T.haar = 0 := by
      rw [integral_re hΦi, hint]
      simp
    have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun g => (RCLike.nonneg_iff.1 (hnn g)).1) hΦi.re).1 h0
    exact (Continuous.ae_eq_iff_eq T.haar (RCLike.continuous_re.comp hcont) continuous_zero).1 hae
  have h1 : RCLike.re (Φ 1) = 0 := congrFun hz 1
  have hD₂j : ∀ y, D₂ (j₂ y) = y := fun y =>
    ext_inner_left ℂ fun v => by rw [hD₂', j₂.inner_map_map]
  have hΦ1 : Φ 1 = ∑ l, inner ℂ (j₁ (ob l)) (j₁ (ob l)) := by
    rw [hΦ]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_one, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply, hD₂j, hD₁]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ1, map_sum] at h1
  simp only [inner_self_eq_norm_sq] at h1
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖j₁ (ob l)‖)).1 h1
  exact ob.toBasis.ext fun l => by simpa using hz' l (Finset.mem_univ l)

theorem eq_zero_of_pos_of_orth : ∀ (p q : ℕ) (T : GrpData p q), (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), Function.Injective j₂ → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).re) → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).re) → (∀ x y u w : E, MeasureTheory.Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧ ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) → j₁ = 0 := by
  intro p q T hG π₁ π₂ E _ _ _ j₁ j₂ hinj hK h₁ h₂ hI
  let φ : E ≃ₗ[ℂ] LinearMap.range j₂ := LinearEquiv.ofInjective j₂ hinj
  let j₁' : LinearMap.range j₂ →ₗ[ℂ] π₁.H := j₁ ∘ₗ φ.symm.toLinearMap
  have hj : ∀ w, j₁' (φ w) = j₁ w := fun w => by
    show j₁ (φ.symm (φ w)) = j₁ w
    rw [φ.symm_apply_apply]
  have key := isometric_case p q T hG π₁ π₂ (LinearMap.range j₂) j₁' (LinearMap.range j₂).subtypeₗᵢ
    ?_ ?_ ?_ ?_
  · exact LinearMap.ext fun w => by simpa [key] using (hj w).symm
  · intro k hk r
    obtain ⟨w, rfl⟩ := φ.surjective r
    obtain ⟨w', e1, e2⟩ := hK k hk w
    refine ⟨φ w', ?_, ?_⟩
    · rw [hj, hj, e1]
    · exact e2
  · intro Y hY r
    obtain ⟨w, rfl⟩ := φ.surjective r
    rw [hj]
    exact Complex.nonneg_iff.2 ⟨(h₁ Y hY w).2, (h₁ Y hY w).1.symm⟩
  · intro Y hY r
    obtain ⟨w, rfl⟩ := φ.surjective r
    show (0 : ℂ) ≤ inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))
    exact Complex.nonneg_iff.2 ⟨(h₂ Y hY w).2, (h₂ Y hY w).1.symm⟩
  · intro x y u w
    obtain ⟨a, rfl⟩ := φ.surjective x
    obtain ⟨b, rfl⟩ := φ.surjective y
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨d, rfl⟩ := φ.surjective w
    simp only [hj]
    exact hI a b c d

end GlobalTheory.PosTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpacStatement
section
open Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ), (∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) = rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v)) → ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  first | exact @GlobalTheory.Branching.Family.equivariant_gl_of_unitary | exact GlobalTheory.Branching.Family.equivariant_gl_of_unitary | (intros; apply GlobalTheory.Branching.Family.equivariant_gl_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelDualPairCasimirApply
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem fock_casimir_apply (p q r s : ℕ) (P : Pol p q r s) :
    casimir (fockAct2 p q r s) P = casimir (fockAct1 p q r s) P -
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • P := by
  have h := LinearMap.congr_fun (_root_.GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 p q r s) P
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  rw [← h, sub_sub_cancel]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypesJointHarmonicShape
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem lowestKTypes_jointShape : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ IsParam (lamM' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) := by
  intro t al be ga de h
  obtain ⟨hA, hpA, hpA', -, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de h
  obtain ⟨hM, hpM', -, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de h
  exact ⟨⟨hpA, hpA', hpM'⟩, hA, hM⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.InducedPBW

def SymbolCongr {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ (l : List (Mat p q)) (v : V),
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) -
      (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈ indFlt act l.length

end GlobalTheory.InducedPBW
end
end

