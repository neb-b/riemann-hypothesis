module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspBasis

open GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem map_cc_mul (A B : Matrix (Fin ρ) (Fin ρ) E) : (A * B).map cc = A.map cc * B.map cc := by
  ext a b
  simp [Matrix.mul_apply, cc_sum', cc_mul']

theorem map_cc_cc (A : Matrix (Fin ρ) (Fin ρ) E) : (A.map cc).map cc = A := by
  ext a b
  simp [cc_cc']

theorem map_cc_one : (1 : Matrix (Fin ρ) (Fin ρ) E).map cc = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h, cc]

theorem isSkew_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsSkew β ↔ β.map cc = -βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsHermE β ↔ β.map cc = βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_conj (P χ : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsHermE χ) :
    FJ.IsHermE (P * χ * (P.map cc)ᵀ) := by
  rw [isHerm_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem isSkew_conj (P β : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsSkew β) :
    FJ.IsSkew (Pᵀ * β * P.map cc) := by
  rw [isSkew_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem comb_change {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (v : Fin ρ → E) :
    ∑ a, v a • e₀ a = ∑ b, (v ᵥ* P) b • e b := by
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem zMatE_change (X : Data E r) {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X e₀ β = FJ.zMatE X e (Pᵀ * β * P.map cc) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [zMatE_mulVec, zMatE_mulVec, comb_change h]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h1 : (fun b => herm X.Gm v (e₀ b)) = P.map cc *ᵥ fun d => herm X.Gm v (e d) := by
    funext b
    rw [h b, herm_comb_r]
    rfl
  change ((β *ᵥ fun b => herm X.Gm v (e₀ b)) ᵥ* P) c =
    ((Pᵀ * β * P.map cc) *ᵥ fun d => herm X.Gm v (e d)) c
  rw [h1, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}

theorem zGam_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {β : Matrix (Fin ρ) (Fin ρ) E}
    (hβ : β ∈ FJ.zGam X cu₀) : Pᵀ * β * P.map cc ∈ FJ.zGam X cu := by
  obtain ⟨hs, γ, hγ, e⟩ := hβ
  exact ⟨isSkew_conj P β hs, γ, hγ, e.trans (zMatE_change X h β)⟩

theorem lattice_le (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) : cu₀.I ≤ cu.I := by
  refine inf_le_inf_left _ fun x hx => ?_
  have hle : Submodule.span E (Set.range cu₀.e) ≤ Submodule.span E (Set.range cu.e) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  exact hle hx

theorem crdI_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {v : Fin ρ → E} (hv : v ∈ FJ.crdI 𝔄 cu₀) :
    v ᵥ* P ∈ FJ.crdI 𝔄 cu := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, e⟩ := hv
    exact Submodule.subset_span ⟨a, ha, x, lattice_le h hx, e.trans (comb_change h v)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Submodule.smul_mem _ _ hx

theorem pair_change (P : Matrix (Fin ρ) (Fin ρ) E) (l x : Fin ρ → E) :
    ∑ i, (P *ᵥ l) i * x i = ∑ i, l i * (x ᵥ* P) i := by
  change (P *ᵥ l) ⬝ᵥ x = l ⬝ᵥ (x ᵥ* P)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem xcFD_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {l : Fin ρ → E} (hl : l ∈ FJ.XcFD 𝔄 cu) :
    P *ᵥ l ∈ FJ.XcFD 𝔄 cu₀ := by
  rw [← SetLike.mem_coe, FJ.xcFD_coe] at hl ⊢
  intro x hx
  rw [pair_change]
  exact hl _ (crdI_change 𝔄 h hx)

theorem dualOE_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {u : Fin ρ → E} (hu : u ∈ FJ.dualOE (FJ.XcFD 𝔄 cu₀)) :
    u ᵥ* P ∈ FJ.dualOE (FJ.XcFD 𝔄 cu) := by
  intro l hl
  have h1 := hu _ (xcFD_change 𝔄 h hl)
  have h2 := pair_change P l u
  simp only [mul_comm (u _), mul_comm ((u ᵥ* P) _)] at h1 ⊢
  rwa [← h2]

theorem prE_change (X : Data E r) (P χ β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.prE X (P * χ * (P.map cc)ᵀ) β = FJ.prE X χ (Pᵀ * β * P.map cc) := by
  have : Matrix.trace ((P * χ * (P.map cc)ᵀ)ᵀ * β) = Matrix.trace (χᵀ * (Pᵀ * β * P.map cc)) := by
    rw [← Matrix.mul_assoc χᵀ, Matrix.trace_mul_comm _ (P.map cc)]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [FJ.prE, this]

theorem form_eq (χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * χ i k * cc (m k) = u ⬝ᵥ (χ *ᵥ fun k => cc (m k)) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_change (P χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) =
      ∑ i, ∑ k, (u ᵥ* P) i * χ i k * cc ((m ᵥ* P) k) := by
  have h1 : (fun k => cc ((m ᵥ* P) k)) = (P.map cc)ᵀ *ᵥ fun k => cc (m k) := by
    funext k
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cc_sum', cc_mul', mul_comm]
  rw [form_eq, form_eq, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem phase_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) :
    ∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X (P * χ * (P.map cc)ᵀ) β = n := fun β hβ => by
  rw [prE_change]
  exact hχ _ (zGam_change h hβ)

theorem integral_change (N : ℕ) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b)
    {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu),
      (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀),
      (N : E) * ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) ∈
        Set.range (algebraMap (𝓞 E) E) := fun u hu m hm => by
  rw [form_change]
  exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)

theorem basis_inv (hP : IsUnit P.det) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) (a : Fin ρ) :
    cu.e a = ∑ b, P⁻¹ a b • cu₀.e b := by
  rw [comb_change h (P⁻¹ a)]
  have h1 : P⁻¹ a ᵥ* P = (1 : Matrix (Fin ρ) (Fin ρ) E) a := by
    rw [← Matrix.nonsing_inv_mul P hP]
    rfl
  rw [h1]
  simp [Matrix.one_apply]

theorem conj_inv (hP : IsUnit P.det) (χ : Matrix (Fin ρ) (Fin ρ) E) :
    P * (P⁻¹ * χ * (P⁻¹.map cc)ᵀ) * (P.map cc)ᵀ = χ := by
  have h1 : (P⁻¹.map cc)ᵀ * (P.map cc)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← map_cc_mul, Matrix.mul_nonsing_inv P hP, map_cc_one,
      Matrix.transpose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

theorem expoMatch_of_basis_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ
  have hQ := basis_inv hP h
  have H' := H _ (isHerm_conj P⁻¹ χ hχ)
  constructor
  · intro hA
    have := integral_change N h (H'.1 (phase_change hQ hA))
    rwa [conj_inv hP] at this
  · intro hB
    have := phase_change h (H'.2 (integral_change N hQ hB))
    rwa [conj_inv hP] at this

end GlobalTheory.CuspBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem uMat_conj_eq_diagonal {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ d : Fin n → ℝ, (∀ k : Fin n, 0 < sgn p0 k * d k) ∧
      (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) = Matrix.diagonal fun a => ((d a : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := hs ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  refine ⟨fun k => (B k k).re, fun k => ?_, ?_⟩
  · have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
      rw [hprod k.succ, hprod k.castSucc]
      exact prod_castLE_succ (f := fun k => B k k) k.isLt
    have h1 := hs k.succ
    have h0 := hs k.castSucc
    rw [hsucc, Complex.mul_re, hre, mul_zero, sub_zero, Fin.val_succ, psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (pos_iff_pos_of_mul_pos (a := psgn p0 k * (lminor A k.castSucc).re) ?_).1 h0
    exact h1.trans_eq (by ring)
  · rw [hdiag]
    congr 1
    funext k
    apply Complex.ext <;> simp [hre]

theorem exists_upper_conj_eq_signature {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, b.det ≠ 0 ∧ b.BlockTriangular id ∧
      bᵀ * A * b.map (starRingEnd ℂ)
        = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨d, hd, hA'⟩ := uMat_conj_eq_diagonal p0 A hA hs
  refine ⟨uMat A * Matrix.diagonal fun k : Fin n => (((√(sgn p0 k * d k))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_uMat, one_mul, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hd k)).ne')
  · exact (uMat_upper A).mul (Matrix.blockTriangular_diagonal _)
  · rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.diagonal_transpose,
      Matrix.diagonal_map (map_zero _), ← Matrix.mul_assoc, Matrix.mul_assoc _ (uMat A)ᵀ,
      Matrix.mul_assoc _ ((uMat A)ᵀ * A), hA',
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    have h1 := Real.mul_self_sqrt (hd k).le
    have h2 := (Real.sqrt_pos.2 (hd k)).ne'
    set s := √(sgn p0 k * d k)
    have h3 : d k = sgn p0 k * (s * s) := by
      rw [h1]
      rcases sgn_sq p0 k with h | h <;> simp [h]
    rw [h3]
    field_simp

theorem frame_mul_triangular_orthonormal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ x₀ = rmul x b) ∧ ∀ (τ : E →+* ℂ) (x₀ x₁ : Matrix (Fin r) (Fin r) ℂ), gram τ Gm x₀ = (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → gram τ Gm x₁ = gram τ Gm x₀ → ∃ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ ∧ x₁ = u * x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx => ?_, fun τ x₀ x₁ h0 h1 => ?_⟩
  · choose b hb using fun τ : Ψ => exists_upper_conj_eq_signature p0 (gram τ.1 Gm (mat x τ))
      (gram_isHermitian τ.1 hG _) (hx τ).2
    refine ⟨rmul x fun τ => b τ, fun τ => b τ,
      fun τ => ⟨(hb τ).1, fun a c hca => (hb τ).2.1 hca⟩, fun τ => ?_, rfl⟩
    show gram τ.1 Gm (mat x τ * b τ) = _
    rw [FrameDegreeData.gram_mul]
    exact (hb τ).2.2
  · have hdet : IsUnit x₀.det := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have h2 := congrArg Matrix.det h0
      rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul,
        zero_mul, Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
      rcases sgn_sq p0 k with h' | h' <;> simp [h']
    refine ⟨x₁ * x₀⁻¹, ?_, (Matrix.nonsing_inv_mul_cancel_right _ _ hdet).symm⟩
    rw [← FrameDegreeData.gram_eq, FrameDegreeData.gram_mul, h1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hdet,
      FrameDegreeData.gram_eq]
    simp

end GlobalTheory.UnitFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerLin

theorem surj_fst (S : Type) [CommRing S] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hr := range_comap_of_surjective _ _ hs
  have hp : (show PrimeSpectrum (DualNumber S) from p) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom S S S).toRingHom : Set (DualNumber S)) := by
    intro x hx
    have hx0 : x.fst = 0 := hx
    have : x * x = 0 := by
      ext <;> simp [hx0]
    have hP := (show PrimeSpectrum (DualNumber S) from p).isPrime
    have h0 : x * x ∈ (show PrimeSpectrum (DualNumber S) from p).asIdeal := by
      rw [this]; exact Ideal.zero_mem _
    exact (hP.mem_or_mem h0).elim id id
  rw [← hr] at hp
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, hq⟩

theorem le_of_fst_eq {S : Type} [CommRing S] {X : Scheme.{0}} {v v' : Sp (DualNumber S) ⟶ X}
    (hh : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v')
    {U : X.Opens} (h : ⊤ ≤ v' ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := surj_fst S p
  have h1 := h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) q))
  change v' _ ∈ U at h1
  change v _ ∈ U
  rw [← Scheme.Hom.comp_apply] at h1 ⊢
  rw [hh]; exact h1

theorem isCombAt_iff_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (w : Fin m → (Fin g → ℂ)), (∀ i, IsDerivAt0 (fun z => (F.ex k P z).left) (w i) (v i)) → ∀ (a : Fin m → ℂ) (v' : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsCombAt (F.u k P) v a v' ↔ IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP m v w hvw a
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ' g ty F k P hP
  obtain ⟨N, _, _, ν, ρ, -, hr, hc, -⟩ := _root_.GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo ℂ (F.u k P)
  have htan : ∀ i, IsTanAt (F.u k P) (v i) := fun i => h1 _ _ (hvw i)
  choose b hb using fun i => (hr (v i)).1 (htan i)
  have hv : v = fun i => ν (b i) := funext fun i => (hb i).symm
  have fwd : ∀ v', IsCombAt (F.u k P) v a v' →
      IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
    intro v' hv'
    have ht' : IsTanAt (F.u k P) v' := by
      rw [hv, hc] at hv'
      exact (hr v').2 ⟨_, hv'.symm⟩
    obtain ⟨v0, hv0, -⟩ := h2 0
    refine ⟨ht'.2.trans ((h1 _ _ hv0).2.symm.trans hv0.1), fun U h f => ?_⟩
    have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => le_of_fst_eq ((htan i).2.trans ht'.2.symm) h
    refine (_root_.GlobalTheory.TanDeriv.deriv_comb E H Dw l Xo ℂ (F.u k P) m v a v' htan hv' U h hU f).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (a i * ·) ((hvw i).2 U (hU i) f)
  intro v'
  refine ⟨fwd v', fun hd => ?_⟩
  have hex : IsCombAt (F.u k P) v a (ν (∑ i, a i • b i)) := by
    rw [hv, hc]
  rw [(h2 _).unique hd (fwd _ hex)]
  exact hex

end GlobalTheory.DerLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ObjRebase

def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)

theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _

theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm

def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}

end GlobalTheory.ObjRebase
end
end

