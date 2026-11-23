module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UbasisAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscreteLatticeMinimum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BfSubRight
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Bf (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) : ℂ := ∑ a, ∑ b, v a * Gp X Z τ a b * conj (w b)

def Nv (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) : ℂ :=
  v (nI X m) + ∑ c, Z τ m c * v (Fin.castLE X.p0_le c)

def Pv (v : Fin r → ℂ) (a : Fin X.p0) : ℂ := v (Fin.castLE X.p0_le a)

private lemma sum_eq_sum_castLE_p0_of_vanish_above (f : Fin r → ℂ) (hf : ∀ j : Fin r, X.p0 ≤ (j : ℕ) → f j = 0) :
    ∑ j, f j = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := by
  let e : Fin X.p0 ↪ Fin r := ⟨Fin.castLE X.p0_le, Fin.castLE_injective X.p0_le⟩
  calc ∑ j, f j = ∑ j ∈ Finset.univ.map e, f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hlt
        exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    _ = ∑ c, f (e c) := Finset.sum_map _ _ _
    _ = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := rfl

private lemma sum_eq_sum_castLE_p0_add_sum_nI (g : Fin r → ℂ) :
    ∑ c, g c = ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) + ∑ m, g (nI X m) := by
  have hr : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  rw [← Fintype.sum_equiv (finCongr hr) (fun i => g (finCongr hr i)) g (fun _ => rfl),
    Fin.sum_univ_add]
  rfl

lemma Lv_p (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (a : Fin X.p0) :
    ∑ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j * v j = v (Fin.castLE X.p0_le a) := by
  have hL : ∀ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j =
      if Fin.castLE X.p0_le a = j then 1 else 0 := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [dif_neg (fun hh => absurd hh.1 (not_le.mpr (by simp))), add_zero]
  simp only [hL, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma Lv_n (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) :
    ∑ j, X.lowBlock Z τ (nI X m) j * v j = Nv X Z τ v m := by
  have hL : ∀ j : Fin r, X.lowBlock Z τ (nI X m) j =
      (if nI X m = j then 1 else 0) + (if h : (j : ℕ) < X.p0 then Z τ m ⟨j, h⟩ else 0) := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    congr 1
    by_cases h : (j : ℕ) < X.p0
    · rw [dif_pos ⟨(by simp [nI] : X.p0 ≤ ((nI X m : Fin r) : ℕ)), h⟩, dif_pos h]
      exact congrFun (congrArg (Z τ) (Fin.ext (by simp [nI]))) _
    · rw [dif_neg (fun hh => h hh.2), dif_neg h]
  simp only [hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Nv]
  congr 1
  rw [sum_eq_sum_castLE_p0_of_vanish_above X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [dif_pos (by simp)]
    first | rfl | (congr 2) | simp
  · intro j hj
    rw [dif_neg (not_lt.mpr hj), zero_mul]

lemma Bf_coord (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) :
    Bf X Z τ v w = ∑ a, Pv X v a * conj (Pv X w a) - ∑ m, Nv X Z τ v m * conj (Nv X Z τ w m) := by
  have hG : ∀ a b, Gp X Z τ a b =
      ∑ c : Fin r, X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ c b) := by
    intro a b
    simp [Gp, Matrix.mul_apply, Matrix.diagonal_apply]
  have h1 : Bf X Z τ v w = ∑ c : Fin r, ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (∑ a, X.lowBlock Z τ c a * v a) *
      conj (∑ b, X.lowBlock Z τ c b * w b) := by
    calc Bf X Z τ v w = ∑ a, ∑ b, ∑ c : Fin r, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := by
          unfold Bf
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hG, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a, ∑ c : Fin r, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : Fin r, ∑ a, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul]
          ring
  rw [h1, sum_eq_sum_castLE_p0_add_sum_nI X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Lv_p X, Lv_p X]
    simp [sgn, Pv]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Lv_n X, Lv_n X]
    simp [sgn, nI]

lemma Bf_sub_left (Z : X.Coord) (τ : X.Ψ) (v t w : Fin r → ℂ) :
    Bf X Z τ (v - t) w = Bf X Z τ v w - Bf X Z τ t w := by
  simp only [Bf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma Bf_sub_right (Z : X.Coord) (τ : X.Ψ) (v t w : Fin r → ℂ) :
    Bf X Z τ w (v - t) = Bf X Z τ w v - Bf X Z τ w t := by
  simp only [Bf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma Bf_conj (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) : Bf X Z τ w v = conj (Bf X Z τ v w) := by
  rw [Bf_coord X, Bf_coord X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, starRingEnd_self_apply]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private lemma sum_eq_add_sum_castLE_of_vanish_above {n : ℕ} (k : Fin n) (f : Fin n → ℂ) (hf : ∀ j : Fin n, k < j → f j = 0) :
    ∑ j, f j = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := by
  let e : Fin k ↪ Fin n := ⟨Fin.castLE k.isLt.le, Fin.castLE_injective _⟩
  have hk : k ∉ Finset.univ.map e := by
    intro h
    obtain ⟨c, _, hc⟩ := Finset.mem_map.mp h
    have h1 := congrArg Fin.val hc
    have h2 := c.isLt
    simp only [e, Function.Embedding.coeFn_mk, Fin.coe_castLE] at h1
    omega
  calc ∑ j, f j = ∑ j ∈ insert k (Finset.univ.map e), f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hle
        push_neg at hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hj (Finset.mem_insert_of_mem
            (Finset.mem_map.mpr ⟨⟨(j : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩))
        · exact hj (by rw [heq]; exact Finset.mem_insert_self _ _)
    _ = f k + ∑ j ∈ Finset.univ.map e, f j := Finset.sum_insert hk
    _ = f k + ∑ c, f (e c) := by rw [Finset.sum_map]
    _ = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := rfl

lemma Bf_gv_zero (Z : X.Coord) (τ : X.Ψ) (hdet : ∀ c : Fin r, (blk (Gp X Z τ) c).det ≠ 0) (k : Fin r)
    (t : Fin r → ℂ) (ht : ∀ b, k ≤ b → t b = 0) :
    Bf X Z τ (fun a => uMat (Gp X Z τ) a k) t = 0 := by
  have hB : IsUnit (blk (Gp X Z τ) k).det := isUnit_iff_ne_zero.mpr (hdet k)
  have hw : Matrix.vecMul (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹)
      (blk (Gp X Z τ) k) = rowc (Gp X Z τ) k := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB, Matrix.vecMul_one]
  show ∑ a, ∑ b, uMat (Gp X Z τ) a k * Gp X Z τ a b * conj (t b) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : k ≤ b
  · simp [ht b hb]
  · push_neg at hb
    rw [← Finset.sum_mul]
    have hcol : ∑ c : Fin k, (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c *
        Gp X Z τ (Fin.castLE k.isLt.le c) b = Gp X Z τ k b := congrFun hw ⟨(b : ℕ), hb⟩
    have hu : ∀ c : Fin k, uMat (Gp X Z τ) (Fin.castLE k.isLt.le c) k =
        -(Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c := by
      intro c
      have hne : Fin.castLE k.isLt.le c ≠ k := by
        intro h
        have h1 := congrArg Fin.val h
        have h2 := c.isLt
        simp only [Fin.coe_castLE] at h1
        omega
      have hlt : Fin.castLE k.isLt.le c < k := Fin.lt_iff_val_lt_val.mpr (by simp)
      simp only [uMat, Matrix.of_apply, if_neg hne, dif_pos hlt]
      try rfl
    have hsum : ∑ a, uMat (Gp X Z τ) a k * Gp X Z τ a b = 0 := by
      rw [sum_eq_add_sum_castLE_of_vanish_above k]
      · rw [show uMat (Gp X Z τ) k k = 1 by simp [uMat]]
        simp only [hu, neg_mul, Finset.sum_neg_distrib]
        rw [hcol]
        ring
      · intro j hj
        simp only [uMat, Matrix.of_apply, if_neg (ne_of_gt hj), dif_neg (not_lt.mpr hj.le), zero_mul]
    rw [hsum, zero_mul]

lemma Bf_self_re (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) :
    (Bf X Z τ v v).re = nsq (Pv X v) - nsq (Nv X Z τ v) := by
  rw [Bf_coord X]
  simp only [Complex.sub_re, Complex.re_sum, nsq]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma Bf_pos_ge (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (hv : ∀ m, v (nI X m) = 0) :
    (1 - X.zN Z ^ 2) * nsq (Pv X v) ≤ (Bf X Z τ v v).re := by
  rw [Bf_self_re X]
  have hN : Nv X Z τ v = (Matrix.of (Z τ)).mulVec (Pv X v) := by
    funext m
    simp only [Nv, hv m, zero_add]
    rfl
  have h1 := nsq_mulVec_le_opN (Matrix.of (Z τ)) (Pv X v)
  have h2 := opN_le_zN X Z τ
  have h3 := opN_nonneg (Matrix.of (Z τ))
  have h4 := nsq_nonneg (Pv X v)
  rw [← hN] at h1
  have h5 : Data.opN (Matrix.of (Z τ)) ^ 2 ≤ X.zN Z ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h5 h4]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficientConvolution_holds : CoefficientConvolution (E := E) :=
  PeriodLatticeMembership.coefficientConvolution_of_subCoefficients (fun r X la P hP ξ hξ x hx ω hωp hωi k ν hk =>
    SublatticeCoefficients.subCoeff X la P hP ξ hξ x hx ω hωp hωi k ν hk)

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitativeHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cusp_coefficient_quantitative_holds : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Jt (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  I • ((2 : ℂ) • X.ppos x τ v - v)

def UBasis (z0 : Frame X.Ψ r) (ξ : Fin r → E) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ k, hermC τ.1 X.Gm (f τ k) (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ (f τ k)) (emb τ.1 ξ) = 0) ∧
    (∀ k, X.Jt z0 τ (f τ k) = (if (k : ℕ) < X.p0 - 1 then I else -I) • f τ k) ∧
    (∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0) ∧
    (∀ c : Fin (r - 2) → ℂ, X.maj z0 τ (∑ k, c k • f τ k) = ∑ k, ‖c k‖ ^ 2) ∧
    (∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 → hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 →
      v ∈ Submodule.span ℂ (Set.range (f τ)))

end Data

theorem exists_unitary_basis_same_flag (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r) (hξ : X.IsIso ξ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0) (hflag : X.SameFlag z0 x0) :
    ∃ f : X.Ψ → Fin (r - 2) → Fin r → ℂ, X.UBasis z0 ξ f := by

  choose f hf using fun τ : X.Ψ =>
    OrthonormalPerpBasis.ubasis_at (X := X.toData) ξ z0 x0 hξ.2.2 hξ.2.1 hz hx0 hortho hflag τ
  exact ⟨f, fun τ => hf τ⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankRieszBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FinrankRieszBounds

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring

variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]

theorem riesz (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add (f := _), Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith


omit hz in
theorem finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by
  classical
  let Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ) :=
    { toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ),
        hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)]
      map_add' := fun u v => by
        funext τ i
        fin_cases i <;> simp [hermC_add_left, Data.jp_add]
      map_smul' := fun c u => by
        funext τ i
        fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }
  have hker : LinearMap.ker Lm = Usub (X := X) z ξ := by
    ext u
    rw [LinearMap.mem_ker]
    show Lm u = 0 ↔ u ∈ X.Uz z ξ
    rw [MajorantOperators.mem_Uz_iff, funext_iff]
    refine forall_congr' fun τ => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp [Lm]
  have hsurj : LinearMap.range Lm = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    have hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0 := by
      intro τ
      rw [← Data.Hf_eq_jp, X.Hf_self hz]
      exact_mod_cast (X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'
    have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
      rw [hermC_emb, hξ.2.1, map_zero]
    refine ⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) •
        X.jp z τ (Data.emb τ.1 ξ) +
      (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩
    funext τ i
    fin_cases i
    · simp [Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]
    · simp [Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee,
        div_mul_cancel₀ _ (hm τ)]
  have hrn := LinearMap.finrank_range_add_finrank_ker Lm
  rw [hsurj, finrank_top, hker] at hrn
  have hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hdom, hcod] at hrn
  have hV : finrank ℝ (VT (X := X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl

  have hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E := by
    have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
      rw [Finset.disjoint_left]
      intro σ hσ hσ'
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ'
      exact (X.cmType τ).mp hτ hσ
    have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
      fun a b h => by
        have := congrArg ComplexEmbedding.conjugate h
        simpa using this
    have h1 := Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      NumberField.Embeddings.card] at h1
    rw [Fintype.card_coe]
    omega
  have hf : Fintype.card X.Ψ ≤ fdeg E := by
    unfold fdeg
    omega
  rw [hV]
  have hk : finrank ℝ (Usub (X := X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by
    rw [Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]
    ring_nf
  rw [hk]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)

end FinrankRieszBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]

end ReciprocityTheory.ChartRestriction.G.FD
end

