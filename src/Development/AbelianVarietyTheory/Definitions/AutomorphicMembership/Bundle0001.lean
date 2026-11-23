module

public import Mathlib
public import Formalism.DegreeFormula.Statement
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder

namespace GlobalTheory.HodgeDomain

variable {p q : ℕ}

def jW (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ -
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁

theorem upq_iff {g : GL (Fin p ⊕ Fin q) ℂ} : g ∈ Upq p q ↔
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Jpq p q * g = Jpq p q := by
  unfold Upq UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  have hc : cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
    ext i j
    simp [cT, conjTranspose_apply]
  rw [hc]

theorem Jpq_sq : Jpq p q * Jpq p q = 1 := by
  unfold Jpq
  rw [fromBlocks_multiply]
  simp

theorem upq_right {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ =
      Jpq p q := by
  have h := upq_iff.mp hg
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have h1 : (Jpq p q * Gᴴ * Jpq p q) * G = 1 := by
    rw [show Jpq p q * Gᴴ * Jpq p q * G = Jpq p q * (Gᴴ * Jpq p q * G) by simp only [Matrix.mul_assoc], h, Jpq_sq]
  have h2 : G * (Jpq p q * Gᴴ * Jpq p q) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc G * Jpq p q * Gᴴ = G * (Jpq p q * Gᴴ * Jpq p q) * Jpq p q := by
        simp only [Matrix.mul_assoc, Jpq_sq, Matrix.mul_one]
    _ = Jpq p q := by rw [h2, Matrix.one_mul]

private lemma Jpq_mul_fromRows {n : Type*} (C : Matrix (Fin p) n ℂ) (D : Matrix (Fin q) n ℂ) :
    Jpq p q * fromRows C D = fromRows C (-D) := by
  ext (i | i) j <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma conjTranspose_fromRows_mul_Jpq_mul_fromRows {n m : Type*} (A : Matrix (Fin p) n ℂ) (B : Matrix (Fin q) n ℂ)
    (C : Matrix (Fin p) m ℂ) (D : Matrix (Fin q) m ℂ) :
    (fromRows A B)ᴴ * Jpq p q * fromRows C D = Aᴴ * C - Bᴴ * D := by
  rw [Matrix.mul_assoc, Jpq_mul_fromRows]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma fromCols_mul_Jpq {m : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ) :
    fromCols A B * Jpq p q = fromCols A (-B) := by
  ext i (j | j) <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma fromCols_mul_Jpq_mul_conjTranspose_fromCols {m n : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ)
    (C : Matrix n (Fin p) ℂ) (D : Matrix n (Fin q) ℂ) :
    fromCols A B * Jpq p q * (fromCols C D)ᴴ = A * Cᴴ - B * Dᴴ := by
  rw [fromCols_mul_Jpq]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma blocks_mul_fromRows {n : Type*} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (X : Matrix (Fin p) n ℂ) (Y : Matrix (Fin q) n ℂ) :
    M * fromRows X Y = fromRows (M.toBlocks₁₁ * X + M.toBlocks₁₂ * Y) (M.toBlocks₂₁ * X + M.toBlocks₂₂ * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem kapQ_gram {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) (z : Matrix (Fin p) (Fin q) ℂ) :
    (kapQ g z)ᴴ * kapQ g z -
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂)ᴴ *
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) = hQ z := by
  have h := upq_iff.mp hg
  unfold kapQ hQ
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have e1 : (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ) := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
  rw [blocks_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows] at e1
  simp only [Matrix.mul_one, conjTranspose_one] at e1
  simpa only [neg_sub] using congrArg Neg.neg e1

theorem kapQ_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (kapQ g z).det := by
  have h1 := kapQ_gram hg z
  have hpd : ((kapQ g z)ᴴ * kapQ g z).PosDef := by
    rw [eq_add_of_sub_eq h1]
    exact Matrix.PosDef.add_posSemidef (by exact hz) (posSemidef_conjTranspose_mul_self _)
  rw [isUnit_iff_ne_zero]
  intro h0
  have := hpd.det_pos
  rw [det_mul, det_conjTranspose, h0, mul_zero] at this
  exact lt_irrefl _ this

theorem moeb_mul_kapQ {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ := by
  have hu := kapQ_isUnit hg hz
  calc moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z + (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) *
        ((kapQ g z)⁻¹ * kapQ g z) := by
        rw [moeb, Matrix.mul_assoc]; rfl
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem hQ_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z = hQ z := by
  have e := moeb_mul_kapQ hg hz
  have h1 := kapQ_gram hg z
  calc (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z =
      (kapQ g z)ᴴ * kapQ g z - (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z)ᴴ * (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z) := by
        unfold hQ
        rw [conjTranspose_mul]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = hQ z := by rw [e]; exact h1

theorem moeb_mem {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q := by
  have hu : IsUnit (kapQ g z) := (Matrix.isUnit_iff_isUnit_det _).mpr (kapQ_isUnit hg hz)
  have h2 : ((kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z).PosDef := by
    rw [hQ_moeb hg hz]; exact hz
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mp h2

private lemma fromCols_mul_eq_blocks {m : Type*} (X : Matrix m (Fin p) ℂ) (Y : Matrix m (Fin q) ℂ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    fromCols X Y * M = fromCols (X * M.toBlocks₁₁ + Y * M.toBlocks₂₁) (X * M.toBlocks₁₂ + Y * M.toBlocks₂₂) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

private lemma mul_fromCols' {m k : Type*} [Fintype m] (N : Matrix k m ℂ) (X : Matrix m (Fin p) ℂ)
    (Y : Matrix m (Fin q) ℂ) : N * fromCols X Y = fromCols (N * X) (N * Y) := by
  ext i (j | j) <;> simp [Matrix.mul_apply]

theorem hP_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    jW g z * hP z * (jW g z)ᴴ = hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) := by
  have h := upq_right hg
  have e := moeb_mul_kapQ hg hz
  unfold jW hP
  unfold kapQ at e
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h e ⊢
  generalize moeb G z = w at e ⊢
  rw [Matrix.mul_add, ← Matrix.mul_assoc] at e
  have k1 : fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G =
      (G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) := by
    rw [fromCols_mul_eq_blocks, mul_fromCols']
    have b1 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₁ + -w * G.toBlocks₂₁ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * 1 := by
      rw [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, sub_eq_add_neg]
    have b2 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₂ + -w * G.toBlocks₂₂ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * -z := by
      rw [Matrix.one_mul, Matrix.neg_mul, eq_sub_of_add_eq' e, Matrix.mul_neg, Matrix.sub_mul]
      abel
    rw [b1, b2]
  have k2 : (G.toBlocks₁₁ - w * G.toBlocks₂₁) *
        (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ) *
        (G.toBlocks₁₁ - w * G.toBlocks₂₁)ᴴ =
      fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w))ᴴ := by
    calc _ = ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z)) * Jpq p q *
          ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G)ᴴ := by
            rw [k1]
      _ = _ := by
            rw [conjTranspose_mul]
            conv_rhs => rw [← h]
            simp only [Matrix.mul_assoc]
  rw [fromCols_mul_Jpq_mul_conjTranspose_fromCols, fromCols_mul_Jpq_mul_conjTranspose_fromCols] at k2
  simpa only [conjTranspose_one, Matrix.mul_one, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using k2

theorem hP_mul_eq_one {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    hP z * (1 + z * (hQ z)⁻¹ * zᴴ) = 1 := by
  have hpd : (hQ z).PosDef := hz
  have hu : IsUnit (hQ z).det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  have key : z * (hQ z * (hQ z)⁻¹) * zᴴ = z * zᴴ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  generalize (hQ z)⁻¹ = R at key ⊢
  unfold hQ at key
  unfold hP
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc] at key ⊢
  rw [← key]
  abel

theorem hP_inv_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z)⁻¹.PosDef := by
  have e : (hP z)⁻¹ = 1 + z * (hQ z)⁻¹ * zᴴ := Matrix.inv_eq_right_inv (hP_mul_eq_one hz)
  rw [e]
  have hq : (hQ z).PosDef := hz
  exact Matrix.PosDef.one.add_posSemidef (hq.inv.posSemidef.mul_mul_conjTranspose_same z)

theorem hP_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z).PosDef := by
  have hu : IsUnit (hP z).det := Matrix.isUnit_det_of_right_inverse (hP_mul_eq_one hz)
  have h := (hP_inv_posDef hz).inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at h

theorem jW_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (jW g z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := (hP_posDef (moeb_mem hg hz)).det_pos
  rw [← hP_moeb hg hz, det_mul, det_mul, det_conjTranspose, h0] at h
  simp at h

theorem hP_inv_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (jW g z)ᴴ * (hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z))⁻¹ * jW g z = (hP z)⁻¹ := by
  have hu := jW_isUnit hg hz
  have hu' : IsUnit (jW g z)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  rw [← hP_moeb hg hz, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hu',
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

def tanAct (g : GL (Fin p ⊕ Fin q) ℂ) (z ξ : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  jW g z * ξ * (kapQ g z)⁻¹

def blkMet (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks A 0 0 B

theorem blkMet_posDef {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) : (blkMet A B).PosDef := by
  unfold blkMet
  have hpsd : (fromBlocks A 0 0 B).PosSemidef := by
    let _ := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
    have h0 : (0 : Matrix (Fin q) (Fin p) ℂ) = (0 : Matrix (Fin p) (Fin q) ℂ)ᴴ := by simp
    rw [h0]
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ hA).2 (by simpa using hB.posSemidef)
  refine hpsd.posDef_iff_isUnit.2 ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
  exact (isUnit_iff_ne_zero.mpr hA.det_pos.ne').mul (isUnit_iff_ne_zero.mpr hB.det_pos.ne')

def hodge (c : ℝ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  blkMet ((c : ℂ) • (hP z)⁻¹) ((c : ℂ) • hQ z)

theorem hodge_posDef {c : ℝ} (hc : 0 < c) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).PosDef := by
  unfold hodge
  have hc' : (0 : ℂ) < (c : ℂ) := Complex.zero_lt_real.mpr hc
  exact blkMet_posDef ((hP_inv_posDef hz).smul hc') ((show (hQ z).PosDef from hz).smul hc')

end GlobalTheory.HodgeDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
section
noncomputable section

open NumberField IsDedekindDomain Topology
open scoped ContDiff

namespace GlobalTheory.CuspRep

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h1 : ‖(∑ k ∈ Finset.range n, z ^ k) - n‖ ≤ n / 2 := by
    have : (∑ k ∈ Finset.range n, z ^ k) - n = ∑ k ∈ Finset.range n, (z ^ k - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (h k).le).trans ?_
    simp; linarith
  have h2 : (n : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    have := norm_sub_norm_le (n : ℂ) (∑ k ∈ Finset.range n, z ^ k)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    linarith
  have h3 := h n
  rw [← geom_sum_mul, norm_mul] at h3
  rw [div_lt_iff₀ hp] at hn
  nlinarith

theorem isOpen_ker_finIdele (E : Type) [Field E] [NumberField E] (ψ : (FiniteAdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hψ : Continuous ψ) : IsOpen {u | ψ u = 1} := by
  have hV : {u | ‖((ψ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 E) E)ˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hψ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : FiniteAdeleRing (𝓞 E) E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : FiniteAdeleRing (𝓞 E) E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : FiniteAdeleRing (𝓞 E) E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  let P : Set (FiniteAdeleRing (𝓞 E) E) :=
    {c | ∃ a : FiniteAdeleRing (𝓞 E) E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ c = N • a}
  have hP : P ∈ 𝓝 0 := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN
  have hmul : ∀ x y : FiniteAdeleRing (𝓞 E) E, x - 1 ∈ P → y - 1 ∈ P → x * y - 1 ∈ P := by
    rintro x y ⟨a, ha, e⟩ ⟨b, hb, e'⟩
    refine ⟨a + b + N • (a * b), fun v => add_mem (add_mem (ha v) (hb v)) (nsmul_mem (mul_mem (ha v) (hb v)) N), ?_⟩
    rw [eq_add_of_sub_eq e, eq_add_of_sub_eq e']
    simp only [nsmul_eq_mul]; ring
  let H : Submonoid (FiniteAdeleRing (𝓞 E) E)ˣ :=
    { carrier := {u | (u : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P}
      one_mem' := ⟨by simpa using mem_of_mem_nhds hP, by simpa using mem_of_mem_nhds hP⟩
      mul_mem' := fun {x y} hx hy => ⟨hmul _ _ hx.1 hy.1, by rw [mul_inv, Units.val_mul]; exact hmul _ _ hx.2 hy.2⟩ }
  have hH : (H : Set (FiniteAdeleRing (𝓞 E) E)ˣ) ∈ 𝓝 1 := by
    change ({u : (FiniteAdeleRing (𝓞 E) E)ˣ | (u : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P} ∩
      {u : (FiniteAdeleRing (𝓞 E) E)ˣ | (↑u⁻¹ : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P}) ∈ 𝓝 1
    refine Filter.inter_mem ?_ ?_
    · exact (Units.continuous_val.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
    · exact (Units.continuous_coe_inv.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
  have hk : ∀ u ∈ H, ψ u = 1 := by
    intro u hu
    apply Units.ext
    refine eq_one_of_pow_near fun n => ?_
    obtain ⟨⟨a, ha, e⟩, ⟨b, hb, e'⟩⟩ := pow_mem hu n
    have := hTV (a := u ^ n) (hTT ⟨?_, ?_⟩)
    · simpa using this
    · change ((u ^ n : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T1
      rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
    · change MulOpposite.op (((u ^ n)⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T2
      rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2
  exact ψ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hH hk)

variable {ι : Type} [Fintype ι]

def expU (z : ι → ℂ) : (ι → ℂ)ˣ :=
  ⟨fun i => Complex.exp (z i), fun i => Complex.exp (-z i),
    by funext i; simp [← Complex.exp_add], by funext i; simp [← Complex.exp_add]⟩


omit [Fintype ι] in
theorem expU_add (z z' : ι → ℂ) : expU (z + z') = expU z * expU z' :=
  Units.ext (funext fun i => Complex.exp_add (z i) (z' i))


omit [Fintype ι] in
theorem expU_zero : expU (0 : ι → ℂ) = 1 := Units.ext (funext fun _ => Complex.exp_zero)


omit [Fintype ι] in
theorem unit_ne_zero (u : (ι → ℂ)ˣ) (i : ι) : (u : ι → ℂ) i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrFun u.mul_inv i)


omit [Fintype ι] in
theorem expU_log (u : (ι → ℂ)ˣ) : expU (fun i => Complex.log ((u : ι → ℂ) i)) = u :=
  Units.ext (funext fun i => Complex.exp_log (unit_ne_zero u i))


omit [Fintype ι] in
theorem continuous_expU : Continuous (expU : (ι → ℂ) → (ι → ℂ)ˣ) :=
  Units.continuous_iff.2 ⟨continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i),
    continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i).neg⟩

theorem exists_lin (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ L : (ι → ℂ) →L[ℝ] ℂ, ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z) := by
  let f : C(ι → ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z => ⟨(ψ (expU z) : ℂˣ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp continuous_expU)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, expU_zero]))
  have hF' : ∀ z, Complex.exp (F z) = (ψ (expU z) : ℂˣ) := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', expU_add, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩


open Classical in
def extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (x : ι → ℂ) : ℂ := by
  classical
  exact if h : IsUnit x then (ψ h.unit : ℂˣ) else 0


omit [Fintype ι] in
theorem extZero_unit (ψ : (ι → ℂ)ˣ →* ℂˣ) (u : (ι → ℂ)ˣ) : extZero ψ u = (ψ u : ℂˣ) := by
  simp [extZero]

theorem extZero_eventually {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℂ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℂ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Complex.log (x i / (u : ι → ℂ) i)) := by
  have h : ∀ᶠ x in 𝓝 (u : ι → ℂ), ∀ i, x i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually_ne (unit_ne_zero u i)
  filter_upwards [h] with x hx
  have e : x = ((u * expU fun i => Complex.log (x i / (u : ι → ℂ) i) : (ι → ℂ)ˣ) : ι → ℂ) := by
    funext i
    change x i = (u : ι → ℂ) i * Complex.exp (Complex.log (x i / (u : ι → ℂ) i))
    rw [Complex.exp_log (div_ne_zero (hx i) (unit_ne_zero u i)), mul_div_cancel₀ _ (unit_ne_zero u i)]
  conv_lhs => rw [e, extZero_unit, map_mul, Units.val_mul, hL]

theorem contDiffAt_extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) (u : (ι → ℂ)ˣ) :
    ContDiffAt ℝ ∞ (extZero ψ) u := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  refine ContDiffAt.congr_of_eventuallyEq ?_ (extZero_eventually hL u)
  refine contDiffAt_const.mul (ContDiffAt.cexp (L.contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun i => ?_)))
  have h1 : ContDiffAt ℝ ∞ Complex.log ((u : ι → ℂ) i / (u : ι → ℂ) i) := by
    rw [div_self (unit_ne_zero u i)]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  exact h1.comp (f := fun x : ι → ℂ => x i / (u : ι → ℂ) i) _
    ((contDiffAt_apply ℝ (fun _ : ι => ℂ) i _).div_const _)

theorem fderiv_extZero {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ} (hψ : Continuous ψ)
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) : fderiv ℝ (extZero ψ) 1 = L := by
  have h0 : DifferentiableAt ℝ (extZero ψ) 1 := (contDiffAt_extZero ψ hψ 1).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun z : ι → ℂ => fun i => Complex.exp (z i)) (ContinuousLinearMap.id ℝ _) 0 := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt (x := 0)).cexp
    simpa using this
  have h2 : HasFDerivAt (extZero ψ) (fderiv ℝ (extZero ψ) 1) (fun i : ι => Complex.exp ((0 : ι → ℂ) i)) := by
    have : (fun i : ι => Complex.exp ((0 : ι → ℂ) i)) = 1 := funext fun _ => Complex.exp_zero
    rw [this]; exact h0.hasFDerivAt
  have h3 := h2.comp 0 h1
  have h4 : HasFDerivAt (fun z => Complex.exp (L z)) L 0 := by
    simpa using (L.hasFDerivAt (x := 0)).cexp
  have h5 : (extZero ψ ∘ fun z : ι → ℂ => fun i => Complex.exp (z i)) = fun z => Complex.exp (L z) :=
    funext fun z => (extZero_unit ψ (expU z)).trans (hL z)
  rw [h5] at h3
  simpa using h3.unique h4

theorem exists_bound (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (u : (ι → ℂ)ˣ) (B : ℝ), 1 ≤ B → ‖(u : ι → ℂ)‖ ≤ B → ‖((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ)‖ ≤ B →
      ‖((ψ u : ℂˣ) : ℂ)‖ ≤ C * B ^ N := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖L‖
  refine ⟨Real.exp (N * Real.pi), N, (Real.exp_pos _).le, fun u B hB h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hz : ‖fun i => Complex.log ((u : ι → ℂ) i)‖ ≤ Real.pi + Real.log B := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, add_comm]
    refine add_le_add (Complex.abs_arg_le_pi _) (abs_le.2 ⟨?_, ?_⟩)
    · have e : ((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ) i = ((u : ι → ℂ) i)⁻¹ :=
        eq_inv_of_mul_eq_one_right (congrFun u.mul_inv i)
      have := Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u⁻¹ i)) ((norm_le_pi_norm _ i).trans h2)
      rw [e, norm_inv, Real.log_inv] at this
      linarith
    · exact Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u i)) ((norm_le_pi_norm _ i).trans h1)
  rw [← expU_log u, hL, Complex.norm_exp]
  have h3 : (L fun i => Complex.log ((u : ι → ℂ) i)).re ≤ N * (Real.pi + Real.log B) :=
    (Complex.re_le_norm _).trans ((L.le_opNorm _).trans (mul_le_mul hN hz (norm_nonneg _) (Nat.cast_nonneg _)))
  refine (Real.exp_le_exp.2 h3).trans_eq ?_
  rw [mul_add, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]

end GlobalTheory.CuspRep
end
end

