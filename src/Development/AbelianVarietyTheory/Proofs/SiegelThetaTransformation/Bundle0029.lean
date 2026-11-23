module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

noncomputable def spOf (γ : GL (Fin r) E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ :=
  Matrix.of fun p q => crd X bas (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
    ((bas (Pi.single p.swap 1) : X.Λ) : Fin r → E)) q.swap


omit [NumberField E] [IsCMField E] in
theorem gl_mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable {X bas}

theorem IsUn.lact_mem {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by

  have hent : ∀ a b, ∑ c, ∑ d, (γ : Matrix (Fin r) (Fin r) E) c a * X.Gm c d *
      cc ((γ : Matrix (Fin r) (Fin r) E) d b) = X.Gm a b := by
    intro a b
    have h := hγ (Pi.single a 1) (Pi.single b 1)
    simpa [herm, Matrix.mulVec, dotProduct, Pi.single_apply, cc] using h

  have key : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    intro τ
    ext a b
    have h := congrArg τ.1 (hent a b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, cc, NumberField.IsCMField.complexEmbedding_complexConj] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact h

  have hgram : ∀ (τ : X.Ψ) (m : Matrix (Fin r) (Fin r) ℂ),
      gram τ.1 X.Gm m = mᵀ * X.Gm.map τ.1 * m.map (starRingEnd ℂ) := by
    intro τ m
    ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    intro τ
    have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    calc (mat x τ)ᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) *
            (mat x τ).map (starRingEnd ℂ))
        = (mat x τ)ᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) *
            (mat x τ).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
      _ = (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by rw [key]
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  refine ⟨?_, fun i => ?_⟩
  · have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero) hdet
  · simpa only [dmin, hmat τ] using hpos i

theorem spOf_mem (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    spOf X bas γ ∈ Matrix.symplecticGroup (Fin g) ℚ := by

  have hinv : ∀ u v : Fin r → E, EF X (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF X u v := by
    intro u v
    have h := hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
    rw [gl_mulVec_inv_mulVec, gl_mulVec_inv_mulVec] at h
    rw [EF_def, EF_def, h]

  have hrow : ∀ p p' : Fin g ⊕ Fin g,
      ∑ i, (spOf X bas γ p (Sum.inr i) * spOf X bas γ p' (Sum.inl i) -
        spOf X bas γ p (Sum.inl i) * spOf X bas γ p' (Sum.inr i)) =
      ((omegaStd (Pi.single p.swap 1 : Fin g ⊕ Fin g → ℤ) (Pi.single p'.swap 1) : ℤ) : ℚ) := by
    intro p p'
    have h := hinv (bas (Pi.single p.swap 1)) (bas (Pi.single p'.swap 1))
    rw [EF_crd hs, hs] at h
    simp only [spOf, Matrix.of_apply, Sum.swap_inl, Sum.swap_inr]
    linarith
  rw [SymplecticGroup.mem_iff]
  ext p p'
  have hJl : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inl j) = spOf X bas γ p (Sum.inr j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  have hJr : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inr j) = -spOf X bas γ p (Sum.inl j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hJl, hJr, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib]
  rw [hrow]
  rcases p with i | i <;> rcases p' with j | j <;>
    simp [omegaStd, Pi.single_apply, Matrix.J, Matrix.one_apply, eq_comm]

theorem hMat_mul_perMat_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : Fin g → Fin g ⊕ Fin g) :
    hMat X bas idx x * perMat X bas idx s (lact γ x) =
      (qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inl j)) * tauMat X bas idx x +
        qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inr j)))ᵀ := by
  have hsym := tauMat_isSymm (idx := idx) hs hx
  ext i k
  have hcol : (fun l => perMat X bas idx s (lact γ x) l k) =
      per X x (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)) ∘ idx := by
    funext l
    rw [perMat_apply, Function.comp_apply,
      ← per_lact x hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)), gl_mulVec_inv_mulVec]
  have hlhs : (hMat X bas idx x * perMat X bas idx s (lact γ x)) i k =
      (hMat X bas idx x *ᵥ fun l => perMat X bas idx s (lact γ x) l k) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hlhs, hcol, hMat_mulVec_per_crd (idx := idx) hs hx]
  simp only [spOf, qm, qv, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.add_apply,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Sum.swap_swap, Sum.swap_inl,
    Sum.swap_inr]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym.apply]
  ring

theorem periods_lact_symplectic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∃ σ ∈ Matrix.symplecticGroup (Fin g) ℚ, ∀ x ∈ X.dom, lact γ x ∈ X.dom ∧ tauMat X bas idx x ∈ Siegel (Fin g) ∧ tauMat X bas idx (lact γ x) = spAct σ (tauMat X bas idx x) ∧ hMat X bas idx (lact γ x) = ((spDen σ (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
  intro E _ _ _ r X g bas idx n hs _ γ hγ
  refine ⟨spOf X bas γ, spOf_mem hs hγ, fun x hx => ?_⟩
  have hx' := IsUn.lact_mem hγ hx
  have hD : hMat X bas idx x * perMat X bas idx Sum.inl (lact γ x) =
      (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inl
  have hN : hMat X bas idx x * perMat X bas idx Sum.inr (lact γ x) =
      (qm (spOf X bas γ).toBlocks₁₁ * tauMat X bas idx x + qm (spOf X bas γ).toBlocks₁₂)ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inr
  have hH := isUnit_det_hMat (idx := idx) hs hx
  have hP := isUnit_det_perMat (idx := idx) hs hx'
  have hPeq : perMat X bas idx Sum.inl (lact γ x) =
      (hMat X bas idx x)⁻¹ * (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    rw [← hD, Matrix.nonsing_inv_mul_cancel_left _ _ hH]
  have hh : hMat X bas idx (lact γ x) =
      ((spDen (spOf X bas γ) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
    change (perMat X bas idx Sum.inl (lact γ x))⁻¹ = _
    rw [hPeq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hH, Matrix.transpose_nonsing_inv]
  refine ⟨hx', ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩, ?_, hh⟩
  have ht : tauMat X bas idx (lact γ x) = (spAct (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    change hMat X bas idx (lact γ x) * perMat X bas idx Sum.inr (lact γ x) = _
    rw [hh, Matrix.mul_assoc, hN, spAct, Matrix.transpose_mul]
  have hsym := tauMat_isSymm (idx := idx) hs hx'
  rw [← hsym, ht, Matrix.transpose_transpose]

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandard
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Patch

open GlobalTheory.SW.Base

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_coprime (𝔞 : Ideal (𝓞 E)) (M : ℕ) (h0 : 𝔞 ≠ ⊥)
    (h : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)})) : ∃ a : ℕ, 0 < a ∧ a.Coprime M ∧ (a : 𝓞 E) ∈ 𝔞 := by
  have ex : ∃ a : ℕ, 0 < a ∧ (a : 𝓞 E) ∈ 𝔞 :=
    ⟨Ideal.absNorm 𝔞, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), Ideal.absNorm_mem 𝔞⟩
  obtain ⟨ha0, ha⟩ := Nat.find_spec ex
  refine ⟨Nat.find ex, ha0, ?_, ha⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left (Nat.find ex) M
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right (Nat.find ex) M
  set g := Nat.gcd (Nat.find ex) M with hg
  have hpos : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hmem : (a' : 𝓞 E) ∈ 𝔞 := by
    have e : (a' : 𝓞 E) = a' * x + (z * m') * (Nat.find ex : ℕ) := by
      have e1 : (M : 𝓞 E) = g * m' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hm'
      have e2 : ((Nat.find ex : ℕ) : 𝓞 E) = g * a' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) ha'
      rw [e2]
      rw [e1] at hxy
      linear_combination (-(a' : 𝓞 E)) * hxy
    rw [e]
    exact 𝔞.add_mem (𝔞.mul_mem_left _ hx) (𝔞.mul_mem_left _ ha)
  have hle : Nat.find ex ≤ a' := Nat.find_min' ex ⟨hpos, hmem⟩
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by intro h; rw [h] at ha'; omega)
  have : g ≤ 1 := by
    by_contra hc
    have : 2 * a' ≤ g * a' := Nat.mul_le_mul_right _ (by omega)
    omega
  show g = 1
  omega

omit [NumberField E] in
theorem int_congr {x y : E} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [NumberField E] in
theorem mem_left {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J := (Ideal.mul_le_inf h).1

omit [NumberField E] in
theorem mem_right {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J' := (Ideal.mul_le_inf h).2

variable [IsCMField E] {n : ℕ}

theorem herm_smul_left (c : E) (x y : Fin n → E) : herm 1 (c • x) y = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, _root_.mul_assoc]

theorem herm_nat_right (c : ℕ) (x y : Fin n → E) : herm 1 x ((c : E) • y) = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, cc, mul_left_comm]

omit [IsCMField E] in
theorem int_of_coprime {a b : ℕ} (h : a.Coprime b) {x : E} (h1 : IsIntegral ℤ ((a : E) * x))
    (h2 : IsIntegral ℤ ((b : E) * x)) : IsIntegral ℤ x := by
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have hbezout : (u : E) * a + (v : E) * b = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → E) huv
  have hx : (u : E) * ((a : E) * x) + (v : E) * ((b : E) * x) = x := by
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul, hbezout, _root_.one_mul]
  rw [← hx]
  exact ((isIntegral_intCast u).mul h1).add ((isIntegral_intCast v).mul h2)

theorem patch {M t : ℕ} (ht : 0 < t) (htM : t.Coprime M) (J J' : Ideal (𝓞 E)) (hJ : (M : 𝓞 E) ∈ J)
    (hJ' : (M : 𝓞 E) ∈ J') (A : Lt E n) (hA : A.FG) (hsd : ∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y))
    (h1 : ∀ j ∈ J, ∀ v ∈ A, (j : E) • (t : E) • v ∈ stdL E n)
    (h2 : ∀ j ∈ J', ∀ v ∈ stdL E n, (j : E) • (t : E) • v ∈ A) :
    ∃ C ∈ Vset E n M, (J * J') • A ≤ C ∧ (J * J') • C ≤ A := by
  obtain ⟨hS, hSsd, -⟩ := Base.stdL_mem_Vset (E := E) n M
  have k1 : ∀ v ∈ A, (M : E) • (t : E) • v ∈ stdL E n := fun v hv => by simpa using h1 _ hJ v hv
  have k2 : ∀ v ∈ stdL E n, (M : E) • (t : E) • v ∈ A := fun v hv => by simpa using h2 _ hJ' v hv
  let C : Lt E n :=
    { carrier := {v | (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n}
      add_mem' := fun ha hb => ⟨by rw [smul_add]; exact A.add_mem ha.1 hb.1,
        by rw [smul_add]; exact (stdL E n).add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c v hv => ⟨by rw [smul_comm]; exact A.smul_mem c hv.1,
        by rw [smul_comm]; exact (stdL E n).smul_mem c hv.2⟩ }
  have mC : ∀ v, v ∈ C ↔ (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n := fun v => Iff.rfl
  have cA : ∀ v ∈ A, (M : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨nat_smul_mem _ _ (nat_smul_mem _ _ hv), by rw [smul_comm]; exact k1 v hv⟩
  have cS : ∀ v ∈ stdL E n, (t : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨k2 v hv, nat_smul_mem _ _ (nat_smul_mem _ _ hv)⟩
  refine ⟨C, ⟨?_, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, t, ht, htM, fun v hv => hv.2, cS⟩, ?_, ?_⟩
  · have hle : C ≤ A ⊔ stdL E n := fun v hv =>
      mem_of_coprime _ htM (Submodule.mem_sup_right hv.2) (Submodule.mem_sup_left hv.1)
    haveI := isNoetherian_of_fg_of_noetherian _ (hA.sup hS)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · have a1 := (hsd _).1 hx.1 _ hy.1
    have a2 := (hSsd _).1 hx.2 _ hy.2
    rw [herm_smul_left, herm_nat_right, ← _root_.mul_assoc, ← Nat.cast_mul] at a1 a2
    exact int_of_coprime (Nat.Coprime.mul_left (htM.mul_right htM) (htM.mul_right htM)) a2 a1
  · refine (mC _).2 ⟨(hsd _).2 fun y hy => ?_, (hSsd _).2 fun y hy => ?_⟩
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cA y hy)
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cS y hy)
  · refine Submodule.smul_le.2 fun j hj v hv => (mC _).2 ⟨nat_smul_mem _ _ (A.smul_mem j hv), ?_⟩
    rw [smul_comm (t : E) j v]; exact h1 j (mem_left hj) v hv
  · refine Submodule.smul_le.2 fun j hj v hv => ?_
    refine mem_of_coprime A (s := t * t) (R := M) (Nat.Coprime.mul_left htM htM) ?_ ?_
    · have := h2 j (mem_right hj) _ ((mC v).1 hv).2
      rw [smul_comm _ j v, Nat.cast_mul, mul_smul]; exact this
    · rw [smul_comm _ j v]; exact A.smul_mem j ((mC v).1 hv).1

theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]

theorem moved (d : Fin n → E) (hd : ∀ k, cc (d k) * d k = 1) (Λ : Lt E n) (hfg : Λ.FG)
    (hsd : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) :
    ∃ A : Lt E n, A.FG ∧ (∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ v, v ∈ A ↔ (fun k => cc (d k) * v k) ∈ Λ := by
  let g : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin (Matrix.diagonal d)).restrictScalars (𝓞 E)
  have hg : ∀ v, g v = fun k => d k * v k := fun v => by
    ext k; simp [g, Matrix.mulVec_diagonal]
  have mA : ∀ v, v ∈ Λ.map g ↔ (fun k => cc (d k) * v k) ∈ Λ := fun v => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (fun k => cc (d k) * g w k) = w := by
        ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, hd, _root_.one_mul]
      rw [this]; exact hw
    · intro hv
      refine ⟨_, hv, ?_⟩
      ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, mul_comm (d k), hd, _root_.one_mul]
  have hh : ∀ x y : Fin n → E, herm 1 (fun k => cc (d k) * x k) y = herm 1 x (g y) := fun x y => by
    rw [hg, Base.herm_one, Base.herm_one]
    exact Finset.sum_congr rfl fun k _ => by rw [cc_mul]; ring
  refine ⟨Λ.map g, hfg.map g, fun x => ?_, mA⟩
  rw [mA, hsd]
  simp only [hh]
  exact ⟨by rintro h _ ⟨y, hy, rfl⟩; exact h y hy, fun h y hy => h _ ⟨y, hy, rfl⟩⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  intro E _ _ _ n r M 𝔍 𝔞 α hM hMJ _ hα hsp hco h hh
  have hα' : (α : E) ≠ 0 := by exact_mod_cast hα
  have hcα : cc (α : E) ≠ 0 := by simpa [cc] using hα'
  set d : Fin n → E := fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E) with hdd
  have hcd : ∀ k, cc (d k) = if (k : ℕ) < r then 1 else (α : E) / cc (α : E) := fun k => by
    simp only [hdd]; split_ifs <;> simp [cc]
  have hd : ∀ k, cc (d k) * d k = 1 := fun k => by
    rw [hcd]; simp only [hdd]; split_ifs
    · simp
    · field_simp
  refine ⟨?_, ?_⟩
  · ext i j
    subst hh
    rw [Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij; simp [ccT, hd]
    · simp [ccT, Matrix.one_apply, hij, Matrix.diagonal_apply, Ne.symm hij, cc]
  rintro Λ ⟨hfg, hsd, s, hs, hsM, hΛS, hSΛ⟩
  obtain ⟨A, hA, hAsd, mA⟩ := moved d hd Λ hfg hsd
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hsp
    exact hα hsp
  obtain ⟨a, ha0, haM, ha⟩ := exists_nat_coprime 𝔞 M h𝔞 hco
  have cnat : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  have q1 : ∀ j ∈ 𝔍, IsIntegral ℤ ((j : E) * a / α) := fun j hj => by
    have : j * a ∈ Ideal.span {α} := hsp ▸ Ideal.mul_mem_mul hj ha
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    have e : (j : E) * a / α = z := by
      rw [div_eq_iff hα']; exact_mod_cast congrArg (fun u : 𝓞 E => (u : E)) hz.symm
    rw [e]; exact z.isIntegral_coe
  have q2 : ∀ j ∈ conjI 𝔍, IsIntegral ℤ ((j : E) * a / cc (α : E)) := fun j hj => by
    induction hj using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have := isIntegral_cc (q1 b hb)
      rw [e]; simpa [cc] using this
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy =>
      refine int_congr (hx.add hy) ?_
      push_cast; ring
    | smul c x _ hx =>
      refine int_congr (c.isIntegral_coe.mul hx) ?_
      rw [smul_eq_mul]; push_cast; ring
  have p1 : ∀ j ∈ 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * d k) := fun j hj k => by
    simp only [hdd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q1 j hj).mul (isIntegral_cc α.isIntegral_coe)) ?_
      ring
  have p2 : ∀ j ∈ conjI 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * cc (d k)) := fun j hj k => by
    rw [hcd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q2 j hj).mul α.isIntegral_coe) ?_
      ring
  have hMJ' : (M : 𝓞 E) ∈ conjI 𝔍 := Ideal.subset_span ⟨M, hMJ, by simp [cc]⟩
  have h1 : ∀ j ∈ 𝔍, ∀ v ∈ A, (j : E) • ((s * a : ℕ) : E) • v ∈ stdL E n := fun j hj v hv => by
    have := (mem_stdL _).1 (hΛS _ ((mA v).1 hv))
    refine (mem_stdL _).2 fun k => ?_
    refine int_congr ((p1 j hj k).mul (this k)) ?_
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast
    linear_combination (-((j : E) * a * s * v k)) * hd k
  have h2 : ∀ j ∈ conjI 𝔍, ∀ v ∈ stdL E n, (j : E) • ((s * a : ℕ) : E) • v ∈ A := fun j hj v hv => by
    have := hSΛ (fun k => (j : E) * a * cc (d k) * v k)
      ((mem_stdL _).2 fun k => (p2 j hj k).mul ((mem_stdL _).1 hv k))
    rw [mA]
    convert this using 1
    ext k
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have ht : 0 < s * a := Nat.mul_pos hs ha0
  obtain ⟨C, hC, c1, c2⟩ := patch ht (Nat.Coprime.mul_left hsM haM) 𝔍 (conjI 𝔍) hMJ hMJ' A hA hAsd h1 h2
  refine ⟨C, hC, A, ⟨hA, hAsd, M * (s * a), Nat.mul_pos hM ht, Nat.coprime_one_right _, fun v hv => ?_,
    fun v hv => ?_⟩, fun v => ?_, c1, c2⟩
  · rw [Nat.cast_mul, mul_smul]; simpa using h1 _ hMJ v hv
  · rw [Nat.cast_mul, mul_smul]; simpa using h2 _ hMJ' v hv
  · rw [mA, hh]
    have : (fun k => cc (d k) * (Matrix.diagonal d *ᵥ v) k) = v := by
      ext k; rw [Matrix.mulVec_diagonal, ← _root_.mul_assoc, hd, _root_.one_mul]
    rw [this]

end GlobalTheory.Dict.Patch
end

