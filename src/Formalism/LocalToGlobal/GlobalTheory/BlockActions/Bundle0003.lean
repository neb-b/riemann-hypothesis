module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
public import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.DefNOfFact
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem span_of_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∀ y, ∃ (x : Fin n → E) (s : E), y = A *ᵥ x + s • z := by
  subst hN
  intro y
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  set w := B⁻¹ *ᵥ y with hw
  have hy : B *ᵥ w = y := by rw [hw, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec]
  refine ⟨fun i => w (Fin.castSucc i), w (Fin.last n), ?_⟩
  rw [← hy]
  funext a
  simp only [hBdef, mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  ring

variable (D : D7)

theorem conj_sigD (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x) := by
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram.2.1 φ x

theorem zc_not_range (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXm D *ᵥ x ≠ zc D := by
  letI := D.host.cmStar
  intro h
  have h1 := hform_iXc_zc D x
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  rw [h, zc_eq, hform_crdM] at h1
  exact D.sp.z_anis h1

theorem span_iXc_zc : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D := by
  intro y
  obtain ⟨x, s, h⟩ := span_of_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (zc D) (iXm_mulVec_injective D) (zc_not_range D) y
  refine ⟨x, s, ?_⟩
  rw [h]
  simp only [iXm, LinearMap.toMatrix'_mulVec]

variable {D}

theorem defN_of_fact {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (C : GL (Fin n) D.host.E)
    (hC : cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = J) (φ : D.host.E →+* ℂ) (x : Fin n → D.host.E) :
    ∃ r : ℝ, 0 ≤ r ∧ φ (hform (sigD D : D.host.E →+* D.host.E) J x x) = r ∧ (r = 0 → x = 0) := by
  have e1 : hform (sigD D : D.host.E →+* D.host.E) J x x =
      ∑ a, (sigD D : D.host.E →+* D.host.E) ((C.1 *ᵥ x) a) * (C.1 *ᵥ x) a := by
    rw [← hC, ← Matrix.mul_one (cT (sigD D : D.host.E →+* D.host.E) C.1), ← Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect]
    simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨∑ a, Complex.normSq (φ ((C.1 *ᵥ x) a)), Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [e1, map_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_mul, conj_sigD, Complex.normSq_eq_conj_mul_self]
  · intro h0
    have hz : C.1 *ᵥ x = 0 := by
      funext a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp h0 a (Finset.mem_univ _)
      rw [Complex.normSq_eq_zero, map_eq_zero] at this
      exact this
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    calc x = C.1⁻¹ *ᵥ (C.1 *ᵥ x) := by rw [mulVec_mulVec, nonsing_inv_mul _ hCi, one_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem crdFacts_of (Tf : FormsTiedSym D u Ch chOf) : CrdFacts D := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  exact
    { conj := conj_sigD D
      defN := fun φ x => defN_of_fact (gramN D D.R.m le_rfl) C hC φ x
      iso := hform_iXc D
      orth := fun x => ⟨hform_iXc_zc D x, hform_zc_iXc D x⟩
      span := span_iXc_zc D }

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG
open scoped ComplexOrder

theorem exists_on_of_posDef {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.PosDef) :
    ∃ o : Matrix (Fin k) (Fin k) ℂ, IsUnit o.det ∧ oᴴ * H * o = 1 := by
  classical
  set U : Matrix (Fin k) (Fin k) ℂ := (hH.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.1.eigenvectorUnitary).2
  have hd : star U * H * U = diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) := by
    have h := hH.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hUdef] using h
  let d : Fin k → ℂ := fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hpos : ∀ i, 0 < hH.1.eigenvalues i := fun i => hH.eigenvalues_pos i
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul ?_ (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))
    · have h1 : U.det * (star U).det = 1 := by
        rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem (hH.1.eigenvectorUnitary).2, Matrix.det_one]
      exact ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
    · simp only [d, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
      exact (Real.sqrt_pos.mpr (hpos i)).ne'
  · rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.star_eq_conjTranspose]
    have e : diagonal (star d) * star U * H * (U * diagonal d) = diagonal (star d) * (star U * H * U) * diagonal d := by
      simp only [Matrix.mul_assoc]
    rw [e, hd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hH.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    have hr : (Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ = 1 := by
      rw [mul_comm ((Real.sqrt (hH.1.eigenvalues i))⁻¹) (hH.1.eigenvalues i), mul_assoc, ← mul_inv,
        Real.mul_self_sqrt (hpos i).le, mul_inv_cancel₀ (hpos i).ne']
    have h2 : (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hH.1.eigenvalues i : ℝ) : ℂ) *
        (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    simp only [d, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    exact h2

variable {D : D7}

theorem embT_sig (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem map_cT {m n : Type} (M : Matrix m n D.host.E) (τ : D.what₂.Tau) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [embT_sig]
  rfl


variable (D) in
theorem gramP_eq : gramP D = ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * iXm D := by
  ext a b
  rw [gramOf_apply]
  have hc : ∀ i : Fin (D.R.N D.R.m - 1), (fun k => iXm D k i) = iXc D (Pi.single i 1) := by
    intro i; funext k; simp only [iXm, LinearMap.toMatrix'_apply]
  rw [hc, hc, hform_iXc]
  simp [hform, Pi.single_apply]


variable (D) in
theorem iXm_leftInv : ∃ L : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, L * iXm D = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (iXc D) (LinearMap.ker_eq_bot.mpr (iXc_injective D))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [iXm, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem gramP_posDef {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (τ : D.what₂.Tau) : (gramC (gramP D) (embT D) τ).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map (embT D τ) with hA
  have hG : gramC (gramP D) (embT D) τ = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    simp only [gramC]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map (embT D τ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map (embT D τ)) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem exists_onP {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    ∃ o : FrP D, ∀ τ, (o.1 τ)ᴴ * gramC (gramP D) (embT D) τ * o.1 τ = 1 := by
  have h := fun τ => exists_on_of_posDef (k := D.R.N D.R.m - 1) (gramC (gramP D) (embT D) τ) (gramP_posDef Tf τ)
  choose o ho1 ho2 using h
  exact ⟨⟨o, ho1⟩, ho2⟩

end Formalism.L2.GlobalTheoryTheory.Br
end
end

