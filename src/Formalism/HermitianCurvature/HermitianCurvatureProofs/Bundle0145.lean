module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRODE
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEigA
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.InvEigA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

def e0A (k r : ℕ) (p : Fin (r + k + 1)) : Fin (2 * r + k + 1) := ⟨p.val, by have := p.isLt; omega⟩

theorem anisotropic_index_injective : Function.Injective (e0A k r) := fun a b h => by
  simp only [e0A, Fin.ext_iff] at h; exact Fin.ext h

theorem sum_embA {a b : ℕ} (f : Fin a → Fin b) (hf : Function.Injective f) (G : Fin b → ℂ)
    (hG : ∀ q, (∀ p, f p ≠ q) → G q = 0) : ∑ p, G (f p) = ∑ q, G q := by
  classical
  calc ∑ p, G (f p) = ∑ q ∈ Finset.univ.map ⟨f, hf⟩, G q := by rw [Finset.sum_map]; rfl
    _ = ∑ q, G q := Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hG q (fun p hp => hq (by
        simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨p, hp⟩)))

theorem hermitian_form_column_vanishes (j y : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) (hy : y.val < r) : Hpk k r y j = 0 := by
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_esI_left (a : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) x = if x = eI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_esI_right (a : Fin r) (y : Fin (2 * r + k + 1)) :
    Hpk k r y (esI k r a) = if y = eI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

variable {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r}

theorem w_colA (hw : w ∈ UWset k r z') (q : Fin (2 * r + k + 1)) (hq : q.val < r) (y : Fin (2 * r + k + 1)) :
    w y q = if y = q then 1 else 0 := by
  have h1 := congrFun (hw.2.1 ⟨q.val, hq⟩).1 y
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rw [e] at h1
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using h1

theorem m_colA (hm : m ∈ Nset k r) (q i : Fin (2 * r + k + 1)) (hq : q.val < r) (hi : q.val ≤ i.val) :
    m i q = if i = q then 1 else 0 := by
  have := hm.2.1 ⟨q.val, hq⟩ i hi
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rwa [e] at this

theorem mw_colXA (hw : w ∈ UWset k r z') (i q : Fin (2 * r + k + 1)) (hq : q.val < r) : (m * w) i q = m i q := by
  rw [Matrix.mul_apply]
  simp only [w_colA hw q hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mw_XA (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i q : Fin (2 * r + k + 1)) (hi : r ≤ i.val)
    (hq : q.val < r) : (m * w) i q = 0 := by
  rw [mw_colXA hw i q hq, m_colA hm q i hq (by omega), if_neg]
  intro h; subst h; omega

theorem mw_zA (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : ((m * w) *ᵥ z') i = z' i := by
  rw [← Matrix.mulVec_mulVec, hw.2.2]
  have e : ∀ j, m i j * z' j = (if i = j then 1 else 0) * z' j := by
    intro j
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [hm.2.2 i j hj.1 hj.2 hi]
    · rw [hz' j (by omega), mul_zero, mul_zero]
  simp only [Matrix.mulVec, dotProduct, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mw_GV (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) : m * w ∈ B.GV k r := WeylGroupFacts.uh_mul hm.1 hw.1

theorem charpoly_eq_of_isIso (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    (m * w)⁻¹ = Hpk k r * (m * w)ᴴ * Hpk k r := Formalism.FourierDecayAlt.P.PBG.inv_GV (mw_GV hw hm)

theorem P_row (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    ((m * w)⁻¹) (esI k r a) j = ∑ y, star ((m * w) y (eI k r a)) * Hpk k r y j := by
  rw [charpoly_eq_of_isIso hw hm, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_apply]
  simp only [hpk_esI_left, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply]

theorem esI_of (i : Fin (2 * r + k + 1)) (hi : r + k < i.val) :
    esI k r ⟨2 * r + k - i.val, by have := i.isLt; omega⟩ = i := by
  ext; simp [esI]; omega

theorem inverse_product_block_zero (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hi : r + k < i.val)
    (hj : j.val ≤ r + k) : ((m * w)⁻¹) i j = 0 := by
  rw [← esI_of i hi, P_row hw hm]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hy : y.val < r
  · rw [hermitian_form_column_vanishes j y hj hy, mul_zero]
  · rw [mw_XA hw hm y _ (by omega) (by simp [eI]; omega), star_zero, zero_mul]

theorem P_XX (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (a b : Fin r) :
    ((m * w)⁻¹) (esI k r a) (esI k r b) = star ((m * w) (eI k r b) (eI k r a)) := by
  rw [P_row hw hm]
  simp only [hpk_esI_right, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem det_inverse_product_block (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    ((m * w)⁻¹).det = (((m * w)⁻¹).submatrix (e0A k r) (e0A k r)).det := by
  classical
  set P := (m * w)⁻¹ with hP
  rw [Matrix.twoBlockTriangular_det P (fun i : Fin (2 * r + k + 1) => i.val ≤ r + k)
    (fun i hi j hj => inverse_product_block_zero hw hm i j (by omega) hj)]
  have e1 : (P.toSquareBlockProp fun i : Fin (2 * r + k + 1) => i.val ≤ r + k).det =
      (P.submatrix (e0A k r) (e0A k r)).det := by
    let e : Fin (r + k + 1) ≃ {i : Fin (2 * r + k + 1) // i.val ≤ r + k} :=
      { toFun := fun p => ⟨e0A k r p, by simp [e0A]; omega⟩
        invFun := fun i => ⟨i.1.val, by have := i.2; omega⟩
        left_inv := fun p => by ext; simp [e0A]
        right_inv := fun i => by ext; simp [e0A] }
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  have e2 : (P.toSquareBlockProp fun i : Fin (2 * r + k + 1) => ¬ i.val ≤ r + k).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one (fun i _ => ?_)
      obtain ⟨i, hi⟩ := i
      have hi' : r + k < i.val := by omega
      show P i i = 1
      rw [← esI_of i hi', hP, P_XX hw hm, mw_colXA hw _ _ (by simp [eI]; omega),
        m_colA hm _ _ (by simp [eI]; omega) le_rfl, if_pos rfl, star_one]
    · intro i j hij
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      have hi' : r + k < i.val := by omega
      have hj' : r + k < j.val := by omega
      have hlt : j.val < i.val := hij
      show P i j = 0
      rw [← esI_of i hi', ← esI_of j hj', hP, P_XX hw hm, mw_colXA hw _ _ (by simp [eI]; omega),
        m_colA hm _ _ (by simp [eI]; omega) (by simp [eI]; omega), if_neg (by simp [eI, Fin.ext_iff]; omega),
        star_zero]
  rw [e1, e2, mul_one]

theorem herm_bvec (z' : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec x) z' = (star z' ᵥ* Hpk k r) x := by
  simp only [herm, bvec, Matrix.mulVec, dotProduct, Matrix.vecMul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem zeta_full (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (j : Fin (2 * r + k + 1))
    (hj : j.val ≤ r + k) : ((star z' ᵥ* Hpk k r) ᵥ* (m * w)⁻¹) j = (star z' ᵥ* Hpk k r) j := by
  rw [charpoly_eq_of_isIso hw hm, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Qx2.hpk_sq',
    Matrix.one_mul, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec]
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases hl : l.val < r
  · rw [hermitian_form_column_vanishes j l hj hl, mul_zero, mul_zero]
  · rw [Pi.star_apply, Pi.star_apply, mw_zA hz' hw hm l (by omega)]

theorem zeta_fix (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    (fun p => herm (Hpk k r) (bvec (e0A k r p)) z') ᵥ* (((m * w)⁻¹).submatrix (e0A k r) (e0A k r)) =
      fun p => herm (Hpk k r) (bvec (e0A k r p)) z' := by
  funext q
  have hq : (e0A k r q).val ≤ r + k := by simp [e0A]; omega
  rw [herm_bvec, ← zeta_full hz' hw hm _ hq]
  simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, herm_bvec]
  refine sum_embA (e0A k r) anisotropic_index_injective (fun x => (star z' ᵥ* Hpk k r) x * ((m * w)⁻¹) x (e0A k r q)) (fun x hx => ?_)
  have : r + k < x.val := by
    by_contra hc
    exact hx ⟨x.val, by omega⟩ (Fin.ext (by simp [e0A]))
  show (star z' ᵥ* Hpk k r) x * ((m * w)⁻¹) x (e0A k r q) = 0
  rw [inverse_product_block_zero hw hm x _ this hq, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.InvEigA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHBTl
section
namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem boundary_torus_adjoin : CutSH.BTlAdjoin := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' X L hX S _ _ l w a b
  set Qa : Subalgebra ℂ (Module.End ℂ (RadSp k r z z' π π')) := Algebra.adjoin ℂ (Set.range (X.op l)) with hQa
  let good : Pr (RadSp k r z z' π π') → Prop := fun x => x.1 ∈ Qa ∧ x.2.unop ∈ Qa
  have hop : ∀ i, X.op l i ∈ Qa := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  have gmul : ∀ x y, good x → good y → good (x * y) := fun x y hx hy =>
    ⟨Subalgebra.mul_mem _ hx.1 hy.1, Subalgebra.mul_mem _ hy.2 hx.2⟩
  have gadd : ∀ x y, good x → good y → good (x + y) := fun x y hx hy =>
    ⟨Subalgebra.add_mem _ hx.1 hy.1, Subalgebra.add_mem _ hx.2 hy.2⟩
  have gneg : ∀ x, good x → good (-x) := fun x hx => ⟨Subalgebra.neg_mem _ hx.1, Subalgebra.neg_mem _ hx.2⟩
  have gzero : good 0 := ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  have gone : good 1 := ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
  have gstar : ∀ x, good x → good (star x) := fun x hx => ⟨hx.2, hx.1⟩
  have galg : ∀ c : ℂ, good (algebraMap ℂ (Pr (RadSp k r z z' π π')) c) := fun c =>
    ⟨Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ (starRingEnd ℂ c)⟩
  have gp : good (L.p l) := by
    rw [hX.1 l]
    exact ⟨hop 0, Subalgebra.neg_mem _ (hop 3)⟩
  have gc : good (L.c l) := by
    rw [hX.2.2.1 l]
    exact ⟨hop 1, hop 4⟩
  have gci : good (L.ci l) := by
    rw [hX.2.2.2.1 l]
    exact ⟨hop 2, hop 5⟩
  have hTs : ∀ (Y : ℂ) (i j : Fin 2), good ((Wd.Ts (site L l) Y) i j) := by
    intro Y i j
    fin_cases i <;> fin_cases j <;>
      simp only [Wd.Ts, site, Formalism.YangianSpanCharacter.T.Tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one]
    · exact gadd _ _ (galg Y) gp
    · exact gneg _ gc
    · exact gci
    · exact gzero
  have hmulA : ∀ M N : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')), (∀ a b, good (M a b)) → (∀ a b, good (N a b)) →
      ∀ a b, good ((M * N) a b) := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    refine Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun c _ => ?_)
    exact gmul _ _ (hM a c) (hN c b)
  have hsumA : ∀ (ι : Type) (t : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))),
      (∀ i, ∀ a b, good (f i a b)) → ∀ a b, good ((∑ i ∈ t, f i) a b) := by
    intro ι t f hf a b
    rw [Matrix.sum_apply]
    exact Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun i _ => hf i a b)
  have heU : ∀ (x : S) (i j : Fin 2), ∀ a b, good ((Wd.eU (A := Pr (RadSp k r z z' π π')) x i j : Wd.SlopeTestRemainingChoices S _) a b) := by
    intro x i j a b
    unfold Wd.eU
    simp only [Matrix.of_apply]
    split_ifs
    · exact gone
    · exact gzero
  have hio : ∀ y, good y → ∀ a b, good ((Wd.io (S := S) y) a b) := by
    intro y hy a b
    unfold Wd.io
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hy
    · exact gzero
  have hvlet : ∀ lt : Wd.Letter ℂ S, ∀ a b, good ((Wd.vlet (site L l) lt) a b) := by
    intro lt
    unfold Wd.vlet Wd.ins
    refine hsumA _ _ _ (fun i => ?_)
    refine hsumA _ _ _ (fun j => ?_)
    refine hmulA _ _ (heU _ i j) ?_
    intro a b
    unfold Wd.lift0
    rw [Matrix.map_apply]
    refine hio _ ?_ a b
    split_ifs
    · exact hTs _ i j
    · rw [Matrix.map_apply]
      exact gstar _ (hTs _ i j)
  have hbT : ∀ w' : List (Wd.Letter ℂ S), ∀ a b, good ((Wd.bT (site L l) w') a b) := by
    intro w'
    induction w' with
    | nil =>
      intro a b
      simp only [Wd.bT]
      rw [Matrix.one_apply]
      split_ifs
      · exact gone
      · exact gzero
    | cons lt w' ih =>
      intro a b
      simp only [Wd.bT]
      exact hmulA _ _ (hvlet lt) ih a b
  exact (hbT w a b).1

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
section
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_algebraic : FamAlg := by
  intro Wp Wq _ _ _ _ _ _ P T j G G' hG hG' m hm
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨hG1', hG2'⟩ := hG'
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    obtain ⟨U', f', hU', hmem', hf', hfe'⟩ := hG1' t₀ ht₀ γ₀ hγ₀
    refine ⟨U ∩ U', fun p => f p + f' p, hU.inter hU', ⟨hmem, hmem'⟩,
      (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), ?_⟩
    intro p hp hpG
    simp only [hfe p hp.1 hpG, hfe' p hp.2 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    obtain ⟨C', hC', ε', hε', hCε'⟩ := hG2' K hK hK0
    refine ⟨C ∪ C', hC.union hC', min ε ε', lt_min hε hε', ?_⟩
    intro t ht γ hne
    by_cases h0 : G t γ = 0
    · have h1 : G' t γ ≠ 0 := by
        intro h1; apply hne; simp [h0, h1]
      obtain ⟨hγ, hb⟩ := hCε' t ht γ h1
      exact ⟨Or.inr hγ, fun hg => (min_le_right _ _).trans (hb hg)⟩
    · obtain ⟨hγ, hb⟩ := hCε t ht γ h0
      exact ⟨Or.inl hγ, fun hg => (min_le_left _ _).trans (hb hg)⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    have hO : IsOpen {p : ℂ × B.Mat P.k (P.r - (j + 1)) | p.1 ≠ 0} :=
      isOpen_ne_fun continuous_fst continuous_const
    refine ⟨U ∩ {p | p.1 ≠ 0}, fun p => m p.1 • f p, hU.inter hO, ⟨hmem, ht₀⟩, ?_, ?_⟩
    · have hm' : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => m p.1) (U ∩ {p | p.1 ≠ 0}) :=
        hm.comp contDiffOn_fst (fun p hp => hp.2)
      exact hm'.smul (hf.mono Set.inter_subset_left)
    · intro p hp hpG
      simp only [hfe p hp.1 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    exact ⟨C, hC, ε, hε, fun t ht γ hne => hCε t ht γ (right_ne_zero_of_smul hne)⟩

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamDeriv
section
open MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_derivative : CutSH.FamDeriv := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG v
  obtain ⟨hloc, hsupp⟩ := hG
  refine ⟨?_, ?_⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hGf⟩ := hloc t₀ ht₀ γ₀ hγ₀
    refine ⟨U, fun p => fderiv ℝ f p ((v, 0) : ℂ × B.Mat P.k (P.r - (j + 1))), hU, hmem, ?_, ?_⟩
    · exact (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    · rintro ⟨t, γ⟩ hp hγ
      simp only [famP, Set.indicator_of_mem hγ]
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun u => f (u, γ) := by
        have hc : Continuous fun u : ℂ => (u, γ) := continuous_id.prodMk continuous_const
        have : ∀ᶠ u in 𝓝 t, (u, γ) ∈ U := hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
        filter_upwards [this] with u hu
        exact hGf (u, γ) hu hγ
      rw [hev.fderiv_eq]
      have hfd : DifferentiableAt ℝ f (t, γ) :=
        (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      have hin := hasFDerivAt_prodMk_left (𝕜 := ℝ) t γ
      rw [show (fun u : ℂ => f (u, γ)) = f ∘ fun u => (u, γ) from rfl, (hfd.hasFDerivAt.comp t hin).fderiv]
      rfl
  · intro K hK hK0
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_compl_singleton (x := (0 : ℂ)))
      (fun t ht => by simpa using hK0 t ht)
    obtain ⟨C, hC, ε, hε, hCε⟩ := hsupp (Metric.cthickening δ K) hK.cthickening
      (fun t ht => by simpa using hsub ht)
    refine ⟨C, hC, ε, hε, fun t ht γ hne => ?_⟩
    have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
      by_contra h
      exact hne (by simp [famP, Set.indicator_of_notMem h])
    have hd : fderiv ℝ (fun u : ℂ => G u γ) t v ≠ 0 := by
      simpa [famP, Set.indicator_of_mem hγ] using hne
    have hex : ∃ u ∈ Metric.ball t δ, G u γ ≠ 0 := by
      by_contra hno
      push Not at hno
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds t hδ] with u hu using hno u hu
      exact hd (by rw [hev.fderiv_eq]; simp)
    obtain ⟨u, hu, hGu⟩ := hex
    have huK : u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le u t δ K ht (le_of_lt (Metric.mem_ball.mp hu))
    obtain ⟨hγC, hε'⟩ := hCε u huK γ hGu
    exact ⟨hγC, fun _ => hε' hγ⟩

end Formalism.FourierDecayAlt.P
end
end

