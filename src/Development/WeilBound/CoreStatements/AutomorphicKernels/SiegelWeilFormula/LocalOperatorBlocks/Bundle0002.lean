module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal
section
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

theorem fP_add_smul (a : ℂ) (P Q : PX m n) : fP (a • P + Q) = a • fP P + fP Q := by
  funext u
  simp [fP, evX, MvPolynomial.eval_add, MvPolynomial.smul_eval, add_mul, mul_assoc]

theorem fP_zero : fP (0 : PX m n) = 0 := by
  funext u
  simp [fP, evX]

theorem fP_one_zero : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

section Real

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (AddMonoidAlgebra.coeff p k).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (AddMonoidAlgebra.coeff p k).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) k = (AddMonoidAlgebra.coeff p k).re := by
  classical
  rw [reP, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_re]

theorem coeff_imP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) k = (AddMonoidAlgebra.coeff p k).im := by
  classical
  rw [imaginary, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_im]

theorem eval_map_real (q : MvPolynomial σ ℝ) (y : σ → ℝ) :
    MvPolynomial.eval (fun i => (y i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) q) = ((MvPolynomial.eval y q : ℝ) : ℂ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = MvPolynomial.map (algebraMap ℝ ℂ) (reP p) + MvPolynomial.C Complex.I * MvPolynomial.map (algebraMap ℝ ℂ) (imaginary p) := by
  ext k
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_reP,
    coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, MvPolynomial.eval (fun i => (y i : ℂ)) p = 0) :
    p = 0 := by
  have hre : ∀ y : σ → ℝ, MvPolynomial.eval y (reP p) = 0 ∧ MvPolynomial.eval y (imaginary p) = 0 := by
    intro y
    have h1 := h y
    rw [eq_map_re_add_im p, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h1
    rw [eval_map_real, eval_map_real] at h1
    have hr := congrArg Complex.re h1
    have hi := congrArg Complex.im h1
    simp at hr hi
    exact ⟨hr, hi⟩
  have a1 : reP p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).1
  have a2 : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).2
  rw [eq_map_re_add_im p, a1, a2]
  simp

end Real

def subF (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)
  else MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)

def subG (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.X (k.1, k.2.1, true))
  else MvPolynomial.C (2 : ℂ)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.X (k.1, k.2.1, true))

theorem subG_subF (P : PX m n) : MvPolynomial.bind₁ subG (MvPolynomial.bind₁ subF P) = P := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x _ = MvPolynomial.aeval x P
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have e : (fun i => MvPolynomial.aeval (fun i => MvPolynomial.aeval x (subG (m := m) (n := n) i)) (subF i)) = x := by
    funext k
    obtain ⟨a, j, b⟩ := k
    cases b <;> simp [subF, subG] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [e]

theorem evX_injective : Function.Injective (evX (m := m) (n := n)) := by
  intro P Q h
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : ∀ x, evX R x = 0 := fun x => by
    simp only [R, evX, map_sub]; exact sub_eq_zero.2 (congrFun h x)
  have h0 : MvPolynomial.bind₁ subF R = 0 := by
    apply eq_zero_of_eval_real
    intro y
    change MvPolynomial.aeval (fun i => (y i : ℂ)) _ = 0
    rw [MvPolynomial.aeval_bind₁]
    have := hR (fun a j => (y (a, j, false) : ℂ) + Complex.I * y (a, j, true))
    rw [evX] at this
    have e : (fun i => MvPolynomial.aeval (fun i => (y i : ℂ)) (subF (m := m) (n := n) i)) =
        fun k => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true))
          else (y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true) := by
      funext k
      obtain ⟨a, j, b⟩ := k
      cases b <;> simp [subF, Complex.ext_iff]
    rw [e]
    exact this
  rw [← subG_subF R, h0, map_zero]

theorem fP_injective : Function.Injective (fP (m := m) (n := n)) := by
  intro P Q h
  apply evX_injective
  funext u
  have e := congrFun h u
  simp only [fP] at e
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) e

theorem isSw_fP (P : PX m n) : IsSw (fP P) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss m n P
  exact ⟨φ, hφ⟩

theorem fP_eq_gZ (sg : ℤˣ) (P : PX m n) :
    fP P = fun u => evX P u * gZ sg ((Complex.I * ((sg : ℤ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
  funext u
  simp only [fP, gs, gZ]
  congr 2
  have htr : Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hI : Complex.I * ((sg : ℤ) : ℂ) * (Complex.I * ((sg : ℤ) : ℂ)) = -1 := by
    rcases Int.units_eq_one_or sg with rfl | rfl <;> simp
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr, smul_eq_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (-2 * (Real.pi : ℂ) * ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)) * hI

theorem fin_deg (d : ℕ) : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d) :=
  inferInstance

def evW (d : ℕ) : MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d →ₗ[ℂ] ((Fin m → Fin n → ℂ) → ℂ) where
  toFun Q u := evX Q.1 u
  map_add' Q Q' := by funext u; simp [evX]
  map_smul' a Q := by funext u; simp [evX]

theorem evW_injective (d : ℕ) : Function.Injective (evW (m := m) (n := n) d) := fun Q Q' h =>
  Subtype.ext (evX_injective (funext fun u => congrFun h u))

theorem continuousOn_of_evX {X : Type} [TopologicalSpace X] {S : Set X} (d : ℕ) (φ : X → PX m n)
    (hd : ∀ x ∈ S, (φ x).totalDegree ≤ d) (hc : ∀ u, ContinuousOn (fun x => evX (φ x) u) S) (l : PX m n →ₗ[ℂ] ℂ) :
    ContinuousOn (fun x => l (φ x)) S := by
  classical
  set W := MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d
  let e : W ≃ₗ[ℂ] LinearMap.range (evW (m := m) (n := n) d) := LinearEquiv.ofInjective _ (evW_injective d)
  haveI : FiniteDimensional ℂ (LinearMap.range (evW (m := m) (n := n) d)) := e.finiteDimensional
  let l' : LinearMap.range (evW (m := m) (n := n) d) →ₗ[ℂ] ℂ := l ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hl' : Continuous l' := LinearMap.continuous_of_finiteDimensional l'
  have hW : ∀ x ∈ S, φ x ∈ W := fun x hx => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd x hx)
  rw [continuousOn_iff_continuous_restrict]
  let g : S → LinearMap.range (evW (m := m) (n := n) d) := fun x => e ⟨φ x, hW x x.2⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun u => ?_
    exact (hc u).restrict
  refine (hl'.comp hg).congr fun x => ?_
  simp [l', g]

theorem gramX_true (x : Fin m → Fin n → ℂ) : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
  ext i j
  simp [gramX, Qp, Qb, evX, Matrix.mul_apply, Matrix.conjTranspose_apply, MvPolynomial.eval_sum]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IntegrandMono
section
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex MvPolynomial

theorem evX_monomial (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (v : Fin m → Fin n → ℂ) :
    evX (monomial e c) v = c * ∏ a, ∏ j, (v a j ^ e (a, j, false) * star (v a j) ^ e (a, j, true)) := by
  simp only [evX, MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine congrArg _ (Finset.prod_congr rfl fun a _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem gZ_diag (sg : ℤˣ) (w : Fin n → ℂ) (v : Fin m → Fin n → ℂ) :
    gZ sg (Matrix.diagonal w) v =
      ∏ a, ∏ j, cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * w j * (normSq (v a j) : ℂ)) := by
  unfold gZ
  have h : (Matrix.diagonal w * ((Matrix.of v)ᴴ * Matrix.of v)).trace =
      ∑ a, ∑ j, w j * (normSq (v a j) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag]
    simp only [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ring

def ker (t : ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  cexp (2 * Real.pi * I * ((t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ))

theorem ker_prod (t : ℂ) (u v : Fin m → Fin n → ℂ) :
    ker t u v = ∏ a, ∏ j, cexp (2 * Real.pi * I * ((t * (star (u a j) * v a j)).re : ℂ)) := by
  unfold ker
  have h : t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) =
      ∑ a, ∑ j, t * (star (u a j) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem integrand_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ)
    (u v : Fin m → Fin n → ℂ) :
    ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) := by
  rw [ker_prod, evX_monomial, gZ_diag]
  simp only [phi1, Finset.prod_mul_distrib]
  ring

theorem intg_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (u : Fin m → Fin n → ℂ) :
    Integrable (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) := by
  have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
      fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
    funext fun v => integrand_mono sg t z e c u v
  rw [h]
  refine Integrable.const_mul ?_ c
  exact Integrable.fintype_prod
    (f := fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))
    fun a => Integrable.fintype_prod
      (f := fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)
      fun j => integrable_gaussian_moment sg t (z j) (u a j) (hz j) _ _

def rn (a : Fin m) (j : Fin n) (q : MvPolynomial Bool ℂ) : PX m n := rename (fun b => (a, j, b)) q

theorem four_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) :
    ∃ Q : PX m n, Q.totalDegree ≤ e.sum (fun _ k => k) ∧ ∀ u, ∫ v : Fin m → Fin n → ℂ,
      ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      evX Q u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u := by
  choose q hqd hq using fun (a : Fin m) (j : Fin n) =>
    mom1 sg t (z j) (hz j) (e (a, j, false)) (e (a, j, true))
  refine ⟨MvPolynomial.C c * ∏ a, ∏ j, rn a j (q a j), ?_, fun u => ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Fintype.sum_bool]
    exact ((MvPolynomial.totalDegree_rename_le _ _).trans (hqd a j)).trans (le_of_eq (add_comm _ _))
  · have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
        fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
      funext fun v => integrand_mono sg t z e c u v
    have hin : ∀ a, ∫ w : Fin n → ℂ, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j) =
        ∏ j, ((MvPolynomial.eval fun b : Bool => if b = true then star (u a j) else u a j) (q a j) *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * (z j)⁻¹) * (normSq (u a j) : ℂ))) := by
      intro a
      rw [integral_fintype_prod_volume_eq_prod
        (fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)]
      exact Finset.prod_congr rfl fun j _ => hq a j (u a j)
    rw [h, integral_const_mul, integral_fintype_prod_volume_eq_prod
      (fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))]
    simp only [hin, gZ_diag]
    simp only [evX, map_mul, map_prod, MvPolynomial.eval_C, rn, MvPolynomial.eval_rename,
      Function.comp_def, Finset.prod_mul_distrib]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end
end

