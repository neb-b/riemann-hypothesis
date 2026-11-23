module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA
section
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcH

variable {m n : ℕ}

def vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : Fin m → Fin n → ℂ :=
  fun a j => u a j * (Real.exp (s * X j) : ℂ)

def crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ℂ := if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1

theorem evX_eq (P : PX m n) (v : Fin m → Fin n → ℂ) : evX P v = MvPolynomial.eval (crd v) P := rfl

theorem crd_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    crd (vS u X s) k = crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) := by
  unfold crd vS
  split_ifs
  · rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_expX (x s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (s * x) : ℝ) : ℂ)) ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) s := by
  have h := ((hasDerivAt_id s).mul_const x).exp
  simp only [id, one_mul] at h
  have h2 := h.ofReal_comp
  have e : ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) = ((Real.exp (s * x) * x : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact h2

theorem crd_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    HasDerivAt (fun s : ℝ => crd (vS u X s) k) ((X k.2.1 : ℂ) * crd (vS u X s) k) s := by
  have h := (hasDerivAt_expX (X k.2.1) s).const_mul (crd u k)
  have e1 : (fun s : ℝ => crd (vS u X s) k) = fun s => crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) :=
    funext fun s => crd_vS u X k s
  rw [e1, crd_vS]
  exact h.congr_deriv (by ring)

theorem pderiv_mul_X (p : PX m n) (k i : Fin m × Fin n × Bool) :
    pderiv i (p * MvPolynomial.X k) = pderiv i p * MvPolynomial.X k + if i = k then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp [add_comm, mul_comm]
  · simp [h, Ne.symm h, mul_comm]

theorem eval_hasDeriv (P : PX m n) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => evX P (vS u X s))
      (∑ k, evX (pderiv k P) (vS u X s) * ((X k.2.1 : ℂ) * crd (vS u X s) k)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [evX_eq, eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [evX_eq, map_add (f := _), add_mul, Finset.sum_add_distrib] at *
    exact hp.add hq
  | mul_X p k hp =>
    have h := hp.mul (crd_hasDeriv u X k s)
    simp only [evX_eq] at *
    have efun : (fun s : ℝ => eval (crd (vS u X s)) (p * MvPolynomial.X k)) =
        fun s => eval (crd (vS u X s)) p * crd (vS u X s) k := by
      funext s'; simp [eval_mul, eval_X]
    rw [efun]
    refine h.congr_deriv ?_
    symm
    set D : Fin m × Fin n × Bool → ℂ := fun i => (X i.2.1 : ℂ) * crd (vS u X s) i with hD
    calc (∑ i, eval (crd (vS u X s)) (pderiv i (p * MvPolynomial.X k)) * D i)
        = ∑ i, (eval (crd (vS u X s)) (pderiv i p) * D i * crd (vS u X s) k +
            (if i = k then eval (crd (vS u X s)) p * D i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pderiv_mul_X]
          split_ifs with hik
          · simp [eval_mul, eval_X]; ring
          · simp [eval_mul, eval_X]; ring
      _ = (∑ i, eval (crd (vS u X s)) (pderiv i p) * D i) * crd (vS u X s) k + eval (crd (vS u X s)) p * D k := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq']
          simp

theorem crd_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, false) = v a j := rfl

theorem crd_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, true) = star (v a j) := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X P) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX P v +
      ∑ k, evX (pderiv k P) v * ((X k.2.1 : ℂ) * crd v k) -
      (2 * c : ℂ) * (∑ a, ∑ j, (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX P v := by
  have hnorm : ∀ a j, ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) := by
    intro a j
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
    Derivation.coeFn_coe, evX_eq, map_sum, map_add, map_sub, map_mul, MvPolynomial.smul_eval, eval_X, smul_eq_mul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, crd_false, crd_true, hnorm]
  set E := (eval (crd v)) P with hE
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (eval (crd v)) ((pderiv (a, j, true)) P) * ((X j : ℂ) * star (v a j)) +
        (eval (crd v)) ((pderiv (a, j, false)) P) * ((X j : ℂ) * v a j)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (X j : ℂ) * (v a j * star (v a j)))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end DCalcH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAwayA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DA

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply GlobalTheory.AdelicU.matHom_injective
  exact Units.ext e

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (A B : Mx D k k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  unfold compAt
  exact Matrix.map_one _ (by simp) (by simp)

theorem finMap_mul {k : ℕ} (A B : Mx D k k) : (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) :=
  Matrix.map_mul (f := finPart D)

theorem compAt_conjT (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {k : ℕ} (A : Mx D k k) :
    compAt θ τ (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) A) = (compAt θ τ A)ᴴ := by
  ext i j
  simp only [compAt, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_Jst (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ ((Jst D n).map (incA D)) = reidx (JJ n) := by
  ext i j
  simp only [compAt, Matrix.map_apply]
  rw [(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1]
  simp only [Jst, blk4, reidx, JJ, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with a | a <;> rcases h2 : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite]

end PositivityTheory.Rg.Sw.Glob.DA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfInG
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

theorem det_JJ_ne : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg] at this
  simp at this

theorem det_ne_of_inG {g : M2 n} (h : InG g) : g.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact det_JJ_ne this.symm

def mkG (g : M2 n) (h : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG h), h⟩

@[simp] theorem mR_mkG (g : M2 n) (h : InG g) : mR (mkG g h) = g := rfl

theorem inG_nU (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : InG (nU b) := by
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]

theorem inG_nbar (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) : InG (nbar c) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]

theorem inG_mM (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  simp [InG, mM, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ ha]

def kth (θ : Fin n → ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ)) (diagonal fun j => (Real.sin (θ j) : ℂ))
    (-diagonal fun j => (Real.sin (θ j) : ℂ)) (diagonal fun j => (Real.cos (θ j) : ℂ))

theorem inK_kth (θ : Fin n → ℝ) : InK (kth θ) := by
  have hcs : ∀ j : Fin n, (Real.cos (θ j) : ℂ) * Real.cos (θ j) + (Real.sin (θ j) : ℂ) * Real.sin (θ j) = 1 := by
    intro j
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  have hsc : ∀ j : Fin n, (Real.sin (θ j) : ℂ) * Real.sin (θ j) + (Real.cos (θ j) : ℂ) * Real.cos (θ j) = 1 := by
    intro j
    rw [add_comm]
    exact hcs j
  refine ⟨?_, ?_⟩
  · simp [InG, kth, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    refine ⟨?_, ?_, ?_⟩
    · funext i
      rw [Pi.zero_apply]
      ring
    · ext i j
      rw [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs
      · linear_combination -(hcs i)
      · simp
    · funext i
      rw [Pi.zero_apply]
      ring
  · simp [kth, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    have h0 : (Matrix.diagonal fun i : Fin n => (Real.cos (θ i) : ℂ) * Real.sin (θ i) +
        -((Real.sin (θ i) : ℂ) * Real.cos (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    have h1 : (Matrix.diagonal fun i : Fin n => (Real.sin (θ i) : ℂ) * Real.cos (θ i) +
        -((Real.cos (θ i) : ℂ) * Real.sin (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    rw [h0, h1, Matrix.fromBlocks_one]

end PositivityTheory.Rg.Sw.Glob.VacB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {m n : ℕ}

theorem evX_Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) (u : Fin m → Fin n → ℂ) :
    evX (Qb ε b i j) u = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evX, Qb, map_sum]

theorem gramB_apply (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramB ε b u i j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := evX_Qb ε b i j u

theorem gramB_not (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB (fun a => !ε a) b u = gramB ε (!b) u := by
  ext i j
  simp only [gramB_apply]
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  cases ε a <;> cases b <;> simp

theorem gramX_eq (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) :
    gramX ε u = gramB ε true u - gramB ε false u := by
  ext i j
  simp [gramX, gramB, Qp, evX, map_sub]

private theorem gramB_eq_conjTranspose_diagonal_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB ε b u = (Matrix.of u)ᴴ * diagonal (fun a => if ε a = b then (1 : ℂ) else 0) * Matrix.of u := by
  ext i j
  simp [gramB_apply, Matrix.mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]

theorem gramB_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    gramB ε b (Matrix.of u * a) = aᴴ * gramB ε b u * a := by
  rw [gramB_eq_conjTranspose_diagonal_mul ε b u]
  refine (gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_
  change (Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem epsT_pos {t : ℝ} (ht : 0 < t) (ε : Fin m → Bool) : epsT t ε = ε := by
  funext a; simp [epsT, ht]

theorem epsT_nonpos {t : ℝ} (ht : ¬ 0 < t) (ε : Fin m → Bool) : epsT t ε = fun a => !ε a := by
  funext a; simp [epsT, ht]

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  simp only [cnt]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simpa using this

theorem chN_mul_gZf (ε : Fin m → Bool) {t c : ℝ} (htc : |t| = c) (b Z : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : chN ε t b u * gZf ε t c Z u = gZf ε t c (Z + b) u := by
  unfold chN gZf
  rw [← Complex.exp_add]
  congr 1
  rw [gramX_eq, conjTranspose_add, hb]
  by_cases ht : 0 < t
  · rw [epsT_pos ht]
    have htc' : t = c := by rw [← htc, abs_of_pos ht]
    subst htc'
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  · rw [epsT_nonpos ht, gramB_not, gramB_not]
    have htc' : t = -c := by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]
    subst htc'
    simp only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.ofReal_neg]
    ring

theorem trace_cyc (Z a G : Matrix (Fin n) (Fin n) ℂ) : (Z * (aᴴ * G * a)).trace = (a * Z * aᴴ * G).trace := by
  rw [show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gZf_mul (ε : Fin m → Bool) (t c : ℝ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZf ε t c Z (Matrix.of u * a) = gZf ε t c (a * Z * aᴴ) u := by
  unfold gZf
  rw [gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocMul
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locMul_of : TensInj → LocMul := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y y' f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  have hf' := hL.1 y' f hf
  rw [← hL.2 (y * y') Ψ hΨ f hf, ← hL.2 y Ψ hΨ _ hf', map_mul, map_mul, Module.End.mul_apply]
  congr 2
  apply Subtype.ext
  exact hL.2 y' Ψ hΨ f hf

end PositivityTheory.Rg.Sw.Glob
end
end

