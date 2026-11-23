module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ContDiffAtMatmul
section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffAt_mat {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Mat n} {x : E}
    (h : ContDiffAt ℝ ∞ A x) (a b : Fin n) : ContDiffAt ℝ ∞ (fun z => A z a b) x :=
  (entL a b).contDiff.contDiffAt.comp x h

theorem contDiffAt_matmul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → Mat n} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (fun z => A z * B z) x := by
  refine contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (contDiffAt_mat hA a c).mul (contDiffAt_mat hB c b)

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_iff_contDiffAt.2 fun x => contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.comp (contDiff_entry b a)).contDiffAt

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  show (x⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem conjT_mem {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  show (xᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 hx

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hy

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derOne_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    {d y : Mat n} (hd : d ∈ GLs n) (hy : y ∈ GLs n) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    fderiv ℝ (fun x' => Kf Fr k Γ T d x' y) x (x * X) =
      Fr x * (fderiv ℝ Fr 1 X * k (x⁻¹ * d * yᴴ⁻¹) + Ld X k (x⁻¹ * d * yᴴ⁻¹)) * Γ * T * Fr y⁻¹ := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * yᴴ⁻¹) x :=
    contDiffAt_matmul (contDiffAt_matmul (contDiffAt_inv hx) contDiffAt_const) contDiffAt_const
  have hdiff : DifferentiableAt ℝ (fun x' => Kf Fr k Γ T d x' y) x := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun x' : Mat n => k (x'⁻¹ * d * yᴴ⁻¹)) x :=
      hkw.comp x (hg.differentiableAt (by simp))
    exact ((((diffAt_of h.smooth hx).mul h1).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have h1 := hasDerivAt_fderiv_line hdiff (x * X)
  have hF : HasDerivAt (fun t : ℝ => Fr (x * (1 + t • X))) (Fr x * fderiv ℝ Fr 1 X) 0 := by
    refine ((hasDerivAt_Fr_line h X).const_mul (Fr x)).congr_of_eventuallyEq ?_
    filter_upwards [line_mem X] with t ht
    exact h.mul x hx _ ht
  have hc : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹ * w) ((-X) * w) 0 :=
    (hasDerivAt_matmul (hasDerivAt_lineInv X) (hasDerivAt_const (0 : ℝ) w)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k ((1 + t • X)⁻¹ * w)) (fderiv ℝ k w ((-X) * w)) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have h2 := (((hF.fun_mul hK).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have e : (fun t : ℝ => Kf Fr k Γ T d (x + t • (x * X)) y) =
      fun t : ℝ => Fr (x * (1 + t • X)) * k ((1 + t • X)⁻¹ * w) * Γ * T * Fr y⁻¹ := by
    funext t
    have e1 : x + t • (x * X) = x * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    simp only [Kf, e1, Matrix.mul_inv_rev, hwdef, Matrix.mul_assoc]
  rw [e] at h1
  rw [h1.unique h2]
  simp only [zero_smul, add_zero, inv_one, Matrix.one_mul, Matrix.mul_one, Ld, neg_mul, map_neg]
  noncomm_ring

theorem derOne : DerOne := fun _ _ _ _ _ _ _ _ _ h _ hk _ _ hd hy _ hx X => derOne_at h hk hd hy hx X

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.MulMemGLs
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_of (y : G n) : y.val ∈ GLs n := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero

theorem mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem act_congr [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    {F F' : Mat n → E.V} (h : Set.EqOn F F' (GLs n)) {x : Mat n} (hx : x ∈ GLs n) : act μ E k F x = act μ E k F' x := by
  simp only [act]
  exact integral_congr_ae (Eventually.of_forall fun y => by
    show (k y.val) (F (x * y.val)) = (k y.val) (F' (x * y.val))
    rw [h (mul_mem_GLs hx (mem_GLs_of y))])

theorem act_dc (hDW : DCwave) (hP : ParamInt) (hZ : ZopDC) (hG : GelComm) (hWE : WaveEx) {lam : Fin n → ℤ} {E : KMod n}
    {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T' : ℝ) (hgb : IsBump g T') (ks : Mat n → (E.V →L[ℂ] E.V))
    (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (DC ε Fr f) 1 = DC ε Fr (act μ E ks f) 1 := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hDu := hDW hG n lam E Fr ε ι S Γ T hC u hu
  have hk1 := hks.2.2.2 _ hDu 1 h1
  obtain ⟨hPs, hPd⟩ := hP n E u hu g T' hgb
  have eqA : Set.EqOn (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') (GLs n) :=
    fun x hx => param_dc ε Fr u hu.1 g T' hgb hPd x hx
  have hz := hZ hG n lam E Fr ε ι S Γ T hC (fun x' => ∫ t, (g t : ℂ) • u t x') hPs w
  have eqB : Set.EqOn (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') (act μ E ks f) (GLs n) := by
    intro x hx
    rw [← hks.2.2.2 u hu x hx]
    exact act_congr μ E ks (fun y hy => hu0 y hy) hx
  have eq0 : Set.EqOn (DC ε Fr f) (DC ε Fr (u 0)) (GLs n) :=
    dc_congr ε Fr (isOpen_GLs n) fun y hy => (hu0 y hy).symm
  calc act μ E ks (DC ε Fr f) 1 = act μ E ks (DC ε Fr (u 0)) 1 := act_congr μ E ks eq0 h1
    _ = zOp w (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') 1 := hk1
    _ = zOp w (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') 1 := zop_congr (isOpen_GLs n) w eqA h1
    _ = DC ε Fr (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') 1 := hz.2 1 h1
    _ = DC ε Fr (act μ E ks f) 1 := dc_congr ε Fr (isOpen_GLs n) eqB h1

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

