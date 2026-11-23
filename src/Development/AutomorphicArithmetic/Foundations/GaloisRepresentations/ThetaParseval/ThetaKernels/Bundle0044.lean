module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinGsT
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem T_add_k (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, ← map_add (f := _)]
  congr 1
  funext z
  exact mul_add _ _ _
variable (d) in
abbrev firstFrameColumns : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₁
theorem split_k (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    u = (u * (incM F (d.b⁻¹).1)ᵀ).toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ + (u * (incM F (d.b⁻¹).1)ᵀ).toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ := by
  have e : incM F d.b.1 = Matrix.fromCols (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d) (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns, _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, ← Matrix.fromCols_toCols d.b.1]; ext i (j | j) <;> rfl
  have e1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one,
      Matrix.transpose_one]
  calc u = u * (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    _ = _ := by
      rw [e, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (u * (incM F (d.b⁻¹).1)ᵀ), Matrix.fromCols_mul_fromRows,
        Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
theorem firstColumns_eq_diag_mul : ∃ t : Matrix (Fin d.n) (Fin d.n) (AE F E), _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * t := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  refine ⟨incM F t.1, ?_⟩
  have h2 : ∀ i j, d.b.1 i (Sum.inl j) = ∑ k, (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) i k * t.1 k j :=
    fun i j => congrFun₂ ht i j
  ext i j
  rw [Matrix.mul_apply]
  change inclR (AF F) (d.b.1 i (Sum.inl j)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  rcases i with i | i <;>
  · change inclR (AF F) ((1 : Matrix (Fin d.n) (Fin d.n) E) i k) = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
def vacF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, gs (2 * Real.pi) (R.loc w X)) * g fun k => (d.crd X k).2
theorem cw_add_smul_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    d.cw w (X + realAd F t • Z) = d.cw w X + (t : ℂ) • d.cw w Z := by
  ext i j
  show piInf (d.B.emb w) ((X + realAd F t • Z) i j) = piInf (d.B.emb w) (X i j) + (t : ℂ) * piInf (d.B.emb w) (Z i j)
  rw [Matrix.add_apply, Matrix.smul_apply, map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul]
theorem crd_add_smul_snd_k (X Z : Mx F E d.m d.n) (t : ℝ) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (X + realAd F t • Z) k).2 = (d.crd X k).2 := by
  have e : d.crd (X + realAd F t • Z) k = d.crd X k + realAd F t * d.crd Z k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [e, snd_add_realAd]
def qL_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Z : Mx F E d.m d.n) (t : ℝ) : ℝ :=
  ∑ w, ∑ a, ∑ i, ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2
theorem gs_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    gs (2 * Real.pi) (R.loc w (X + realAd F t • Z)) = Complex.exp ((-(2 * Real.pi * ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) : ℝ) : ℂ) := by
  simp only [gs, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KK.cw_add_smul_k, Matrix.mul_add, Matrix.mul_smul, Matrix.map_apply, norm_star, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]
theorem vacF_line_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) (t : ℝ) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z) = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, _root_.PositivityTheory.SiegelWeilFormula.KK.crd_add_smul_snd_k, _root_.PositivityTheory.SiegelWeilFormula.KK.gs_loc_k]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vacF_deriv_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z))
      (((-(4 * Real.pi) * ∑ w, (Matrix.trace ((((R.fr w)⁻¹).1 * d.cw w X)ᴴ * (((R.fr w)⁻¹).1 * d.cw w Z))).re : ℝ) : ℂ) *
        _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X) 0 := by
  have hf : (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z)) =
      fun t => Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 :=
    funext (_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z)
  rw [hf]
  have hq : HasDerivAt (_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z)
      (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k
    refine HasDerivAt.fun_sum (A := fun w (t : ℝ) => ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun w _ => ?_
    refine HasDerivAt.fun_sum (A := fun a (t : ℝ) => ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun a _ => ?_
    exact HasDerivAt.fun_sum (A := fun i (t : ℝ) =>
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun i _ =>
      hasDerivAt_normSq _ _
  have he := ((hq.const_mul (-(2 * Real.pi))).ofReal_comp.cexp).mul_const (g fun k => (d.crd X k).2)
  refine he.congr_deriv ?_
  have e0 : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z 0 : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
    have := _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z 0
    rwa [realAd_zero, zero_smul, add_zero] at this
  rw [e0]
  have e2 : (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) =
      2 * ∑ w, ∑ a, ∑ i, (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re := by
    simp only [Finset.mul_sum]
  simp only [trace_re, e2]
  push_cast
  ring
theorem frame_form_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * dbl (d.Y.J.map (d.B.emb w).1) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
  have h := d.ok.good.cm
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have hd : (dbl d.Y.J).map (d.B.emb w).1 = dbl (d.Y.J.map (d.B.emb w).1) := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks]
  have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map, cst, hd] at this
  rw [this]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
theorem map_mul_incM_T_k {p q r : Type} [Fintype q] (w : InfinitePlace F) (x : Matrix p q (AE F E)) (y : Matrix r q E) :
    (x * (incM F y)ᵀ).map (piInf (d.B.emb w)) = x.map (piInf (d.B.emb w)) * (y.map (d.B.emb w).1)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_map, map_incM']
theorem T_D_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u) Φ) X = (∑ w, Sw (d.A.J.map (d.B.emb w).1) ((R.fr w)⁻¹).1 (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) ((d.b⁻¹).1.map (d.B.emb w).1) (d.cw w X) (d.cw w u)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := at_mul hu _
  have h1 : At (evI F) (W.toCols₁ * tAᵀ) := at_mul (at_toCols₁ hWa) _
  have h2 : At (evI F) W.toCols₂ := at_toCols₂ hWa
  have e1 : W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ = (W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ := by
    rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.split_k u
  rw [← hW, e1] at hs
  have hsplitD : Box.D (d.dd.e u) Φ = Box.D (d.dd.e ((W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
      Box.D (d.dd.e (W.toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ := by
    conv_lhs => rw [hs]
    rw [map_add (f := _), Box.D_add_left]
  rw [hsplitD, _root_.PositivityTheory.SiegelWeilFormula.KK.T_add_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k hΦ h1, hT]
  have hder := _root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_secondColumns hΦ h2 X
  rw [hT] at hder
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_deriv_k R g X W.toCols₂).unique hder |>.symm]
  have hmX : ∀ w, (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW : ∀ w, W.map (piInf (d.B.emb w)) = d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ := fun w => by
    rw [hW, _root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW1 : ∀ w, (W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) =
      (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁ * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k, ← hmW]; rfl
  have hmW2 : ∀ w, d.cw w W.toCols₂ = (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₂ := fun w => by
    rw [← hmW]; rfl
  have hm : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (W.toCols₁ * tAᵀ) X = ∑ w, -(2 * (T1 (d.A.J.map (d.B.emb w).1) (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) (d.cw w X) ((d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁)).re) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, ← e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmX w, hmW1 w]
    rfl
  rw [hm]
  simp only [hmW2, Sw, T2]
  rw [Finset.sum_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vac_rel_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u u' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (hu' : At (evI F) u') (hr : Box.Rel d.B.emb (fun _ => 1) (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) u u') (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u') Φ) X = Complex.I * d.T (Box.D (d.dd.e u) Φ) X := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu' X, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu X, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfi : (R.fr w).1 * ((R.fr w)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Sw_rel e2 hfi (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (R.hfr w) R.hζ (d.cw w X) (d.cw w u) (d.cw w u') (hr w)
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVac
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem splitting_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om :=
  d.ok.dbl.weil.2.1.toIsSplitting
theorem imp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) :
    Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
  ⟨(_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).pres k, (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).impl k (d.dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩
theorem om_D_k (k : d.G) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) : d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have := (_root_.PositivityTheory.SiegelWeilFormula.KK.imp_k d k).inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this
theorem D_kfS_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) :
    Box.D (d.dd.e u) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact Box.DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i
theorem vac_kfS_k (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = Complex.I • Box.D (d.dd.e u) Φ) : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  have hB := d.ok.good
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := _root_.GlobalTheory.ThK.Dbl.finLevel_k F E σ d.B d.m d.n d.A d.Y hB d.κ d.dd d.K (_root_.PositivityTheory.SiegelWeilFormula.KK.isCompact_K_k d) Φ hΦ
  have radd : ∀ u (x y : d.Fn), d.dd.rho d.B.ψ u (x + y) = d.dd.rho d.B.ψ u x + d.dd.rho d.B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : d.Fn), d.dd.rho d.B.ψ u (c • x) = c • d.dd.rho d.B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = Complex.I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by
        simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [Box.D] at e1 e2 ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [Box.D] at e1 ⊢
        rw [Box.DP_smul h.1, Box.DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : d.κ → AF F), (∀ i, evI F (y i) = 0) → Dense.pt x 0 + y = Dense.pt x (Box.fn y) := fun x y hy => by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (Dense.pt 0 (Box.fn z) i) = 0 := fun i => congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at this
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ a) h.1, ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    have cm := (hc k⁻¹ (inv_mem hk) w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlace
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.ae_ext (z z' : AE F E) (h : ∀ w, piInf (d.B.emb w) z = piInf (d.B.emb w) z') (hf : finOne F • z = finOne F • z') :
    z = z' :=
  Place.ad_ext d.cm d.B.emb h hf
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.exists_insW (w : InfinitePlace F) : ∃ ins : ℂ →+ AE F E, (∀ z, piInf (d.B.emb w) (ins z) = z) ∧
    (∀ w', w' ≠ w → ∀ z, piInf (d.B.emb w') (ins z) = 0) ∧ ∀ z, finOne F • ins z = 0 := by
  obtain ⟨s, -, h1, h2, h3, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨AddMonoidHom.mk' (fun z => s (Pi.single w z)) (fun a b => by rw [Pi.single_add, h3]), fun z => ?_,
    fun w' hw' z => ?_, fun z => h2 _⟩
  · simp [h1]
  · simp [h1, Pi.single_eq_of_ne hw']
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainMain
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem perLift_k (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n < d.m) (hEA : d.EisAll) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn}
    (hφ : R.IsLift w Ψ φ) (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I (φ P) x) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _)]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1
      map_smul' := fun a P => by rw [map_smul]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1 }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, ⟨ε, ww, hww, -⟩, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hsec1 : IsSec d.K d.χ (s0 d.m d.n) (d.sec0 (φ 1)) := hSK F E σ d (φ 1) (hKF 1)
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht
      sl Il d.lamSet :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1
      Ileft := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2
      Ik := by
        intro P g k hk
        show thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := fun g a b P => hGI F E σ d R w Ψ hΨ φ hφ g a b P
      Idil := hGD F E σ d R w Ψ hΨ φ hφ
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩
      Λadd := fun l hl => (hLB F E σ d l hl).1
      Λbd := fun l hl => (hLB F E σ d l hl).2
      Λsing := fun f hf hinv hz => hLS F E σ d R w f hf hinv hz
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x, hcd, hT, rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ hsec1 hE1
        have hWh := hW F E σ d hnm hEA (φ 1) (hKF 1) nb lam 𝓖 hcd ε ww hww T hT x
        have hC := hTC F E σ d (φ 1) (hφ 1).1 nb lam 𝓖 hcd T x
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z) T x) (s0 d.m d.n)
          (fc d.B.ψ d.b nb lam 𝓖 (d.I (φ 1)) T x)
        rw [hC]
        exact hWh.congr ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x).2 T hT).symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm.le)
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il d.lamSet hGDat P x
theorem mainOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainOf_k := by
  intro hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW F E _ _ _ _ _ σ d hnm hEA Φ hΦ x
  obtain ⟨R⟩ := hRD F E σ d
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hsch : ∀ i, φ i (P i) ∈ d.sch := fun i => (hφ i (P i)).1
  have eT : ∀ i, d.T (φ i (P i)) = R.tens w (fP (P i)) (Ψ i) := fun i => (hφ i (P i)).2
  have hΦeq : Φ = ∑ i, φ i (P i) := by
    have hmem : Φ - ∑ i, φ i (P i) ∈ d.sch := d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => hsch i)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, eT, hsum, sub_self]
  have key : ∀ i, HolValueAt (fun z => d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x) (s0 d.m d.n)
      (d.I (φ i (P i)) x) := fun i =>
    _root_.PositivityTheory.SiegelWeilFormula.KMain.perLift_k hA hT hTC hAux hFM hLo hLI hGS hGI hGD hPK hSK hLB hLS hU hW d hnm hEA R w (hΨ i) (hφ i) (P i) x
  have hv : d.I Φ x = ∑ i, d.I (φ i (P i)) x := by
    rw [hΦeq, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hsch i) (by rw [eT]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hKi i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 Φ = fun y => ∑ i, d.sec0 (φ i (P i)) y := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦeq, ← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    rfl
  have heq : EqRight (fun z => ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x (fun i _ => htt i z (hz' i))
    show ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x = d.eis (d.sec0 Φ) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    simp only [Finset.mul_sum]
    exact this.symm
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCover
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem exists_cover_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) :
    ∃ C : Set (nA σ Y b), IsCompact C ∧ ∀ β : nA σ Y b, ∃ ν : nF σ Y b, β + (ν : nA σ Y b) ∈ C := by
  obtain ⟨K, hK, hKx⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB) hb
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨⟨γ, hγ⟩, by rwa [add_comm]⟩
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

