module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensStepOf
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

open scoped Classical in
open Classical in
def repPt {L : Type} [Field L] [NumberField L] {n : ℕ} (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) :
    (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else (Y (InfinitePlace.mk p.1))⁻¹ p.2.2 p.2.1

def DensA : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0

def DensB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

theorem densStep_of (ha : DensA) (hb : DensB) : DensStep :=
  fun L _ _ _ n F h => hb L n F (ha L n F h)

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GeneralLinearReduction
section
noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

def mPt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then M p.2.1 p.2.2 else (M⁻¹) p.2.2 p.2.1

theorem gPt_eq {n : ℕ} (g : GL (Fin n) ℂ) : gPt g = mPt g.val := by
  funext p
  unfold gPt mPt
  rw [Matrix.coe_units_inv]

theorem mPt_continuousAt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt mPt M := by
  rw [continuousAt_pi]
  rintro ⟨b, i, j⟩
  cases b
  · simp only [mPt, Bool.false_eq_true, if_false]
    have h1 : ContinuousAt (fun N : Matrix (Fin n) (Fin n) ℂ => N⁻¹) M :=
      continuousAt_matrix_inv M (by simpa [isUnit_iff_ne_zero] using hM)
    exact (continuous_apply_apply j i).continuousAt.comp h1
  · simp only [mPt, if_true]
    exact (continuous_apply_apply i j).continuousAt

def Rm {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix ι ι ℂ := fun i j => MvPolynomial.eval (mPt M) (Q i j)

theorem Rm_continuousAt {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt (Rm Q) M := by
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact ((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp (mPt_continuousAt M hM)

def dd {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t), Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)),
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add],
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add]⟩

theorem dd_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    (dd c t).val = Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t) := rfl

theorem dd_inv_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    ((dd c t)⁻¹).val = Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)) := rfl

theorem dd_tri {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : (dd c t).val.BlockTriangular id := by
  rw [dd_val]
  exact Matrix.blockTriangular_diagonal _

def phi {n : ℕ} (c lam : Fin n → ℤ) : ℤ := ∑ i, c i * lam i

theorem char_dd {n : ℕ} (c lam : Fin n → ℤ) (t : ℝ) :
    ∏ i, (dd c t).val i i ^ lam i = Complex.exp ((phi c lam : ℂ) * t) := by
  rw [dd_val]
  simp only [Matrix.diagonal_apply_eq]
  rw [show (phi c lam : ℂ) * t = ∑ i, (lam i : ℂ) * ((c i : ℂ) * t) by
    unfold phi
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Complex.exp_int_mul ((c i : ℂ) * t) (lam i)).symm

theorem tendsto_exp_neg {k : ℤ} (hk : k < 0) :
    Tendsto (fun t : ℝ => Complex.exp ((k : ℂ) * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun t : ℝ => ‖Complex.exp ((k : ℂ) * t)‖) = fun t => Real.exp ((k : ℝ) * t) := by
    funext t
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [h]
  apply Real.tendsto_exp_atBot.comp
  exact Filter.tendsto_id.const_mul_atTop_of_neg (by exact_mod_cast hk)

theorem wt_le {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j))
    (hmul : ∀ g h, R (g * h) = R g * R h)
    (S : Set (Matrix ι ι ℂ)) (hS : ∀ s ∈ S, ∀ g, s * R g = R g * s)
    (v u : ι → ℂ) (lam mu : Fin n → ℤ)
    (hv : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v)
    (hu : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u)
    (hmem : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)})
    (hu0 : u ≠ 0) (c : Fin n → ℤ) (hc : ∀ i j, i < j → c j < c i) :
    phi c mu ≤ phi c lam := by
  have hR : ∀ g : GL (Fin n) ℂ, R g = Rm Q g.val := by
    intro g; ext i j; rw [hRQ, Rm, gPt_eq]
  set f : (ι → ℂ) → ℝ → (ι → ℂ) := fun w t => Complex.exp (-((phi c lam : ℂ) * t)) • (R (dd c t) *ᵥ w) with hf
  let P : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∃ y, Tendsto (f w) atTop (𝓝 y)}
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        refine ⟨ya + yb, ?_⟩
        have e : f (a + b) = fun t => f a t + f b t := by funext t; simp [hf, Matrix.mulVec_add, smul_add]
        rw [e]; exact ha.add hb
      zero_mem' := ⟨0, by
        have e : f 0 = fun _ => 0 := by funext t; simp [hf]
        rw [e]; exact tendsto_const_nhds⟩
      smul_mem' := by
        rintro r a ⟨ya, ha⟩
        refine ⟨r • ya, ?_⟩
        have e : f (r • a) = fun t => r • f a t := by funext t; simp [hf, Matrix.mulVec_smul, smul_comm r]
        rw [e]; exact ha.const_smul r }

  have hgenL : ∀ s ∈ S, ∀ large₂ : GL (Fin n) ℂ, LowUni large₂.val → s *ᵥ (R large₂ *ᵥ v) ∈ P := by
    intro s hs large₂ hL
    have comm : ∀ g y, R g *ᵥ (s *ᵥ y) = s *ᵥ (R g *ᵥ y) := by
      intro g y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS s hs]
    have key : ∀ t, f (s *ᵥ (R large₂ *ᵥ v)) t = s *ᵥ (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
      intro t
      have e2 : dd c t * large₂ = (dd c t * large₂ * (dd c t)⁻¹) * dd c t := by group
      have inner : R (dd c t) *ᵥ (R large₂ *ᵥ v) =
          Complex.exp ((phi c lam : ℂ) * t) • (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← hmul, show R (dd c t * large₂) = R (dd c t * large₂ * (dd c t)⁻¹) * R (dd c t) by
          rw [← hmul, ← e2], ← Matrix.mulVec_mulVec, hv (dd c t) (dd_tri c t),
          char_dd, Matrix.mulVec_smul, hR]
      simp only [hf]
      rw [comm, inner, Matrix.mulVec_smul, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    have hM : Tendsto (fun t => (dd c t * large₂ * (dd c t)⁻¹).val) atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have hentry : ∀ t, (dd c t * large₂ * (dd c t)⁻¹).val i j =
          Complex.exp (((c i - c j : ℤ) : ℂ) * t) * large₂.val i j := by
        intro t
        rw [Units.val_mul, Units.val_mul, dd_val, dd_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
        rw [mul_comm (Complex.exp _) (large₂.val i j), mul_assoc, ← Complex.exp_add, mul_comm]
        congr 2; push_cast; ring
      simp only [hentry]
      rcases lt_trichotomy i j with h | h | h
      · rw [hL.1 i j h, Matrix.one_apply_ne h.ne]; simp
      · subst h; simp [hL.2]
      · rw [Matrix.one_apply_ne h.ne']
        simpa using (tendsto_exp_neg (sub_neg.2 (hc j i h))).mul_const (large₂.val i j)
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    refine ⟨s *ᵥ (Rm Q 1 *ᵥ v), ?_⟩
    rw [show f (s *ᵥ (R large₂ *ᵥ v)) = _ from funext key]
    exact (hcs.tendsto _).comp ((Rm_continuousAt Q 1 (by simp)).tendsto.comp hM)

  have hgen : ∀ s ∈ S, ∀ g : GL (Fin n) ℂ, s *ᵥ (R g *ᵥ v) ∈ P := by
    intro s hs g
    have hclosed : IsClosed (P : Set (ι → ℂ)) := Submodule.closed_of_finiteDimensional P
    have hdet : g.val.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun x : ℂ => s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v)) (𝓝[≠] 0) (𝓝 (s *ᵥ (R g *ᵥ v))) := by
      rw [hR]
      exact (hcs.tendsto _).comp ((Rm_continuousAt Q g.val hdet).tendsto.comp (tendsto_add_smul g.val))
    apply hclosed.mem_of_tendsto hlim
    filter_upwards [dense_LU g.val] with x hx
    obtain ⟨hdx, L, U, hL, hU, hLU⟩ := hx
    have hdL : L.det ≠ 0 := by rw [det_lowUni hL]; exact one_ne_zero
    have hdU : U.det ≠ 0 := by intro h; apply hdx; rw [hLU, Matrix.det_mul, h, mul_zero]
    set large₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdL
    set Ug := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdU
    have e : g.val + x • 1 = (large₂ * Ug).val := by rw [hLU]; rfl
    have hUg : Ug.val.BlockTriangular id := fun i j h => hU i j h
    show s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v) ∈ P
    rw [e, ← hR, hmul, ← Matrix.mulVec_mulVec, hv Ug hUg, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact P.smul_mem _ (hgenL s hs large₂ hL)
  have huP : u ∈ P := by
    refine Submodule.span_le.2 ?_ hmem
    rintro w ⟨s, hs, g, rfl⟩
    exact hgen s hs g
  obtain ⟨y, hy⟩ := huP
  by_contra hlt
  push Not at hlt
  have hfu : ∀ t, f u t = Complex.exp (((phi c mu - phi c lam : ℤ) : ℂ) * t) • u := by
    intro t
    simp only [hf]
    rw [hu (dd c t) (dd_tri c t), char_dd, smul_smul, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hnorm : Tendsto (fun t => ‖f u t‖) atTop atTop := by
    have e : (fun t => ‖f u t‖) = fun t => Real.exp (((phi c mu - phi c lam : ℤ) : ℝ) * t) * ‖u‖ := by
      funext t; rw [hfu, norm_smul, Complex.norm_exp]; simp
    rw [e]
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by exact_mod_cast sub_pos.2 hlt))).atTop_mul_const
      (norm_pos_iff.2 hu0)
  exact not_tendsto_atTop_of_tendsto_nhds hy.norm hnorm

theorem general_linear_reduction : GLStep := by
  intro n ι _ _ R Q hRQ hmul S hS v u lam mu hv hu hspv hspu hv0 hu0
  have memu : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} := by
    rw [hspv]; exact Submodule.mem_top
  have memv : v ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} := by
    rw [hspu]; exact Submodule.mem_top
  have key : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j < c i) → phi c mu = phi c lam := fun c hc =>
    le_antisymm (wt_le R Q hRQ hmul S hS v u lam mu hv hu memu hu0 c hc)
      (wt_le R Q hRQ hmul S hS u v mu lam hu hv memv hv0 c hc)
  funext k
  let c0 : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ)
  let ck : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ) + if i = k then 1 else 0
  have h0 := key c0 (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [c0]; omega)
  have h1 := key ck (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [ck]; split_ifs <;> omega)
  have hk : ∀ x : Fin n → ℤ, phi ck x = phi c0 x + x k := by
    intro x
    simp [phi, ck, c0, add_mul, Finset.sum_add_distrib]
  rw [hk, hk] at h1
  linarith

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem conj_conj (τ : L →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem conj_ne (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  have h : ¬ ComplexEmbedding.IsReal τ := by
    rw [← InfinitePlace.isComplex_mk_iff]; exact IsTotallyComplex.isComplex _
  rwa [ComplexEmbedding.isReal_iff] at h

def W0 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R := (Fin.revPerm.toPEquiv).toMatrix

theorem longest_element_conj {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    W0 R n * M * W0 R n = M.submatrix Fin.rev Fin.rev := by
  rw [W0, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j; simp

theorem longest_element_mul_self {R : Type} [CommRing R] : W0 R n * W0 R n = 1 := by
  have h := longest_element_conj (R := R) (n := n) 1
  rw [Matrix.mul_one] at h
  rw [h]; exact Matrix.submatrix_one_equiv Fin.revPerm

theorem lattice_model_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : (W0 R n).map f = W0 S n := by
  ext i j; simp only [W0, Matrix.map_apply, PEquiv.toMatrix_apply]; split_ifs <;> simp

theorem longest_element_transpose {R : Type} [CommRing R] : (W0 R n)ᵀ = W0 R n := by
  ext i j; simp only [W0, Matrix.transpose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Fin.revPerm_apply]
  congr 1; apply propext; constructor <;> (rintro rfl; simp)

def w0L : GL (Fin n) L := ⟨W0 L n, W0 L n, longest_element_mul_self, longest_element_mul_self⟩

theorem longest_element_mem : (w0L : GL (Fin n) L) ∈ GQ0 L n := by
  change W0 L n * conjT _ (W0 L n) = 1
  rw [conjT, lattice_model_map, longest_element_transpose, longest_element_mul_self]

theorem conjAL_incl (x : L) : conjAL L (Algebra.TensorProduct.includeLeftRingHom x) =
    Algebra.TensorProduct.includeLeftRingHom ((IsCMField.complexConj L : L →+* L) x) := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

theorem map_mem_GA (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) g ∈ GA L n := by
  change (g.val.map _) * conjT (conjAL L) (g.val.map _) = 1
  have hg' : g.val * conjT _ g.val = 1 := hg
  have : conjT (conjAL L) (g.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) =
      (conjT (IsCMField.complexConj L : L →+* L) g.val).map Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]; exact conjAL_incl _
  rw [this, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero _) (map_one _)]

def toGQ (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) : GQ L n :=
  ⟨⟨_, map_mem_GA g hg⟩, ⟨g, hg, rfl⟩⟩

theorem toGQ_val (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) :
    ((((toGQ g hg : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      g.val.map Algebra.TensorProduct.includeLeftRingHom := rfl

end

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

