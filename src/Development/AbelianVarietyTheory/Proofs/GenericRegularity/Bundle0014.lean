module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
section
noncomputable section

namespace GlobalTheory.FrameNorm.UnitFr

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hermC_mul_left {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G (fun k => u k * α) v = α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermC_mul_right {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G u (fun k => v k * α) = (starRingEnd ℂ) α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]
  ring

theorem col_mul_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℝ) (c : Fin r) :
    col (A * Matrix.diagonal fun a => (β a : ℂ)) c = fun k => col A c k * (β c : ℂ) := by
  funext k
  simp [col, Matrix.mul_diagonal]

theorem gram_mul_diag {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A : Matrix (Fin r) (Fin r) ℂ)
    (β : Fin r → ℝ) :
    gram τ G (A * Matrix.diagonal fun a => (β a : ℂ)) =
      Matrix.diagonal (fun a => (β a : ℂ)) * gram τ G A * Matrix.diagonal (fun a => (β a : ℂ)) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [gram, Matrix.of_apply, col_mul_diag, hermC_mul_left, hermC_mul_right, Complex.conj_ofReal]
  ring

theorem lminor_diag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℂ) (i : Fin (r + 1)) :
    lminor (Matrix.diagonal β * M * Matrix.diagonal β) i =
      (∏ a : Fin i, β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 * lminor M i := by
  unfold lminor
  have e : (Matrix.diagonal β * M * Matrix.diagonal β).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) =
      Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) *
        M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) *
        Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) := by
    ext a b
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

variable {r : ℕ} (X : Data E r)

def tq (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := ‖dmin X.Gm x τ a.succ / dmin X.Gm x τ a.castSucc‖

def bt (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := tq X x τ a ^ (-(1 : ℝ) / 2)

def unitB (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)

def unitF (x : Frame X.Ψ r) : Frame X.Ψ r := rmul x (unitB X x)

theorem mat_unitF (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (unitF X x) τ = mat x τ * Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) := rfl

theorem dmin_unitF (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (unitF X x) τ i =
      (((∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 : ℝ) : ℂ) * dmin X.Gm x τ i := by
  unfold dmin
  rw [mat_unitF, gram_mul_diag, lminor_diag]
  push_cast
  rfl

variable {X}

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have := (hx' τ).2 i
  rw [h, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

theorem tq_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < tq X x τ a :=
  norm_pos_iff.2 (div_ne_zero (dmin_ne hx τ _) (dmin_ne hx τ _))

theorem bt_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < bt X x τ a :=
  Real.rpow_pos_of_pos (tq_pos hx τ a) _

theorem bt_sq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) :
    bt X x τ a ^ 2 = (tq X x τ a)⁻¹ := by
  unfold bt
  rw [← Real.rpow_natCast, ← Real.rpow_mul (tq_pos hx τ a).le]
  norm_num
  exact Real.rpow_neg_one _

def gN (x : Frame X.Ψ r) (τ : X.Ψ) (m : ℕ) : ℝ := if h : m < r + 1 then ‖dmin X.Gm x τ ⟨m, h⟩‖ else 1

theorem gN_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (m : ℕ) : gN x τ m ≠ 0 := by
  unfold gN
  split_ifs with h
  · exact norm_ne_zero_iff.2 (dmin_ne hx τ _)
  · exact one_ne_zero

theorem gN_zero (x : Frame X.Ψ r) (τ : X.Ψ) : gN x τ 0 = 1 := by
  unfold gN
  rw [dite_eq_left (Nat.succ_pos r)]
  have : dmin X.Gm x τ ⟨0, Nat.succ_pos r⟩ = 1 := Matrix.det_fin_zero
  rw [this, norm_one]

theorem prod_gN {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (n : ℕ) :
    ∏ m ∈ Finset.range n, gN x τ m / gN x τ (m + 1) = gN x τ 0 / gN x τ n := by
  induction n with
  | zero => simp [div_self (gN_ne hx τ 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [gN_ne hx τ n, gN_ne hx τ (n + 1), gN_ne hx τ 0]

theorem tq_castLE {x : Frame X.Ψ r} (τ : X.Ψ) {i : ℕ} (hi : i ≤ r) (a : Fin i) :
    tq X x τ (Fin.castLE hi a) = gN x τ (a + 1) / gN x τ a := by
  unfold tq gN
  rw [dite_eq_left (by omega), dite_eq_left (by omega), norm_div]
  rfl

theorem norm_dmin_unitF {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (unitF X x) τ i‖ = 1 := by
  rw [dmin_unitF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Finset.prod_pow]
  have h1 : ∀ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a) ^ 2 =
      gN x τ (a : ℕ) / gN x τ ((a : ℕ) + 1) := by
    intro a
    rw [bt_sq hx, tq_castLE, inv_div]
  simp_rw [h1]
  rw [Fin.prod_univ_eq_prod_range (fun m => gN x τ m / gN x τ (m + 1)), prod_gN hx, gN_zero]
  have h2 : gN x τ i = ‖dmin X.Gm x τ i‖ := by
    unfold gN
    rw [dite_eq_left i.isLt]
  rw [h2, div_mul_cancel₀ _ (norm_ne_zero_iff.2 (dmin_ne hx τ i))]

theorem unitB_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitB X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne'
  · show Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) a c = 0
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hca)

theorem unitF_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitF X x ∈ X.dom := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_unitF, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hx' τ).1
      (Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne')
  · rw [dmin_unitF, Complex.re_ofReal_mul]
    have hs : 0 < (∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 :=
      pow_pos (Finset.prod_pos fun a _ => bt_pos hx τ _) 2
    have := (hx' τ).2 i
    nlinarith

theorem pnorm_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) :
    X.pnorm la P (unitF X x) = X.pnorm la P x := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]
  rw [show unitF X x = rmul x (unitB X x) from rfl, hB _ (unitB_mem x hx), norm_mul, mul_comm]
  congr 1
  unfold bchar
  simp only [norm_prod, norm_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ‖(Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) i i)‖ ^ la τ i = _
  rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_of_nonneg (bt_pos hx τ i).le]
  unfold bt
  rw [← Real.rpow_intCast, ← Real.rpow_mul (tq_pos hx τ i).le]
  unfold tq
  congr 1
  ring

theorem pnorm_eq_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : X.IsSec la P) : X.pnorm la P x = ‖P (unitF X x)‖ := by
  rw [← pnorm_unitF x hx la P (hP.2.1 x hx)]
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem lact_one' {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end GlobalTheory.FrameNorm.UnitFr

namespace GlobalTheory.FrameNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem exists_unitFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU
  have h3 := hU.2.2.1
  have h4 := hU.2.2.2.1
  clear hU
  let uf : ∀ k, (U.X k).dom → (U.X k).dom := fun k x => ⟨UnitFr.unitF (U.X k) x.1, UnitFr.unitF_mem x.1 x.2⟩
  have huf : ∀ k x, (uf k x).1 = FD.rmul x.1 (UnitFr.unitB (U.X k) x.1) := fun _ _ => rfl
  have hun : ∀ k x, IsUnitFr (U.X k) (uf k x).1 := fun k x τ i => UnitFr.norm_dmin_unitF x.2 τ i
  have hpn : ∀ k (x : (U.X k).dom) (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P →
      (U.X k).pnorm la P x.1 = ‖P (uf k x).1‖ := fun k x la P hP => UnitFr.pnorm_eq_unitF x.1 x.2 la P hP
  clear_value uf
  have key : ∀ k (x : (U.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k (uf k x)) (U.un k x) := by
    intro k x
    obtain ⟨t, ht⟩ := (h4 k k x (uf k x)).2
      ⟨1, (U.X k).Γ.one_mem, UnitFr.unitB (U.X k) x.1, UnitFr.unitB_mem x.1 x.2, by
        rw [UnitFr.lact_one', huf]⟩
    exact ⟨t⁻¹, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k (uf k x))
      (U.un k x)).2.2.2 t ht⟩
  refine ⟨fun k x => ⟨uf k x, hun k x, ⟨_, UnitFr.unitB_mem x.1 x.2, huf k x⟩, key k x, hpn k x⟩, fun y => ?_⟩
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨s, hs⟩ := key k x
  exact ⟨k, uf k x, t * s, hun k x,
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k (uf k x)) (U.un k x) y).2.2.1 s t hs ht⟩

end GlobalTheory.FrameNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCell
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntLie

theorem int_comb {V L : Type} [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] {n r : ℕ}
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V) (hu : InCell ix u) (x : Fin n → V) (cf : Fin r → L)
    (h : (fun j => algebraMap V L (x j)) = ∑ i, cf i • fun j => algebraMap V L (u j i)) :
    ∃ a : Fin r → V, x = ∑ i, a i • fun j => u j i := by
  have h1 := ((GlobalTheory.cell_columns_saturated_and_triangular V L n r ix u hu).1 r x).1 (by
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩))
  obtain ⟨a, -, ha⟩ := (GlobalTheory.mem_span_first_columns_iff u r x).1 h1
  refine ⟨a, ?_⟩
  rw [ha]
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f)) =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.Reg.IntLie

namespace GlobalTheory.Reg

open IntLie
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA chart_of_basis dualMapR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj


set_option maxHeartbeats 800000 in
theorem tie_vectors_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hcell
  let _ := io.toAlgebra
  intro z Λ tie G m m2 hφ
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨v, hv0, hvb, -⟩ := M.lie T.V f₀ G m
  obtain ⟨xc, hxc, hxv⟩ := chart_of_basis hvb
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G M.n xc hxc
  have hpt : ∀ cc : Fin M.n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := Λ.m1.cart
  have h2 : IsGrpPullback Λ.t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  let vA := fun e : Fin M.n → T.Fr => Classical.choose (relA_exists_v z.x h1 h2 (tvec (x := x') e))
  have hvA := fun e : Fin M.n → T.Fr => Classical.choose_spec (relA_exists_v z.x h1 h2 (tvec (x := x') e))
  have tanA : ∀ e, IsTanAt z.x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan z.x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig z.x h1 h2 (hvA e) (Λ.t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (Λ.m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin M.n → T.Fr) (cf : Fin m → T.Fr) (e : Fin M.n → T.Fr),
      IsCombAt z.x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA z.x Λ.m1.φ m2.φ (sclA z.x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl z.x (hvA (d i)) (cf i)
    have hp := relA_prod z.x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA z.x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq z.x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA z.x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq z.x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have combV : ∀ cc : Fin M.n → T.V, IsLieComb cc v (tvec (x := xc) cc) := by
    intro cc
    refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cc i)) ≫ tvec (x := xc) (Pi.single i 1), fun i => ?_, ?_⟩
    · rw [hxv i]; rfl
    · refine Eq.trans ?_ (prod_tvec hxc cc fun i => Pi.single i 1).symm
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
  have gen : ∀ τ i, ∃ u' : epsR T.Fr ⟶ Λ.t'.G, u'.left ≫ Λ.m1.φ = z.u τ i ∧
      u'.left ≫ m2.φ = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (tvec (x := xc) fun j => u₀ τ j i).left := by
    intro τ i
    obtain ⟨v', u', hv', hc, hu'⟩ := tie τ i
    refine ⟨u', hu', ?_⟩
    refine (GlobalTheory.lieComb_baseChange T.V T.Fr (algebraMap T.V T.Fr) G.G Λ.t'.G m2.φ m2.cart M.n v _ _ v' u'
      (fun j => ?_) (combV fun j => u₀ τ j i)).2 hc
    apply m.cart.1.hom_ext
    · refine (Category.assoc _ _ _).trans (((congrArg ((v' j).left ≫ ·) hφ).trans (hv' j)).trans ?_)
      rw [dualMapR_comp]
      exact (Category.assoc _ _ _).trans
        ((congrArg (spMap (dualMapR (algebraMap T.V T.Fr)) ≫ ·) (hv0 j).symm).trans (Category.assoc _ _ _).symm)
    · rw [Category.assoc, m2.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over _).symm
  have hz : ∀ τ, z.u τ = fun i => (vA fun j => algebraMap T.V T.Fr (u₀ τ j i)).left := by
    intro τ
    funext i
    obtain ⟨u', hu1, hu2⟩ := gen τ i
    obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (u₀ τ j i))
    have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (u₀ τ j i))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
    have e : u'.left = w.left := by
      apply m2.cart.1.hom_ext
      · exact hu2.trans (hw'.trans (hcomp fun j => u₀ τ j i)).symm
      · exact (Over.w u').trans ((Over.w w).trans (Category.comp_id _)).symm
    rw [hwl, ← hu1, e]
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have eigV : ∀ τ (cc : Fin M.n → T.V), IsEigAt c τ (vA fun j => algebraMap T.V T.Fr (cc j)).left ↔
      ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := by
    intro τ cc
    rw [eigA]
    refine forall_congr' fun a => ?_
    rw [hM, ← hχ, funext_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← map_mul]
    exact inj.eq_iff
  have mapc : ∀ τ (r : Fin (Dw.mult τ) → T.V) (cc : Fin M.n → T.V), (cc = ∑ i, r i • fun j => u₀ τ j i) →
      (fun j => algebraMap T.V T.Fr (cc j)) =
        ∑ i, algebraMap T.V T.Fr (r i) • fun j => algebraMap T.V T.Fr (u₀ τ j i) := by
    rintro τ r cc rfl
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine ⟨fun τ i => cvV (tvec (x := xc) fun j => u₀ τ j i), fun τ i => isTan_cvV (isTan_tvec hxc _),
    fun τ i a s hs => ?_, fun τ w hw he => ?_, fun τ i => ?_⟩
  · have hs' : s = χ τ a := inj (hs.trans (hχ τ a).symm)
    subst hs'
    refine (eigV_iff hxc (G.act.act a) _ _).2 ((eigV τ _).1 ?_ a)
    have := z.eig τ i
    rw [hz τ] at this
    exact this
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
    have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
      (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
    obtain ⟨cf, hcf, hu⟩ := z.basis τ _ (tanA _) ((eigV τ cc).2 hcc)
    rw [hz τ] at hcf hu
    obtain ⟨r, hr⟩ := int_comb (ix τ) (u₀ τ) (hcell τ) cc cf ((combA _ cf _).1 hcf)
    refine ⟨r, (comb_iff hxc (fun i j => u₀ τ j i) r cc).2 hr, fun r' h' => ?_⟩
    have h'' := (comb_iff hxc (fun i j => u₀ τ j i) r' cc).1 h'
    have e1 := hu _ ((combA _ _ _).2 (mapc τ r cc hr))
    have e2 := hu _ ((combA _ _ _).2 (mapc τ r' cc h''))
    funext i
    exact inj (congrFun (e2.trans e1.symm) i)
  · obtain ⟨u', hu1, hu2⟩ := gen τ i
    refine ⟨u'.left, hu1, ?_⟩
    rw [cvV_left]
    exact hu2

end GlobalTheory.Reg
end
end

