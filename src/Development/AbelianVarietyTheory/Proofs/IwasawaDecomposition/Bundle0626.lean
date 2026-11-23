module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
  GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem topCoeff_sum' {n : ℕ} {κ : Type} (s : Finset κ) (P : κ → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, P i) = ∑ i ∈ s, topCoeff (P i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_real_smul {n : ℕ} (r : ℝ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (r • P) = (r : ℂ) * topCoeff P := by
  simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem topCoeff_chern_eq_sum_rep : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  intro ι _ m n R
  classical
  have hmem := GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan m n (MvPolynomial (Fin n × Fin n) ℂ)
    (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.1 hmem
  choose ρ hρ using fun i => (g i).2
  refine ⟨Fin k, inferInstance, ρ, f, fun A hA => ?_⟩
  set c : ι × ℕ → MvPolynomial (Fin n × Fin n) ℂ := fun x => (Matrix.charpolyRev (-A x.1)).coeff x.2 with hc
  have hch : ∀ x : ι × ℕ, IsWeightedHomogeneous (1 : Fin n × Fin n → ℕ) (c x) x.2 := fun x =>
    ChernDegree.charpolyRev_coeff_isHomogeneous (-A x.1) (fun i j => (hA x.1 i j).neg) x.2
  have key : ∀ d : ι × ℕ →₀ ℕ, Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d ≠ n →
      topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) = 0 := by
    intro d hd
    have h1 : IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) (monomial d (AddMonoidAlgebra.coeff R d))
        (Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    exact ChernDegree.topCoeff_eq_zero (ChernDegree.aeval_isWeightedHomogeneous h1 c hch) hd
  have e1 : topCoeff (aeval c R) = ∑ d ∈ R.support, topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by
    conv_lhs => rw [R.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, topCoeff_sum']
  have e2 : topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) =
      ∑ d ∈ R.support with Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d = n,
        topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [weightedHomogeneousComponent_apply, map_sum, topCoeff_sum']
  have e3 : topCoeff (aeval c R) = topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) := by
    rw [e1, e2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rfl
    · exact key d h
  have hval := congrFun hfg A
  simp only [Finset.sum_apply, Pi.smul_apply] at hval
  rw [e3, ← hval, topCoeff_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topCoeff_real_smul, ← hρ i]

end GlobalTheory.GoodMetric.ChernSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric

section Subst

variable {n : ℕ}

namespace LinSubst

def rowSel (c : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i => Pi.single (c i) 1

theorem topCoeff_add (P Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (P + Q) = topCoeff P + topCoeff Q := by
  simp [topCoeff, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem topCoeff_C_mul (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) : topCoeff (C a * P) = a * topCoeff P := by
  simp only [topCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_apply_sum_single {k : ℕ} (f : Fin k → Fin n × Fin n) :
    ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x = k := by
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

theorem prod_X_eq_monomial' {ι : Type} [Fintype ι] (f : ι → Fin n × Fin n) :
    (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ i, Finsupp.single (f i) 1) 1 := by
  rw [monomial_sum_one]
  rfl

theorem topCoeff_prod_X_of_ne {k : ℕ} (hk : k ≠ n) (f : Fin k → Fin n × Fin n) :
    topCoeff (∏ i, X (f i)) = 0 := by
  rw [topCoeff]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [prod_X_eq_monomial', coeff_monomial, if_neg, mul_zero]
  intro h
  have : ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x =
      ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x := by rw [h]
  rw [sum_apply_sum_single, sum_apply_sum_single (fun a => (a, w a))] at this
  exact hk this

theorem graph_apply (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_eq_iff (g h : Fin n → Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) = ∑ a, Finsupp.single (a, h a) 1 ↔ g = h := by
  constructor
  · intro e
    funext x
    have := DFunLike.congr_fun e (x, g x)
    rw [graph_apply, graph_apply] at this
    by_contra hne
    rw [if_pos rfl, if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  · rintro rfl
    rfl

theorem det_rowSel_of_not_injective {c : Fin n → Fin n} (hc : ¬ Function.Injective c) : (rowSel c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hc
    obtain ⟨i, j, h, h'⟩ := hc
    exact ⟨i, j, h, h'⟩
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [rowSel, hij])

theorem det_rowSel_perm (σ : Equiv.Perm (Fin n)) : (rowSel σ).det = Equiv.Perm.sign σ := by
  have : rowSel σ = σ.permMatrix ℂ := by
    ext i j
    simp [rowSel, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_permutation]

theorem sum_prod_mul_det_rowSel (U : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c : Fin n → Fin n, (∏ i, U i (c i)) * (rowSel c).det = U.det := by
  have h : (fun i => ∑ a, U i a • (Pi.single a 1 : Fin n → ℂ)) = U := by
    ext i j
    simp [Pi.single_apply]
  conv_rhs => rw [← h]
  change _ = (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem topCoeff_prod_X_pair (c d : Fin n → Fin n) :
    topCoeff (∏ i, X (c i, d i)) = (rowSel c).det * (rowSel d).det := by
  rw [topCoeff, prod_X_eq_monomial']
  simp only [coeff_monomial]
  by_cases hc : Function.Injective c
  · have hcb : Function.Bijective c := Finite.injective_iff_bijective.mp hc
    set σ := Equiv.ofBijective c hcb with hσ
    have e : (∑ i, Finsupp.single (c i, d i) 1 : Fin n × Fin n →₀ ℕ) =
        ∑ a, Finsupp.single (a, (d ∘ σ.symm) a) 1 := by
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [σ]
    simp_rw [e, graph_eq_iff]
    have hcσ : rowSel c = rowSel ⇑σ := rfl
    rw [hcσ, det_rowSel_perm]
    by_cases hd : Function.Injective d
    · set τ := Equiv.ofBijective d (Finite.injective_iff_bijective.mp hd) with hτ
      have hdτ : d ∘ σ.symm = ⇑(σ.symm.trans τ) := by
        ext a
        simp [τ]
      have hdτ' : rowSel d = rowSel ⇑τ := rfl
      rw [hdτ, hdτ', det_rowSel_perm]
      simp only [DFunLike.coe_fn_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]
    · rw [det_rowSel_of_not_injective hd, mul_zero]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg, mul_zero]
      intro h
      apply hd
      have : d = w ∘ σ := by
        rw [← h]
        ext a
        simp
      rw [this]
      exact w.injective.comp σ.injective
  · rw [det_rowSel_of_not_injective hc, zero_mul]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro h
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, c i ≠ x := by
      have : ¬ Function.Surjective c := fun hs => hc (Finite.injective_iff_surjective.mpr hs)
      simpa [Function.Surjective] using this
    have h1 := DFunLike.congr_fun h (x, w x)
    rw [graph_apply, if_pos rfl, Finsupp.finsetSum_apply] at h1
    simp [Finsupp.single_apply, hx] at h1

theorem rowSel_mul_apply (c : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (i b : Fin n) :
    (rowSel c * M) i b = M (c i) b := by
  simp [rowSel, Matrix.mul_apply, Pi.single_apply]

theorem exists_prod_X (u : Fin n × Fin n →₀ ℕ) :
    ∃ (k : ℕ) (f : Fin k → Fin n × Fin n), monomial u (1 : ℂ) = ∏ i, X (f i) := by
  induction u using Finsupp.induction with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | single_add x m u _ _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    refine ⟨m + k, Fin.append (fun _ => x) f, ?_⟩
    rw [Fin.prod_univ_add, monomial_single_add, hf]
    simp [Fin.append_left, Fin.append_right]

theorem topCoeff_subst_prod (J : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (f : Fin k → Fin n × Fin n) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ)) = J.det * starRingEnd ℂ J.det * topCoeff (∏ i, X (f i)) := by
  rw [map_prod]
  simp only [aeval_X]
  have e : ∀ i, (∑ a, ∑ b, C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b) :
      MvPolynomial (Fin n × Fin n) ℂ) =
      ∑ p : Fin n × Fin n, C (J (f i).1 p.1 * starRingEnd ℂ (J (f i).2 p.2)) * X p := fun i =>
    (Fintype.sum_prod_type' (fun a b => C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b))).symm
  simp_rw [e]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
  by_cases hk : k = n
  · subst hk
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, J (f i).1 (c i) * starRingEnd ℂ (J (f i).2 (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (rowSel (fun i => (f i).1) * J) i (c i)) * (rowSel c).det) *
        ((∏ i, (rowSel (fun i => (f i).2) * J.map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [rowSel_mul_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, Matrix.det_mul, Matrix.det_mul]
    have hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
      rw [RingHom.map_det]
      rfl
    rw [hc]
    ring
  · simp [topCoeff_prod_X_of_ne hk]

end LinSubst

open LinSubst

theorem topCoeff_subst_conj (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) =
      J.det * starRingEnd ℂ J.det * topCoeff P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u r =>
    obtain ⟨k, f, hf⟩ := exists_prod_X u
    have e : (monomial u r : MvPolynomial (Fin n × Fin n) ℂ) = C r * ∏ i, X (f i) := by
      rw [← hf, C_mul_monomial, mul_one]
    rw [e, map_mul, aeval_C, algebraMap_eq, topCoeff_C_mul, topCoeff_C_mul, topCoeff_subst_prod]
    ring
  | add p q hp hq =>
    rw [map_add (f := _), topCoeff_add, topCoeff_add, hp, hq, mul_add]

end Subst

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram GlobalTheory.TrueCx Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeGenUnf

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_mem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : Formalism.L2.PjFree.relab c σ τ.1 ∈ (U.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ.1).2 τ.2)

theorem comb_unitary {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x x₁ : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k) x₁.1)
    (e : (U.un k x₁).x = (U.un k x).x) (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hT : ∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) ((U.un k x₁).u τ b)) :
    Tᴴ * T = 1 :=
  _root_.GlobalTheory.ShFam.lie_coord_unitary hσ hU k x x₁ hx hx₁ e τ T hT

theorem uniformisation_component_eq_of_same_modulusPoint {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨g0, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem unitary_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)} (hf : IsHodgeFrame Uf y f) (hg : IsHodgeFrame Uf y g)
    (τ : E →+* ℂ) : (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  have e1 : σ = σ' := by_contra fun h => (hE σ' (Ne.symm h)).false k
  have e2 : σ = σ₁ := by_contra fun h => (hE σ₁ (Ne.symm h)).false k₁
  subst e1 e2
  have hid : ∀ {ψ : ℂ →+* ℂ}, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) → σ = ψ.comp σ → ψ = RingHom.id ℂ := by
    intro ψ h h'
    rcases h with rfl | rfl
    · rfl
    · exact (not_good_conj c (σ := σ) hσ (h' ▸ hσ)).elim
  obtain rfl := hid h1 h2
  obtain rfl := hid g1 g2
  have hx : (cxPt Z ((Uf σ).un k x)).1 ≫ genι Z = spMap (RingHom.id ℂ) ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap (RingHom.id ℂ) h2 hx
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  obtain rfl : k = k₁ := (uniformisation_component_eq_of_same_modulusPoint hσ hU x x₁ e.symm).symm
  have key := comb_unitary hσ hU k x x₁ h4 g4 e τ _ (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  rw [h6.co τ hg' hx] at key
  convert key using 2 <;> ext <;> simp

theorem gram_eq_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ} {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : IsHodgeFrame Uf y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge Uf b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame Uf y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    unitary_of_single hE hσ hU h.choose_spec hf, Matrix.one_mul]

theorem unfFam_empty (U : Formalism.L2.PjFree.Unf Xo c σ r) (σ' : c.F →+* ℂ) (h : σ' ≠ σ) :
    IsEmpty (unfFam U σ').Comp := by
  unfold unfFam
  rw [dite_eq_right (Ne.symm h)]
  exact inferInstanceAs (IsEmpty Empty)

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := dif_pos rfl

theorem isHodgeFrame_of_eq {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hq : Uf σ = U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) :
    IsHodgeFrame (Z := Z) Uf (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) := by
  subst hq
  exact isHodgeFrame_cxFrame hσ hx


variable (Z) in
theorem hodgeMet_gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  rw [hodgeMet, gram_eq_of_single (unfFam_empty U) hσ ((unfFam_self U).symm ▸ hU)
    (isHodgeFrame_of_eq (unfFam_self U) hσ hx), EigFrame.co_self, conjTranspose_one, Matrix.mul_one]

end GlobalTheory.HodgeGenUnf

namespace GlobalTheory.HodgeGenUnf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

def letter {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : (U.X k).Ψ :=
  ⟨Formalism.L2.PjFree.relab c σ τ.1, relab_mem hσ hU k τ⟩

theorem mult_psi (τ : GlobalTheory.AllWt.Psi H) : Dw.mult τ.1 = Dw.p := if_pos τ.2


variable (Z) in
theorem hodgeMet_gram_frame {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (f : (U.X k).dom) (τ : GlobalTheory.AllWt.Psi H) (τ' : (U.X k).Ψ)
    (hτ : τ'.1 = Formalism.L2.PjFree.relab c σ τ.1) (hj : Dw.p ≤ Dw.p + Dw.q) :
    ((hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1).submatrix
        (Fin.cast (mult_psi τ).symm) (Fin.cast (mult_psi τ).symm) =
      ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) hj f.1 τ')ᴴ * (hP (moeb (frameCo (U.X k) hj f.1 τ') 0))⁻¹ *
        coW (U.X k) hj f.1 τ') := by
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k) f.1 f.2
  let f' : (U.X k).dom := ⟨x1, KU.orth_dom _ h1⟩
  have hz : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f.1 = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f'.1 := by
    show domPt _ _ _ f.1 = domPt _ _ _ x1
    rw [ef, domPt_rmul _ _ _ hb]
  have hmo : ∀ ρ : (U.X k).Ψ, moeb (frameCo (U.X k) hj f.1 ρ) 0 = moeb (frameCo (U.X k) hj f'.1 ρ) 0 :=
    fun ρ => congrFun hz ρ
  have h1' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f.2 f'.2 ρ (hmo ρ)
  have h2' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f'.2 f.2 ρ (hmo ρ).symm
  have hx : (U.un k f).x = (U.un k f').x := PointWell.pt_eq_of_block hU hσ k f f' h1' h2'
  have hg : (hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1 =
      (Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i)ᴴ *
        (hodgeMet Z U).gram (cxPt Z (U.un k f')) (cxFrame Z (U.un k f')) τ.1 *
        Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i :=
    eigGram_of_comb (hodgeMet Z U) _ _ hx τ.1 _ (fun i => lie_comb_of_block hU hσ k f f' h1' h2' τ.1 i)
  rw [hg, hodgeMet_gram_orth Z hσ hU (x := f') h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_submatrix_sq]
  set e := Fin.cast (mult_psi τ).symm
  have he : Function.Bijective e := (finCongr (mult_psi τ).symm).bijective
  rw [Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
  have hKe : (Matrix.of fun b i : Fin (Dw.mult τ.1) =>
      coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i).submatrix e e =
      Matrix.of fun b i : Fin Dw.p => coef (U.X k) f.1 f'.1 τ'.1 b i := by
    ext b i; rw [hτ]; rfl
  obtain ⟨hco1, -⟩ := hodge_co (U.X k) hj hp h1 τ'
  rw [hKe, coef_eq_coW_change (U.X k) hj hp f.2 f'.2 τ' (hmo τ'), hmo τ',
    eq_of_conj_eq_one (isUnit_coW _ _ hp f'.2 _) hco1]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeGenUnf
end
end

