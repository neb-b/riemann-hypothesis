module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
section
noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set

def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ

def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ

def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)

end GlobalTheory.SphereMeanDrop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficient
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  intro n g g'
  have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
    unfold pPart; fun_prop
  have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
    unfold qPart; fun_prop
  refine continuous_of_dominated (bound := fun x => SchwartzMap.seminorm ℂ 0 0 g * ‖g' x‖) ?_ ?_ ?_ ?_
  · intro w
    exact (((continuous_phase w).mul (g.continuous.comp (continuous_id.add continuous_const))).mul
      (continuous_star.comp g'.continuous)).aestronglyMeasurable
  · intro w
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, norm_mul, norm_phase, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  · exact (SchwartzMap.integrable g').norm.const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, phase]
    fun_prop

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem contDiffOn_one_wdb_of_contDiffOn_two_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y) U :=
    hg.fderiv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (Complex.I • bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) U :=
    (h1.add (contDiffOn_const.mul h2)).div_const 2
  have e : wdb n l g = fun y =>
      (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_wd_of_contDiffOn_one_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by
  have hD : ContinuousOn (fun y => fderiv ℝ g y) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun y => fderiv ℝ g y (bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ g y (Complex.I • bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h3 : ContinuousOn
      (fun y => (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2) U :=
    (h1.sub (continuousOn_const.mul h2)).div_const 2
  have e : wd n j g = fun y =>
      (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_cHess_of_contDiffOn_two :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  intro n U φ hU hφ j l
  have hc : ContDiffOn ℝ 2 (fun v => (φ v : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hb := contDiffOn_one_wdb_of_contDiffOn_two_isOpen hU hc l
  simpa only [cHess, Matrix.of_apply] using continuousOn_wd_of_contDiffOn_one_isOpen hU hb j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
section
open MvPolynomial
open scoped ContDiff
open GlobalTheory.PsCo.Pc1

noncomputable section

namespace GlobalTheory.PsCo.Pc1.B

theorem sb_derivcut (H : ℝ → ℝ) (hH : IsCutFn H) : IsCutFn (deriv H) := by
  obtain ⟨hc, R, hR⟩ := hH
  refine ⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩
  have h : H =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy
    exact hR y (le_of_lt hy)
  rw [h.deriv_eq]
  simp

theorem sb_evrp {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sb_degmono {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (s : _) (a : ℂ) :
    (dZ ε Z (monomial s a)).totalDegree ≤ (monomial s a).totalDegree := by
  refine induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a
  · intro a
    have : dZ ε Z (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact (dZ ε Z).map_algebraMap a
    rw [this]; simp
  · intro p v ih
    by_cases hp : p = 0
    · simp [hp]
    rw [Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (add_le_add le_rfl ?_)
      simp only [dZ, mkDerivation_X]
      cases v with
      | inl x =>
        simp only [Sum.elim_inl]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
      | inr x =>
        simp only [Sum.elim_inr]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega

theorem sb_degdz {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (P : Poly n) :
    (dZ ε Z P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (sb_degmono ε Z m _).trans ?_
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

theorem sb_degrp {n : ℕ} (ε : Fin n → Bool) : (rP ε : Poly n).totalDegree ≤ 2 := by
  unfold rP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem sb_evderiv {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : D (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [this, eval_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p v hp =>
    have h := hp.fun_mul (hγ v)
    simp only [map_mul, eval_X]
    refine h.congr_deriv ?_
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]
    ring

theorem sb_curve {n : ℕ} (Z g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) a b)
      (((NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) * Z -
        Z * (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) a b) s := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s :=
    hasDerivAt_exp_smul_const _ _
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s :=
    hasDerivAt_exp_smul_const _ _
  have h3 := (h1.mul_const g).mul h2
  have hc : Commute Z (NormedSpace.exp (s • Z)) := ((Commute.refl Z).smul_right s).exp_right
  have hc' : Commute (-Z) (NormedSpace.exp (s • (-Z))) := ((Commute.refl (-Z)).smul_right s).exp_right
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  have h4 := L.hasFDerivAt.comp_hasDerivAt s h3
  simp only [Function.comp_def] at h4
  have e : ∀ u : ℝ, (u : ℂ) • Z = u • Z := fun u => by simp
  simp only [e, smul_neg] at *
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_
  show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _
  have hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) =
      NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z -
        Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z)) := by
    rw [← hc'.eq]; noncomm_ring
  rw [hm]

theorem sb_evcurve {n : ℕ} (ε : Fin n → Bool) (Z g : Mat n) (s : ℝ) (P : Poly n) (hZ : LieU ε Z) :
    HasDerivAt (fun u : ℝ => ev (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) P) (ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z P)) s := by
  refine sb_evderiv (dZ ε Z)
    (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P
  have hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b) := fun a b => (hZ a b).symm
  rintro (x | x)
  · refine (sb_curve Z g s x.1 x.2).congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  · refine (sb_curve Z g s x.1 x.2).star.congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']

theorem cutoffPolynomial_conjugation_deriv_mem_shapeSpan : StBasDeriv := by
  intro n ε Z H P hZ hH
  refine ⟨?_, fun g s => ?_⟩
  · have h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩
      have := (sb_degdz ε Z (rP ε)).trans (sb_degrp ε)
      exact (totalDegree_mul _ _).trans (by omega)
    have h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩
      exact (sb_degdz ε Z P).trans (by omega)
    have e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P) := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  · have hE := sb_evcurve ε Z g s (rP ε) hZ
    simp only [sb_evrp] at hE
    obtain ⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε)) := ⟨_, rfl⟩
    rw [← hc] at hE
    have hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE
      simpa [Function.comp_def] using this
    have him : c.im = 0 := by
      have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE
      simp [Function.comp_def] at h1
      exact h1.unique (hasDerivAt_const _ _)
    have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
    have hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) :=
      ((hH.1.differentiable (by simp)) _).hasDerivAt
    have hcomp := (hHd.comp s hre).ofReal_comp
    have hP := sb_evcurve ε Z g s P hZ
    have htot := hcomp.fun_mul hP
    refine htot.congr_deriv ?_
    simp only [adBas, bas, map_mul, ← hc, Function.comp_apply]
    rw [← hcre]
    simp only [Complex.ofReal_re, Complex.ofReal_mul]
    ring

end GlobalTheory.PsCo.Pc1.B
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

end GlobalTheory.SepModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicIrreducibleOfNotDvdDiscr
section
namespace GlobalTheory

open Polynomial NumberField

theorem cyclotomic_irreducible_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by
  intro E _ _ l hl hd
  refine ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt hl fun P hP hlP => ?_
  exact (not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.1 hl)).1 hd P hP
    (by simpa using hlP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMBlockEntries
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem dM_X_inl_entry {n : ℕ} (ε : Fin n → Bool) (x : Mode ε) (a b : Fin n) :
    dM ε x (X (Sum.inl (a, b))) =
      (if x.1.1 = b then X (Sum.inl (a, x.1.2)) else 0) - (if a = x.1.2 then X (Sum.inl (x.1.1, b)) else 0) := by
  classical
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single x.1.2]
    · by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single x.1.1]
    · by_cases h : a = x.1.2
      · simp [Matrix.single_apply, h]
      · simp [Matrix.single_apply, h, Ne.symm h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp

theorem dM_block_entries : BlockDeterminantCondition := by
  intro n ε a b hab
  classical
  cases ha : ε a with
  | true =>
    refine ⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩
    have hne : a ≠ x.1.2 := by
      intro h
      have := x.2.2
      rw [← h, ha] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]
    · by_cases h : x.1.1 = b <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  | false =>
    have hb : ε b = false := by rw [← hab, ha]
    refine ⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩
    have hne : x.1.1 ≠ b := by
      intro h
      have := x.2.1
      rw [h, hb] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]
    · by_cases h : a = x.1.2 <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMDetbPEqZero
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem modeDerivation_det_eq_zero : GlobalTheory.PsCo.Cw2a.T_dM_detb := by
  intro n ε x
  let Mx : Matrix (Fin n) (Fin n) (Poly n) := Matrix.of fun a b => X (Sum.inr (a, b))
  let W : Matrix (Fin n) (Fin n) (Poly n) := (barM ε (Matrix.single x.1.2 x.1.1 1)).map C
  have hD : ∀ i j, dM ε x (Mx i j) = (Mx * W - W * Mx) i j := by
    intro i j
    simp only [dM, dZ, Mx, W, Matrix.of_apply, mkDerivation_X, Sum.elim_inr, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_sub_distrib]
  have key := _root_.GlobalTheory.DetDeriv.main (dM ε x) Mx
  have hdet : detbP n = Mx.det := rfl
  rw [hdet, key]
  simp_rw [hD]
  have htr : ∑ i, ∑ j, Mx.adjugate j i * (Mx * W - W * Mx) i j
      = Matrix.trace (Mx.adjugate * (Mx * W - W * Mx)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  rw [htr, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc Mx.adjugate Mx W, Matrix.adjugate_mul,
    ← Matrix.mul_assoc Mx.adjugate W Mx, Matrix.trace_mul_comm (Mx.adjugate * W) Mx,
    ← Matrix.mul_assoc Mx Mx.adjugate W, Matrix.mul_adjugate, sub_self]

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMuEqExtDerivation
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem coefM_apply_eq_coeff {n L : ℕ} (k : ℕ) (s : PolyM n L) :
    coefM n L k s = (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) s).coeff k := by
  simp only [coefM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    Polynomial.lcoeff_apply]

theorem dMu_eq_extDerivation {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) :
    dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := by
  unfold dMu
  refine congrArg _ (funext fun w => ?_)
  cases w with
  | none => rfl
  | some v => simp only [inM]

theorem coefM_dMu : T_coefM_dMu := by
  intro n L ε x k s
  have h := GlobalTheory.coeff_optionEquivLeft_extDerivation (dL L ε x) k s
  rw [coefM_apply_eq_coeff, coefM_apply_eq_coeff, ← h]
  have e : dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := dMu_eq_extDerivation ε x
  refine congrArg (fun D : Derivation ℂ (PolyM n L) (PolyM n L) => (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) (D s)).coeff k) (e.trans ?_)
  refine congrArg _ (funext fun w => ?_)
  cases w <;> rfl

end GlobalTheory.PsCo.Cw2a
end

