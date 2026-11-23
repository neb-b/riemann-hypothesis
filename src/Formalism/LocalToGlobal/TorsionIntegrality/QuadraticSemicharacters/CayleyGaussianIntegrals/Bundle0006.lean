module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.TaylorMvLinear
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.IteratedDerivLine
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

theorem lineRestr_hasSubst {K : Type*} [CommRing K] {n : Type*} [Finite n] (v : n → K) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    have : PowerSeries.constantCoeff (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K) = 0 := by simp
    exact this

theorem lineRestr_monomial {K : Type*} [CommRing K] {n : Type*} [Fintype n] (v : n → K) (d : n →₀ ℕ) :
    (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]

theorem lineCoeff' : LineCoeff := by
  intro K _ n _ _ v T k
  unfold lineRestr
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (lineRestr_hasSubst v)]
  have key : ∀ d : n →₀ ℕ, MvPowerSeries.coeff d T •
      MvPowerSeries.coeff (Finsupp.single () k)
        (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = if k = ∑ i, d i then MvPowerSeries.coeff d T * ∏ i, v i ^ d i else 0 := by
    intro d
    rw [lineRestr_monomial]
    have : MvPowerSeries.coeff (Finsupp.single () k)
        (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K)
        = PowerSeries.coeff k (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K) := rfl
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  rw [finsum_congr key]
  rw [finsum_eq_sum_of_support_subset (s := Finset.finsuppAntidiag Finset.univ k)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [if_pos hd.1.symm]
  · intro d hd
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hd
    obtain ⟨h, -⟩ := hd
    simp [Finset.mem_finsuppAntidiag, h]

theorem LineUnique_of (h : LineCoeff) : LineUnique := by
  classical
  intro K _ _ n _ T T' hv
  ext ν
  set k := ∑ i, ν i with hk
  let p : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T)
  let q : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T')
  have hpq : p = q := by
    refine MvPolynomial.funext fun v => ?_
    have h1 := h K n v T k
    have h2 := h K n v T' k
    rw [hv v, h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, q, map_sum, MvPolynomial.eval_monomial]
    simp only [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    exact h1.symm
  have hν : ν ∈ Finset.finsuppAntidiag Finset.univ k := by simp [Finset.mem_finsuppAntidiag, hk]
  have hc : ∀ S : MvPowerSeries n K, AddMonoidAlgebra.coeff (∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
      MvPolynomial.monomial μ (MvPowerSeries.coeff μ S)) ν = MvPowerSeries.coeff ν S := by
    intro S
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' _ ν, if_pos hν]
  rw [← hc T, ← hc T']
  exact congrArg (fun R => AddMonoidAlgebra.coeff R ν) hpq

theorem lineUnique' : LineUnique := LineUnique_of lineCoeff'

def cntVec {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) : n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (Finset.univ.filter fun j => f j = i).card

theorem cntVec_apply {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) (i : n) :
    cntVec f i = (Finset.univ.filter fun j => f j = i).card := rfl

theorem cntVec_sum {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) :
    ∑ i, cntVec f i = k := by
  simp only [cntVec_apply]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
  simp

theorem cntVec_prod {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} {K : Type*} [CommMonoid K] (v : n → K)
    (f : Fin k → n) : ∏ i, v i ^ cntVec f i = ∏ j, v (f j) := by
  rw [← Finset.prod_fiberwise Finset.univ f (fun j => v (f j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cntVec_apply, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]

theorem taylorMv_coeff {n : Type*} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (k : ℕ) (ν : n →₀ ℕ)
    (h : ν.degree = k) :
    MvPowerSeries.coeff ν (taylorMv F) = ((k.factorial : ℕ) : ℂ)⁻¹ *
      ∑ f : Fin k → n with cntVec f = ν, iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
  subst h
  change ((ν.degree.factorial : ℕ) : ℂ)⁻¹ * _ = _
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; ext i; exact h i
  · intro h i; exact (cntVec_apply f i).symm.trans (DFunLike.congr_fun h i)

theorem multilinear_diag {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin k => n → ℂ) ℂ) (v : n → ℂ) :
    D (fun _ => v) = ∑ f : Fin k → n, (∏ j, v (f j)) * D fun j => Pi.single (f j) (1 : ℂ) := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : D (fun _ => v) = D (fun _ : Fin k => ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ)) := by
    rw [← hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, D.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [D.map_smul_univ (fun j => v (f j)) (fun j => Pi.single (f j) (1 : ℂ)), smul_eq_mul]

theorem iteratedDeriv_line {n : Type*} [Fintype n] (F : (n → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) (v : n → ℂ)
    (k : ℕ) : iteratedDeriv k (fun t : ℂ => F (t • v)) 0 = iteratedFDeriv ℂ k F 0 fun _ => v := by
  let g : ℂ →L[ℂ] (n → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ v
  let s : Set (n → ℂ) := {x | AnalyticAt ℂ F x}
  have hs : IsOpen s := isOpen_analyticAt ℂ F
  have hgs : IsOpen (g ⁻¹' s) := hs.preimage g.continuous
  have h0 : g 0 ∈ s := by simpa [s] using hF
  have hc : ContDiffOn ℂ (k : ℕ∞) F s :=
    AnalyticOnNhd.contDiffOn (fun x hx => hx) hs.uniqueDiffOn
  have := g.iteratedFDerivWithin_comp_right hc hs.uniqueDiffOn hgs.uniqueDiffOn h0 (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hgs h0, iteratedFDerivWithin_of_isOpen k hs h0] at this
  have hfg : (fun t : ℂ => F (t • v)) = F ∘ g := by
    ext t; simp [g]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfg, this]
  simp [g]

theorem TaylorLine_of (h : LineCoeff) : TaylorLine := by
  intro n _ _ F hF v
  ext k
  rw [h ℂ n v (taylorMv F) k, Formalism.L2.Th1.F.taylor0, PowerSeries.coeff_mk, iteratedDeriv_line F hF v k,
    multilinear_diag]
  have h1 : ∀ ν ∈ Finset.finsuppAntidiag (Finset.univ : Finset n) k,
      MvPowerSeries.coeff ν (taylorMv F) * ∏ i, v i ^ ν i
      = ((k.factorial : ℕ) : ℂ)⁻¹ * ∑ f : Fin k → n with cntVec f = ν,
          (∏ j, v (f j)) * iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
    intro ν hν
    rw [Finset.mem_finsuppAntidiag] at hν
    rw [taylorMv_coeff F k ν (by rw [Finsupp.degree_eq_sum]; exact hν.1), mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [← (Finset.mem_filter.1 hf).2, cntVec_prod, mul_comm]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
    Finset.sum_fiberwise_of_maps_to (fun f _ => by simp [Finset.mem_finsuppAntidiag, cntVec_sum]),
    div_eq_inv_mul]

theorem taylorLine' : TaylorLine := TaylorLine_of lineCoeff'

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LineRestrLinSubst
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace TMv

open Formalism.L2.Th1.F (taylor0 taylorRing taylorDeriv)

section Formal

variable {K : Type*} [CommRing K] {n : Type*} [Finite n]

theorem hasSubst_line (v : n → K) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    change PowerSeries.constantCoeff (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K) = 0
    simp

def lineHom (v : n → K) : MvPowerSeries n K →+* PowerSeries K :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst_line v)).toRingHom

theorem lineHom_apply (v : n → K) (T : MvPowerSeries n K) : lineHom v T = lineRestr v T := by
  change MvPowerSeries.substAlgHom (R := K) (hasSubst_line v) T = _
  rw [MvPowerSeries.substAlgHom_apply]
  rfl

theorem lineRestr_add (v : n → K) (S T : MvPowerSeries n K) :
    lineRestr v (S + T) = lineRestr v S + lineRestr v T := by
  simp only [← lineHom_apply, map_add (f := _)]

theorem lineRestr_mul (v : n → K) (S T : MvPowerSeries n K) :
    lineRestr v (S * T) = lineRestr v S * lineRestr v T := by
  simp only [← lineHom_apply, map_mul]

theorem lineRestr_one (v : n → K) : lineRestr v (1 : MvPowerSeries n K) = 1 := by
  simp only [← lineHom_apply, map_one]

theorem lineRestr_sum {ι : Type*} (v : n → K) (s : Finset ι) (T : ι → MvPowerSeries n K) :
    lineRestr v (∑ i ∈ s, T i) = ∑ i ∈ s, lineRestr v (T i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← lineHom_apply, map_sum]

theorem lineRestr_C (v : n → K) (c : K) : lineRestr v (MvPowerSeries.C c) = PowerSeries.C c :=
  MvPowerSeries.subst_C c

theorem lineRestr_X (v : n → K) (i : n) :
    lineRestr v (MvPowerSeries.X i) = PowerSeries.C (v i) * PowerSeries.X :=
  MvPowerSeries.subst_X (hasSubst_line v) i

end Formal

theorem lineRestr_linSubst {K : Type*} [CommRing K] {m n : Type*} [Finite m] [Fintype n]
    (M : Matrix m n K) (v : n → K) (T : MvPowerSeries m K) :
    lineRestr v (linSubst M T) = lineRestr (M.mulVec v) T := by
  have hM : MvPowerSeries.HasSubst
      (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
  unfold linSubst
  conv_lhs => unfold lineRestr
  rw [MvPowerSeries.subst_comp_subst_apply hM (hasSubst_line v)]
  unfold lineRestr
  congr 1
  funext i
  change lineRestr v (∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K)) = _
  rw [lineRestr_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lineRestr_mul, lineRestr_C, lineRestr_X, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]

theorem lineRestr_at1_eq_rescale {K n : Type} [Field K] [Finite n] (v : n → K) (i : n) (f : PowerSeries K) :
    lineRestr v (Formalism.InvariantFactorPaths.G7.at1 i f) = PowerSeries.rescale (v i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  unfold Formalism.InvariantFactorPaths.G7.at1 lineRestr
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hX (hasSubst_line v),
    PowerSeries.rescale_eq_subst, PowerSeries.subst_def, PowerSeries.smul_eq_C_mul]
  congr 1
  funext _
  exact MvPowerSeries.subst_X (hasSubst_line v) i

theorem lineRestr_block {K : Type*} [CommRing K] {n : Type*} [Fintype n] (a : Fin 4)
    (v : Fin 4 × n → K) (T : MvPowerSeries n K) :
    lineRestr v (MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) T)
      = lineRestr (fun i => v (a, i)) T := by
  have hX : MvPowerSeries.HasSubst
      (fun i : n => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  unfold lineRestr
  rw [MvPowerSeries.subst_comp_subst_apply hX (hasSubst_line v)]
  congr 1
  funext i
  exact MvPowerSeries.subst_X (hasSubst_line v) (a, i)

section Analytic

variable {n : Type} [Fintype n]

theorem analyticAt_line {F : (n → ℂ) → ℂ} {t₀ : ℂ} (v : n → ℂ) (hF : AnalyticAt ℂ F (t₀ • v)) :
    AnalyticAt ℂ (fun t : ℂ => F (t • v)) t₀ :=
  hF.comp_of_eq (f := fun t : ℂ => t • v) (analyticAt_id.smul analyticAt_const) rfl

theorem analyticAt_line0 {F : (n → ℂ) → ℂ} (v : n → ℂ) (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun t : ℂ => F (t • v)) 0 :=
  analyticAt_line v (by rwa [zero_smul])

theorem analyticAt_clm {m : Type} [Fintype m] {F : (m → ℂ) → ℂ} (L : (n → ℂ) →L[ℂ] (m → ℂ))
    (hF : AnalyticAt ℂ F 0) : AnalyticAt ℂ (fun w => F (L w)) 0 :=
  hF.comp_of_eq (L.analyticAt 0) (map_zero L)

end Analytic

end TMv

open TMv Formalism.L2.Th1.F

theorem TaylorMvLinear_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvLinear := by
  intro n _ _ F G hF hG
  refine ⟨hU ℂ n _ _ fun v => ?_, fun c => hU ℂ n _ _ fun v => ?_⟩
  · rw [hL n (fun z => F z + G z) (hF.add hG) v, lineRestr_add, hL n F hF v, hL n G hG v]
    exact (taylorRing.1 _ _ (analyticAt_line0 v hF) (analyticAt_line0 v hG)).1
  · rw [hL n (fun z => c * F z) (analyticAt_const.mul hF) v, lineRestr_mul, lineRestr_C, hL n F hF v,
      ← taylorRing.2.1 c]
    exact (taylorRing.1 _ _ analyticAt_const (analyticAt_line0 v hF)).2

theorem TaylorMvMul_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvMul := by
  intro n _ _ F G hF hG
  refine hU ℂ n _ _ fun v => ?_
  rw [hL n (fun z => F z * G z) (hF.mul hG) v, lineRestr_mul, hL n F hF v, hL n G hG v]
  exact (taylorRing.1 _ _ (analyticAt_line0 v hF) (analyticAt_line0 v hG)).2

theorem TaylorMvComp_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvComp := by
  intro m n _ _ _ _ M F hF
  refine hU ℂ n _ _ fun v => ?_
  have hA : AnalyticAt ℂ (fun w : n → ℂ => F (M.mulVec w)) 0 :=
    analyticAt_clm (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) hF
  rw [hL n _ hA v, lineRestr_linSubst, hL m F hF]
  simp only [Matrix.mulVec_smul]

theorem TaylorMvCoord_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvCoord := by
  intro n _ _ i f hf
  refine hU ℂ n _ _ fun v => ?_
  have hA : AnalyticAt ℂ (fun z : n → ℂ => f (z i)) 0 :=
    hf.comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl
  rw [hL n _ hA v, lineRestr_at1_eq_rescale, ← taylorDeriv.2.1 f (v i) hf]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem taylorMv_prod (hU : LineUnique) (hL : TaylorLine) {n : Type} [Fintype n] [DecidableEq n]
    {ι : Type} (s : Finset ι) (F : ι → (n → ℂ) → ℂ) (hF : ∀ i, AnalyticAt ℂ (F i) 0) :
    taylorMv (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, taylorMv (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    refine hU ℂ n _ _ fun v => ?_
    rw [hL n _ analyticAt_const v, lineRestr_one, taylorRing.2.1 1, map_one]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [TaylorMvMul_of hU hL n (F a) _ (hF a) (Finset.analyticAt_fun_prod s fun i _ => hF i), ih]

theorem TaylorMvProd_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvProd := by
  intro n _ _ f hf
  have h := taylorMv_prod hU hL Finset.univ (fun (i : n) (z : n → ℂ) => f i (z i)) fun i =>
    (hf i).comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl
  refine Eq.trans h (Finset.prod_congr rfl fun i _ => ?_)
  exact TaylorMvCoord_of hU hL n i (f i) (hf i)

theorem TaylorMvTens4_of (hU : LineUnique) (hL : TaylorLine) : TaylorMvTens4 := by
  intro n _ _ θ hθ
  have hA : ∀ a : Fin 4, AnalyticAt ℂ (fun z : Fin 4 × n → ℂ => θ (slice a z)) 0 := fun a =>
    analyticAt_clm (ContinuousLinearMap.pi fun i : n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 × n => ℂ) (a, i)) hθ
  have h := taylorMv_prod hU hL Finset.univ (fun (a : Fin 4) (z : Fin 4 × n → ℂ) => θ (slice a z)) hA
  refine Eq.trans h (Finset.prod_congr rfl fun a _ => ?_)
  refine hU ℂ (Fin 4 × n) _ _ fun v => ?_
  rw [hL _ _ (hA a) v, lineRestr_block, hL n θ hθ]
  rfl

theorem TaylorMvInj_of (_hU : LineUnique) (hL : TaylorLine) : TaylorMvInj := by
  intro n _ _ F G hF hG h
  funext v
  have hF' : AnalyticOnNhd ℂ (fun t : ℂ => F (t • v)) Set.univ := fun t _ =>
    analyticAt_line v (hF _ (Set.mem_univ _))
  have hG' : AnalyticOnNhd ℂ (fun t : ℂ => G (t • v)) Set.univ := fun t _ =>
    analyticAt_line v (hG _ (Set.mem_univ _))
  have hT : taylor0 (fun t : ℂ => F (t • v)) = taylor0 fun t : ℂ => G (t • v) := by
    rw [← hL n F (hF 0 (Set.mem_univ _)) v, ← hL n G (hG 0 (Set.mem_univ _)) v, h]
  have hE := taylorDeriv.2.2 _ _ (hF' 0 (Set.mem_univ _)) (hG' 0 (Set.mem_univ _)) hT
  have := congrFun (hF'.eq_of_eventuallyEq hG' hE) 1
  simpa using this

end Formalism.L2.Th1.H
end
end

