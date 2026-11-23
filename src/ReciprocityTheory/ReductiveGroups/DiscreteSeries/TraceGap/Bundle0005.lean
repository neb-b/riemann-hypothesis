module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FfExpWedgeHasDeriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysApplySingle
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0004
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem sgE_cpT (a b : Fin n) :
    sgE ε (cpT (N := N)) cmT a b = LinearMap.lTensor N (sgE ε (cpFock (n := n)) cmFock a b) := by
  have e : ∀ f : Module.End ℂ (Fock n), LinearMap.lTensor N f = Module.End.lTensorAlgHom ℂ (Fock n) N f :=
    fun f => rfl
  unfold sgE
  split_ifs <;> rw [e] <;> simp only [map_sum, map_mul, map_neg, map_zero] <;> rfl

theorem tcoef_eq_sum (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ N (Fock n)) :
    tcoef φ y = ∑ s : Finset (Fin (n * n)), φ (fockBasis n s) • tcoef ((fockBasis n).coord s) y := by
  conv_lhs => rw [tcoef_expand y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, tcoef_tmul]

theorem tco_actDiag (E : Fin n → Fin n → Module.End ℂ N) (X : Matrix (Fin n) (Fin n) ℂ)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) =
      actM E X (tcoef ((fockBasis n).coord s) y) + tcoef ((fockBasis n).coord s ∘ₗ sgX ε X) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actM, diagE, sgE_cpT, eT, sgX, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
      TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, map_sum, map_smul, map_add,
      tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [Finset.smul_sum, Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, mul_comm]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_mul]
  | add y y' hy hy' =>
    rw [map_add (f := _), map_add (f := _), hy, hy', map_add (f := _), map_add (f := _), map_add (f := _)]
    abel

end T

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tco_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (wK hD hk y) =
      ∑ s', (fockBasis n).coord s (ff ε k (fockBasis n s')) • sigD hD hk (tcoef ((fockBasis n).coord s') y) := by
  conv_lhs => rw [tcoef_expand y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, wK, TensorProduct.map_tmul, tcoef_tmul, AlgHom.toLinearMap_apply]

theorem tco_wK_hasDeriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inK ε X) (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    HasDerivAt (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
        (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H))
      ((tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) : D) : H) 0 := by
  have hXh : Xᴴ = -X := ((HW.inK_iff' ε X).1 hX).1
  have hfun : (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
      (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H)) =
      fun t : ℝ => ∑ s', (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X)) (fockBasis n s')) •
        σ (NormedSpace.exp ((t : ℂ) • X)) ((tcoef ((fockBasis n).coord s') y : D) : H) := by
    funext t
    rw [tco_wK, Submodule.coe_sum]
    rfl
  rw [hfun]
  have hc : ∀ s', HasDerivAt (fun t : ℝ => (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X))
      (fockBasis n s'))) ((fockBasis n).coord s (sgX ε X (fockBasis n s'))) 0 := by
    intro s'
    have := hasDerivAt_pi.1 (ff_exp_hasDeriv (ε := ε) hXh (fockBasis n s')) s
    simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using this
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ =>
    (hc s').fun_smul (hD.deriv X hX.1 (tcoef ((fockBasis n).coord s') y))
  convert h using 1
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  simp only [h0, ff_one, AlgHom.id_apply, hσ.1.1, ContinuousLinearMap.one_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [tco_actDiag, Submodule.coe_add, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y, Submodule.coe_sum,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
    simp

def coordH : TensorProduct ℂ D (Fock n) →ₗ[ℂ] (Finset (Fin (n * n)) → H) :=
  LinearMap.pi fun s => D.subtype ∘ₗ tcoef ((fockBasis n).coord s)

theorem coordH_apply (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    coordH y s = ((tcoef ((fockBasis n).coord s) y : D) : H) := rfl

theorem coordH_injective : Function.Injective (coordH (D := D) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot, tcoef_expand y]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : ((tcoef ((fockBasis n).coord s) y : D) : H) = 0 := congrFun hy s
  rw [show tcoef ((fockBasis n).coord s) y = 0 from Subtype.ext this, TensorProduct.zero_tmul]

theorem actDiag_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    actM (diagE ε (eT E) cpT cmT) X y ∈ S' := by
  let T := S'.map (coordH (D := D) (n := n))
  have : FiniteDimensional ℂ T := Module.Finite.map S' coordH
  have hTc : IsClosed (T : Set (Finset (Fin (n * n)) → H)) := Submodule.closed_of_finiteDimensional T
  have hder : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) X y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have h1 : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) ∈ T :=
    fun t => Submodule.mem_map_of_mem (hK _ _ y hy)
  have hmem : coordH (actM (diagE ε (eT E) cpT cmT) X y) ∈ T :=
    hTc.mem_of_tendsto hder.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (h1 _) (h1 _)))
  obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.1 hmem
  rwa [coordH_injective hweq] at hw

theorem diagE_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    diagE ε (eT E) cpT cmT a b y ∈ S' := by
  have h1 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab 1) hy
  have h2 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab Complex.I) hy
  rw [USum.actM_zM] at h1 h2
  have gen : ∀ x y : TensorProduct ℂ D (Fock n),
      x = (1 / 2 : ℂ) • ((x - y) - Complex.I • (Complex.I • x - (-Complex.I) • y)) := by
    intro x y
    rw [smul_sub Complex.I, smul_smul, smul_smul, show Complex.I * Complex.I = -1 from Complex.I_mul_I,
      show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
    module
  have key : diagE ε (eT E) cpT cmT a b y = (1 / 2 : ℂ) •
      ((((1 : ℂ) • diagE ε (eT E) cpT cmT a b - star (1 : ℂ) • diagE ε (eT E) cpT cmT b a) y) -
        Complex.I • (((Complex.I • diagE ε (eT E) cpT cmT a b - star Complex.I • diagE ε (eT E) cpT cmT b a)) y)) := by
    simp only [Complex.star_def, Complex.conj_I, map_one]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul]
    exact gen _ _
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DetOneSubEqSumMinors
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem det_one_sub_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (1 - A).det =
      ∑ s : Finset ι, (-1 : ℂ) ^ s.card * (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have e : Matrix.det (1 - A) =
      Matrix.detRowAlternating ((fun i => (-A) i) + (fun i => (1 : Matrix ι ι ℂ) i)) := by
    refine congrArg Matrix.detRowAlternating ?_
    funext i j
    simp [sub_eq_neg_add]
  rw [e, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine (Matrix.det_piecewise_one_eq_submatrix_det (-A) s).trans ?_
  have hn : (-A).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      -(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) := by
    ext i j
    simp
  rw [hn, Matrix.det_neg, Fintype.card_coe]

theorem fock_repr_ιMulti (S : Finset (Fin (n * n))) (v : Fin S.card → (Fin n × Fin n → ℂ)) :
    (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (Matrix.of fun i j => v i (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  have h1 : (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).exteriorPower S.card).repr
        (exteriorPower.ιMulti ℂ S.card v) (Set.powersetCard.ofCard (rfl : S.card = S.card)) := by
    rw [fockBasis, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
      Set.powersetCard.prodEquiv_symm_apply]
    exact DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ (exteriorPower.ιMulti ℂ S.card v).2
  rw [h1, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

theorem ffMat_diag_det (k : Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin (n * n))) :
    ffMat ε k S S = (Matrix.of fun i j : Fin S.card =>
      adMat ε k (finProdFinEquiv.symm (S.orderEmbOfFin rfl i))
        (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti, fock_repr_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

def physEmb (ε : Fin n → Bool) : {x : Fin n × Fin n // IsPhys ε x} ↪ Fin (n * n) :=
  ⟨fun x => finProdFinEquiv x.1, fun _ _ h => Subtype.ext (finProdFinEquiv.injective h)⟩

theorem ffMat_map_physEmb (k : Matrix (Fin n) (Fin n) ℂ) (s : Finset {x : Fin n × Fin n // IsPhys ε x}) :
    ffMat ε k (s.map (physEmb ε)) (s.map (physEmb ε)) =
      ((Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix
        (Subtype.val : s → _) Subtype.val).det := by
  classical
  set S := s.map (physEmb ε) with hS
  rw [ffMat_diag_det]
  have hmem : ∀ i, ∃ x ∈ s, physEmb ε x = S.orderEmbOfFin rfl i :=
    fun i => Finset.mem_map.1 (S.orderEmbOfFin_mem rfl i)
  let e : Fin S.card → s := fun i => ⟨(hmem i).choose, (hmem i).choose_spec.1⟩
  have he : ∀ i, (((e i : {x : Fin n × Fin n // IsPhys ε x}) : Fin n × Fin n)) =
      finProdFinEquiv.symm (S.orderEmbOfFin rfl i) := by
    intro i
    rw [← (hmem i).choose_spec.2]
    exact (finProdFinEquiv.symm_apply_apply _).symm
  have hp : ∀ i, IsPhys ε (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) :=
    fun i => he i ▸ (e i : {x : Fin n × Fin n // IsPhys ε x}).2
  have hinj : Function.Injective e := by
    intro i j hij
    have h1 := he i
    rw [hij, he j] at h1
    exact (S.orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h1.symm)
  have hcard : Fintype.card (Fin S.card) = Fintype.card s := by simp [S]
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, hcard⟩))]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.ofBijective_apply]
  rw [he i, he j]
  simp only [adMat, if_pos (hp i), if_pos (hp j)]

theorem strPhys_eq_physDet (k : Matrix (Fin n) (Fin n) ℂ) : strPhys ε k = physDet ε k := by
  classical
  have h1 : physDet ε k = (1 - Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
      k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).det := by
    rw [physDet]
    congr 1
  rw [h1, det_one_sub_eq_sum_minors, strPhys]
  symm
  refine Finset.sum_bij (fun s _ => s.map (physEmb ε)) ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsPhysSet]
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hm
    show IsPhys ε (finProdFinEquiv.symm (finProdFinEquiv x.1))
    rw [Equiv.symm_apply_apply]
    exact x.2
  · intro s _ t _ h
    exact Finset.map_injective _ h
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine ⟨Finset.univ.filter (fun x => physEmb ε x ∈ S), Finset.mem_univ _, ?_⟩
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hm
      refine ⟨⟨finProdFinEquiv.symm m, hS m hm⟩, ?_, finProdFinEquiv.apply_symm_apply m⟩
      show finProdFinEquiv (finProdFinEquiv.symm m) ∈ S
      rw [Equiv.apply_symm_apply]
      exact hm
  · intro s _
    rw [ffMat_map_physEmb, Finset.card_map]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.InvoluteExteriorPower
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem involute_exteriorPower {p : ℕ} {w : Fock n} (hw : w ∈ ⋀[ℂ]^p (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute w = ((-1 : ℂ) ^ p) • w := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact involute_ιMulti p v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem gradT_range_ext {V : Submodule ℂ N} {p : ℕ} {z : TensorProduct ℂ N (Fock n)}
    (hz : z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^p (Fin n × Fin n → ℂ)).subtype)) :
    gradT z = ((-1 : ℂ) ^ p) • z := by
  obtain ⟨x, rfl⟩ := hz
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [TensorProduct.map_tmul, gradT, Submodule.coe_subtype, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    rw [involute_exteriorPower w.2, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem gradT_cpcm (i a j b : Fin n) :
    gradT (N := N) * (cpT i a * cmT j b) = cpT i a * cmT j b * gradT := by
  rw [← mul_assoc, gradT_cpT, neg_mul, mul_assoc, gradT_cmT, mul_neg, neg_neg, mul_assoc]

theorem gradT_sgE (a b : Fin n) :
    gradT (N := N) * sgE ε cpT cmT a b = sgE ε cpT cmT a b * gradT := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · simp

theorem gradT_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) (y : TensorProduct ℂ N (Fock n)) :
    gradT (diagE ε (eT E) cpT cmT a b y) = diagE ε (eT E) cpT cmT a b (gradT y) := by
  have h1 := LinearMap.congr_fun (eT_gradT E a b) y
  have h2 := LinearMap.congr_fun (gradT_sgE (ε := ε) (N := N) a b) y
  simp only [mul_apply_eq_comp] at h1 h2
  simp only [diagE, LinearMap.add_apply, map_add (f := _), h1, h2]

theorem gradT_kLowSpan (E : Fin n → Fin n → Module.End ℂ N) {z : TensorProduct ℂ N (Fock n)} {c : ℂ}
    (hz : gradT z = c • z) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) z) : gradT y = c • y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, -, rfl⟩ := hx
    induction l with
    | nil => exact hz
    | cons p l ih =>
      simp only [lowWord]
      rw [gradT_diagE, ih, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

