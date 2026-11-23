module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix Module MeasureTheory
open scoped ComplexOrder Classical

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem blockDiagonal_mulVec_apply {j : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : κ → Matrix (Fin j) (Fin j) ℂ) (z : Fin j × κ → ℂ) (k : Fin j) (v : κ) :
    (blockDiagonal R *ᵥ z) (k, v) = (R v *ᵥ fun k' => z (k', v)) k := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul]

theorem det_blockDiagonal_real {j : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (R : κ → Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det ((Matrix.toLin' (blockDiagonal R)).restrictScalars ℝ) = ∏ v, Complex.normSq (R v).det := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_blockDiagonal, map_prod]
  simp [Algebra.norm_complex_apply]

variable (I : AutInst) (j : ℕ)

def t8Eq : Fin 2 × (Fin j × InfinitePlace I.F) ≃ Fin (2 * I.f * j) :=
  Fintype.equivFinOfCardEq (by simp [card_infinite_places]; ring)

def t8J : (Fin j × InfinitePlace I.F → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  complexToEuclidean (t8Eq I j)

theorem placeEmbedding_norm_sq (z : Fin j × InfinitePlace I.F → ℂ) : ‖t8J I j z‖ ^ 2 = ∑ q, ‖z q‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← (t8Eq I j).sum_comp]
  simp [t8J, complexToEuclidean, Fintype.sum_prod_type, Fin.sum_univ_two, Module.Basis.smulTower_repr,
    Complex.coe_basisOneI_repr, Complex.sq_norm, Complex.normSq_apply, ← sq]
  simp only [Finset.sum_add_distrib]

def placeCoordsBasis : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (Fin j × InfinitePlace I.F → ℂ) :=
  (Pi.basis fun _ : Fin j => embeddingBasis I).map (LinearEquiv.curry ℝ ℂ (Fin j) (InfinitePlace I.F)).symm

theorem placeCoordsBasis_apply (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) (q : Fin j × InfinitePlace I.F) :
    placeCoordsBasis I j p q = if q.1 = p.1 then I.φ q.2 (integralBasis I.E p.2) else 0 := by
  simp [placeCoordsBasis, embeddingBasis, Pi.basis_apply]
  by_cases h : q.1 = p.1
  · rw [if_pos h]
    simp [Function.uncurry_def, h]
  · rw [if_neg h]
    simp [Function.uncurry_def, Pi.single_eq_of_ne h]

def t8B0 : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (EuclideanSpace ℝ (Fin (2 * I.f * j))) :=
  (placeCoordsBasis I j).map (t8J I j)

def t8K : ℝ := volume.real (ZSpan.fundamentalDomain (t8B0 I j))

theorem integral_covolume_pos : 0 < t8K I j := by
  unfold t8K
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range (t8B0 I j)))
      (EuclideanSpace ℝ (Fin (2 * I.f * j))) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℝ (Fin (2 * I.f * j))) s⟩
  refine ENNReal.toReal_pos ?_ ?_
  · exact (ZSpan.isAddFundamentalDomain (t8B0 I j) volume).measure_ne_zero (NeZero.ne volume)
  · exact (ZSpan.fundamentalDomain_isBounded (t8B0 I j)).measure_lt_top.ne

def placeCoords : (Fin j → I.E) →+ (Fin j × InfinitePlace I.F → ℂ) where
  toFun a := fun q => I.φ q.2 (a q.1)
  map_zero' := by
    funext q
    simp
  map_add' a b := by
    funext q
    simp

theorem placeCoords_apply (a : Fin j → I.E) (q : Fin j × InfinitePlace I.F) : placeCoords I j a q = I.φ q.2 (a q.1) := rfl

theorem placeCoords_single (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    placeCoords I j (Pi.single p.1 (integralBasis I.E p.2)) = placeCoordsBasis I j p := by
  funext q
  rw [placeCoords_apply, placeCoordsBasis_apply]
  by_cases h : q.1 = p.1
  · simp [h]
  · simp [h, Pi.single_apply]

def t8O : Submodule ℤ (Fin j → I.E) :=
  Submodule.span ℤ (Set.range fun p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E) =>
    Pi.single p.1 (integralBasis I.E p.2))

theorem mem_integral_vectors (a : Fin j → I.E) (ha : ∀ k, ∃ c : 𝓞 I.E, (c : I.E) = a k) : a ∈ t8O I j := by
  have key : ∀ (k : Fin j) (x : 𝓞 I.E), Pi.single k (x : I.E) ∈ t8O I j := by
    intro k x
    have hx : (x : I.E) = ∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i := by
      conv_lhs => rw [← (RingOfIntegers.basis I.E).sum_repr x]
      simp [integralBasis_apply]
    have hs : Pi.single k (∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i) =
        ∑ i, ((RingOfIntegers.basis I.E).repr x i) • (Pi.single k (integralBasis I.E i) : Fin j → I.E) := by
      funext k'
      by_cases h : k' = k
      · subst h
        simp [Finset.sum_apply]
      · simp [Finset.sum_apply, Pi.single_apply, h]
    rw [hx, hs]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, i⟩, rfl⟩)
  rw [← Finset.univ_sum_single a]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := ha k
  rw [← hc]
  exact key k c

variable {I j}

def t8Rl (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    (Fin j × InfinitePlace I.F → ℂ) →ₗ[ℂ] (Fin j × InfinitePlace I.F → ℂ) :=
  Matrix.toLin' (blockDiagonal R)

def t8T (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    EuclideanSpace ℝ (Fin (2 * I.f * j)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  (t8J I j).toLinearMap ∘ₗ (t8Rl R).restrictScalars ℝ ∘ₗ (t8J I j).symm.toLinearMap

theorem blockLinear_det (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (t8T R) = ∏ v, Complex.normSq (R v).det := by
  unfold t8T
  rw [LinearMap.det_conj]
  exact det_blockDiagonal_real R

theorem blockLinear_det_ne_zero (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    LinearMap.det (t8T R) ≠ 0 := by
  rw [blockLinear_det]
  exact Finset.prod_ne_zero_iff.2 fun v _ => (Complex.normSq_pos.2 (hR v)).ne'

def t8Th (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → I.E) →+ EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  ((t8J I j).toLinearMap.toAddMonoidHom.comp ((t8Rl R).toAddMonoidHom)).comp (placeCoords I j)

theorem blockTransform_apply (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (a : Fin j → I.E) :
    t8Th R a = t8J I j (t8Rl R (placeCoords I j a)) := rfl

theorem blockTransform_single (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ)
    (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    t8Th R (Pi.single p.1 (integralBasis I.E p.2)) = t8T R (t8B0 I j p) := by
  rw [blockTransform_apply, placeCoords_single]
  simp [t8T, t8B0]

theorem blockTransform_norm_sq (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (a : Fin j → I.E) :
    ‖t8Th R a‖ ^ 2 = ∑ v, ∑ k, ‖(R v *ᵥ fun k' => I.φ v (a k')) k‖ ^ 2 := by
  rw [blockTransform_apply, placeEmbedding_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [t8Rl, Matrix.toLin'_apply, blockDiagonal_mulVec_apply, placeCoords_apply]

theorem blockTransform_injective (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    Function.Injective (t8Th R) := by
  intro a b h
  have h1 : t8Rl R (placeCoords I j a) = t8Rl R (placeCoords I j b) := (t8J I j).injective h
  have hdet : (blockDiagonal R).det ≠ 0 := by
    rw [det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hR v
  have hinj : Function.Injective (blockDiagonal R).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have h2 : placeCoords I j a = placeCoords I j b := hinj h1
  funext k
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  exact (I.φ v).injective (congrFun h2 (k, v))

def blockBasis (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (EuclideanSpace ℝ (Fin (2 * I.f * j))) :=
  (t8B0 I j).map ((t8T R).equivOfDetNeZero (blockLinear_det_ne_zero R hR))

theorem blockBasis_apply (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0)
    (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) : blockBasis R hR p = t8T R (t8B0 I j p) := by
  simp [blockBasis]


set_option maxRecDepth 20000 in
theorem covolume_blockBasis (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (blockBasis R hR))) =
      (∏ v, Complex.normSq (R v).det) * t8K I j := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain (blockBasis R hR) volume)]
  rw [Measure.real, ZSpan.measure_fundamentalDomain (blockBasis R hR) volume (t8B0 I j)]
  have hb : (t8B0 I j).det ⇑(blockBasis R hR) = LinearMap.det (t8T R) := by
    have : ⇑(blockBasis R hR) = t8T R ∘ ⇑(t8B0 I j) := funext fun p => blockBasis_apply R hR p
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hb, blockLinear_det, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]
  rfl

theorem map_integral_vectors_span (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    (t8O I j).map (t8Th R).toIntLinearMap = Submodule.span ℤ (Set.range (blockBasis R hR)) := by
  rw [t8O, Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun p => ?_))
  show t8Th R (Pi.single p.1 (integralBasis I.E p.2)) = blockBasis R hR p
  rw [blockTransform_single, blockBasis_apply]

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.FreeQuotientRank
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := by
  simp [uMat]

theorem coordV_mul (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I (x * (y, k)) v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
  have hA : ((x * (y, k)).1 v)⁻¹ = (y v)⁻¹ * (x.1 v)⁻¹ := by
    rw [← _root_.mul_inv_rev]
    rfl
  unfold coordV
  rw [hA, uMat_mul, Matrix.mulVec_mulVec, mul_assoc]

theorem coordV_mul' (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I x v u = uMat (y v) *ᵥ coordV I (x * (y, k)) v u := by
  rw [coordV_mul, Matrix.mulVec_mulVec, ← uMat_mul, mul_inv_cancel, uMat_one, Matrix.one_mulVec]

theorem eventually_uMat_near (I : AutInst) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 (1 : I.Ginf), ∀ v, ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 < δ := by
  rw [Filter.eventually_all]
  intro v
  have c1 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  have c2 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  refine Filter.Eventually.and ?_ ?_
  · exact c1.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)
  · exact c2.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)

theorem eventually_kg_one (I : AutInst) : ∀ᶠ k in 𝓝 (1 : I.Gf), k ∈ I.Kg 1 := by
  have ho := I.topf_open 1 le_rfl
  refine ho.mem_nhds ?_
  exact ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩

theorem sizes_locally_comparable (h4 : LatticeRightInvariant) (h5 : GramDistortionBound) : SizesLocallyComparable := by
  intro I x r hr
  set N := Fintype.card (InfinitePlace I.F)
  set c : ℝ := r ^ (((N + 1 : ℕ) : ℝ)⁻¹) with hcdef
  have hc1 : 1 < c := Real.one_lt_rpow hr (by positivity)
  have hcN : c ^ N ≤ r := by
    calc c ^ N ≤ c ^ (N + 1) := pow_le_pow_right₀ hc1.le (Nat.le_succ N)
      _ = r := Real.rpow_inv_natCast_pow (by linarith) (Nat.succ_ne_zero N)
  set ε : ℝ := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set δ : ℝ := ε ^ 2 / (1 + ε) with hδdef
  have hδ : 0 < δ := by positivity
  have hbound : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 < δ →
      ∀ w : Fin I.n → ℂ, ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2 := by
    intro M hM w
    refine (sum_norm_mulVec_sq_le M w hε).trans ?_
    have hw : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hw
    have h1 : (1 + 1 / ε) * ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 ≤ (1 + 1 / ε) * δ :=
      mul_le_mul_of_nonneg_left hM.le (by positivity)
    have h2 : (1 + 1 / ε) * δ = ε := by
      rw [hδdef]
      field_simp
      ring
    linarith
  have hW : ∀ᶠ z in 𝓝 (1 : I.GA), (∀ v, ∑ i, ∑ l, ‖(uMat (z.1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (z.1 v) - 1) i l‖ ^ 2 < δ) ∧ z.2 ∈ I.Kg 1 := by
    have h := (eventually_uMat_near I hδ).prod_mk (eventually_kg_one I)
    rw [show (1 : I.GA) = (1, 1) from rfl, nhds_prod_eq]
    exact h
  have hx : ∀ᶠ x' in 𝓝 x, (∀ v, ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v) - 1) i l‖ ^ 2 < δ) ∧ (x⁻¹ * x').2 ∈ I.Kg 1 := by
    have ht : Tendsto (fun x' : I.GA => x⁻¹ * x') (𝓝 x) (𝓝 1) := by
      have h := (continuous_const_mul x⁻¹).tendsto x
      rwa [inv_mul_cancel] at h
    exact ht.eventually hW
  filter_upwards [hx] with x' hx'
  obtain ⟨hy, hk⟩ := hx'
  set y := (x⁻¹ * x').1
  set k := (x⁻¹ * x').2
  have hxe : x * (y, k) = x' := by
    change x * ((x⁻¹ * x').1, (x⁻¹ * x').2) = x'
    rw [Prod.mk.eta, mul_inv_cancel_left]
  have hlat : latSet I x' = latSet I x := by
    have h := h4 I x y k hk.1
    rwa [hxe] at h
  have hc1' : ∀ v u, coordV I x' v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
    intro v u
    have h := coordV_mul I x y k v u
    rwa [hxe] at h
  have hc2' : ∀ v u, coordV I x v u = uMat (y v) *ᵥ coordV I x' v u := by
    intro v u
    have h := coordV_mul' I x y k v u
    rwa [hxe] at h
  refine ⟨fun s => ⟨subOfEq I hlat s, ?_⟩, fun s' => ⟨subOfEq I hlat.symm s', ?_⟩⟩
  · exact (size_subOfEq_le I h5 hlat _ hc1' hc1.le (fun v w => hbound _ (hy v).1 w) s).trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s))
  · exact (size_subOfEq_le I h5 hlat.symm _ hc2' hc1.le (fun v w => hbound _ (hy v).2 w) s').trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s'))

end Formalism.L2.SG.Pf.Tau
end
end

