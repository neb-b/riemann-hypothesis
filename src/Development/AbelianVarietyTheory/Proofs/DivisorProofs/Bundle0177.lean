module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeFormComplexStructureBaseCh
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

theorem form_cx_coord (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by
  rw [form_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

theorem form_cx_basis (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by
  rw [form_cx_coord]
  obtain ⟨i0, a⟩ := p
  obtain ⟨j0, b⟩ := q
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem form_cx_baseChange_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by
  set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb
  set c := b.repr x with hc
  have hx' : x = ∑ p, c p • b p := (b.sum_repr x).symm
  have key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ) := by
    conv_lhs => rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb,
      Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv
  have key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    rw [key, Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec,
      Matrix.map_apply, Finset.mul_sum, hv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key2]
  have hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    intro α
    by_cases h0 : v α = 0
    · simp [h0]
    · simpa using (hS.dotProduct_mulVec_pos h0).le
  have hne : c ≠ 0 := by
    intro h; apply hx; rw [hx']; simp [h]
  obtain ⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Finsupp.ext h)
  have hα : v α ≠ 0 := fun h => hp (by simpa [hv] using congrFun h i)
  have hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    simpa using hS.dotProduct_mulVec_pos hα
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))

end GlobalTheory.UnitaryStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationUniformizerIntegralClosureEqExpNegRamifStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (π : R), Irreducible π → P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  first | exact @GlobalTheory.valuation_uniformizer_integralClosure | exact GlobalTheory.valuation_uniformizer_integralClosure | (intros; apply GlobalTheory.valuation_uniformizer_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamard
section
open MeasureTheory

namespace GlobalTheory.CoordBox

theorem volume_coordBox_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K]
    (w : K → V) (t : ℝ) (ht : 0 ≤ t) (hK : Fintype.card K = Module.finrank ℝ V) :
    MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  classical
  set n := Fintype.card K with hn
  let o : OrthonormalBasis K ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hK).symm
  let v : K → V := fun k => (2 * t) • w k
  let a : V := -∑ k, t • w k
  have hsub : {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ⊆ (fun x => x + a) '' parallelepiped v := by
    rintro y ⟨c, hc, rfl⟩
    set s : K → ℝ := fun k => (c k + t) / (2 * t) with hs
    have hkey : ∀ k, s k * (2 * t) = c k + t := by
      intro k
      rcases ht.eq_or_lt with h0 | hpos
      · have hck : c k = 0 := by
          have := hc k
          rw [← h0] at this
          exact abs_nonpos_iff.mp this
        simp [hs, ← h0, hck]
      · simp only [hs]
        field_simp
    refine ⟨∑ k, s k • v k, ?_, ?_⟩
    · rw [mem_parallelepiped_iff]
      refine ⟨s, ?_, rfl⟩
      constructor
      · intro k
        have h1 := (abs_le.mp (hc k)).1
        exact div_nonneg (by linarith) (by linarith)
      · intro k
        have h2 := (abs_le.mp (hc k)).2
        exact div_le_one_of_le₀ (by linarith) (by linarith)
    · simp only [v, a, smul_smul, hkey, add_smul, Finset.sum_add_distrib]
      abel
  have hvol : volume (parallelepiped v) = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := by
    rw [← o.addHaar_eq_volume, MeasureTheory.Measure.addHaar_parallelepiped]
    congr 1
    have hsm : o.toBasis.det v = (∏ _k : K, (2 * t)) • o.toBasis.det w :=
      o.toBasis.det.toMultilinearMap.map_smul_univ (fun _ => 2 * t) w
    rw [hsm, Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)]
  have hdet : |o.toBasis.det w| ≤ ∏ k, ‖w k‖ := by
    have := GlobalTheory.Hadamard.norm_orthonormalBasis_det_le (𝕜 := ℝ) o w
    simpa [Real.norm_eq_abs] using this
  calc volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ volume ((fun x => x + a) '' parallelepiped v) := measure_mono hsub
    _ = volume (parallelepiped v) := by
        rw [Set.image_add_right, measure_preimage_add_right]
    _ = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := hvol
    _ ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hdet (pow_nonneg (by linarith) _)

end GlobalTheory.CoordBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixedStatement
section
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  first | (exact @GlobalTheory.weightSpace_iff_idempotent_fixed) | (exact GlobalTheory.weightSpace_iff_idempotent_fixed) | (intros; apply GlobalTheory.weightSpace_iff_idempotent_fixed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPosStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSpace_tensor_ringHom_finrank_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.weightSpace_tensor_ringHom_pos) | (exact GlobalTheory.weightSpace_tensor_ringHom_pos) | (intros; apply GlobalTheory.weightSpace_tensor_ringHom_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedDetDivergenceMemIdeal
section
open MvPolynomial

namespace GlobalTheory

theorem weighted_det_divergence_mem_ideal : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (δ0 : Derivation K R R) (I : Ideal R) (M : Matrix ι ι R) (a b : ι → R) (w t ρ : R), (∀ i j, δ0 (M i j) = δ i (a j)) → (∀ h i j, δ h (M i j) = δ i (M h j)) → δ0 w = 0 → (∀ i, δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j ∈ I) → ρ = ∑ j, b j * a j → δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * ∑ j, M.adjugate j i * a j) + t * δ i ρ * (w * ∑ j, M.adjugate j i * a j)) ∈ I := by
  intro K R _ _ _ ι _ _ δ δ0 I M a b w t ρ h0 hM hw hI hρ
  set c : ι → R := fun i => ∑ j, M.adjugate j i * a j with hc
  have hdet : δ0 M.det = ∑ i, δ i (c i) := by
    rw [_root_.GlobalTheory.DetDeriv.main δ0 M]
    have hp := _root_.GlobalTheory.PiolaAlg.piola_identity δ M hM
    have h1 : ∀ i, δ i (c i) = ∑ j, M.adjugate j i * δ0 (M i j) + ∑ j, a j * δ i (M.adjugate j i) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hc, map_sum, Derivation.leibniz, smul_eq_mul, h0, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, a j * δ i (M.adjugate j i) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hp j, mul_zero]
    simp only [h1, Finset.sum_add_distrib, h2, add_zero]
  have hadj : ∀ k, ∑ i, c i * M i k = M.det * a k := by
    intro k
    have h3 : ∀ j, ∑ i, M.adjugate j i * M i k = if j = k then M.det else 0 := by
      intro j
      have := congrFun (congrFun (Matrix.adjugate_mul M) j) k
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    calc ∑ i, c i * M i k = ∑ j, a j * ∑ i, M.adjugate j i * M i k := by
          simp only [hc, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = M.det * a k := by
          simp only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  have hrho : ∑ i, c i * (w * ∑ j, M i j * b j) = ρ * (w * M.det) := by
    calc ∑ i, c i * (w * ∑ j, M i j * b j) = ∑ j, w * b j * ∑ i, c i * M i j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ρ * (w * M.det) := by
          rw [hρ, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by rw [hadj]; ring
  have key : δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i))
      = - ∑ i, c i * (δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j) := by
    rw [Derivation.leibniz, hw, smul_zero, add_zero, smul_eq_mul, hdet, ← hrho, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  change δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) ∈ I
  rw [key]
  exact I.neg_mem (I.sum_mem fun i _ => I.mul_mem_left _ (hI i))

end GlobalTheory
end

