module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace TermBoundEq

theorem flagIntegralReal_rootRingToReal (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h P) = (flagIntegral f N P : ℝ) := by
  subst h
  have hid : (Prod.map id (finCongr (rfl : j + k = j + k)) : Fin f × Fin (j + k) → _) = id :=
    funext fun _ => rfl
  have : rootRingToReal f (j + k) j k rfl P = map (algebraMap ℚ ℝ) P := by
    simp only [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hid,
      rename_id_apply]
  rw [this, flagIntegralReal_map]

def coeffMap {σ : Type*} (φ : Module.Dual ℚ ℝ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ d ∈ P.support, monomial d (φ (AddMonoidAlgebra.coeff P d))

variable {σ : Type*} (φ : Module.Dual ℚ ℝ)

theorem coeff_coeffMap (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap φ P) d = φ (AddMonoidAlgebra.coeff P d) := by
  classical
  rw [coeffMap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [notMem_support_iff.1 hd, map_zero]

theorem coeffMap_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    coeffMap φ (∑ i ∈ s, P i) = ∑ i ∈ s, coeffMap φ (P i) := by
  ext d
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_coeffMap, coeff_sum, map_sum]

theorem coeffMap_map_mul (R : MvPolynomial σ ℚ) (P : MvPolynomial σ ℝ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R * P) = R * coeffMap φ P := by
  classical
  ext d
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_coeffMap, coeff_mul, coeff_mul, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_coeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem coeffMap_map (R : MvPolynomial σ ℚ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R) = φ 1 • R := by
  ext d
  rw [coeff_coeffMap, coeff_map, coeff_smul, smul_eq_mul, ← mul_one (algebraMap ℚ ℝ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem dual_flagIntegralReal (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    φ (flagIntegralReal f N P) = flagIntegral f N (coeffMap φ P) := by
  have hterm : ∀ α : Fin f × Fin N →₀ ℕ,
      AddMonoidAlgebra.coeff P α * ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) *
          α.prod (fun _ e => (e.factorial : ℝ)) =
        (AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ e => (e.factorial : ℚ))) • AddMonoidAlgebra.coeff P α := by
    intro α
    rw [Rat.smul_def]
    simp only [Finsupp.prod, Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast]
    ring
  show φ (∑ α ∈ _, _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hterm, map_sum, map_smul, smul_eq_mul, flagIntegral, coeff_coeffMap]
  exact sum_congr rfl fun α _ => by ring

theorem flagIntegral_sub_smul (f N : ℕ) (A B : RootRing f N) (s : ℚ) :
    flagIntegral f N (A - s • B) = flagIntegral f N A - s * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_smul, smul_eq_mul]
  ring

end TermBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StaircaseIsHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem CoinvAtTop.closed : CoinvAtTop.Statement :=
  CoinvAtTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof)

namespace FlagProportional

theorem staircase_isHomogeneous (f j k : ℕ) :
    (monomial (Coinv.staircase f (j + k)) (1 : ℝ)).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  show ∑ v, (Coinv.staircase f (j + k)) v = Coinv.coinvTop f (j + k)
  rw [← Coinv.sum_staircase_exponents]
  simp [Coinv.staircase]

theorem eval_top (f j k : ℕ) (L : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ)
    (hL : ∀ (m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), 1 ≤ m →
      m ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k → G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k - m) →
        L (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0)
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (hG : G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k)) (c : ℝ)
    (hc : G - C c * monomial (Coinv.staircase f (j + k)) 1 ∈ Coinv.psumIdeal ℝ f (j + k)) :
    L G = c * L (monomial (Coinv.staircase f (j + k)) 1) := by
  classical
  set D := IndefiniteRowSideFullHecke.RestTerms.dimFl f j k
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  obtain ⟨Q, hQ, hEq⟩ := CoinvIdealComponent.proof CoinvIdealRepresentation.proof
    HomogeneousComponentMul.proof ℝ f (j + k) _ hc D
  have hJ : (G - C c * s).IsHomogeneous D := hG.sub ((staircase_isHomogeneous f j k).C_mul c)
  have hcomp : homogeneousComponent D (G - C c * s) = G - C c * s := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hJ), if_pos rfl]
  have e1 := hcomp.symm.trans hEq
  have e2 : G - C c * s = homogeneousComponent D
      (∑ m ∈ Finset.Icc 1 (j + k), ∑ b : Fin f, Coinv.bps ℝ f (j + k) m b * Q m b) := by
    rw [← e1, hcomp]
  have hzero : L (G - C c * s) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hp : (Coinv.bps ℝ f (j + k) m b).IsHomogeneous m :=
      IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (hQ m b)))]
    split_ifs with h
    · exact hL m b (Q m b) hm1 (by omega) (hQ m b)
    · exact map_zero L
  calc L G = L (G - C c * s) + L (C c * s) := by rw [← map_add (f := _), sub_add_cancel]
    _ = c * L s := by rw [hzero, zero_add, C_mul', map_smul, smul_eq_mul]

end FlagProportional


open FlagProportional in
theorem FlagIntegralProportional.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.FlagIntegralProportional.Statement := by
  intro f j k _ _ _ I hI
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  have hdd : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      ∃ c : ℝ, I G = c * I s ∧ IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G = c * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s := by
    intro G hG
    obtain ⟨c, hc⟩ := CoinvAtTop.closed ℝ f (j + k) G hG
    exact ⟨c, eval_top f j k I hI.kills G hG c hc,
      eval_top f j k (IndefiniteRowSideFullHecke.RestTerms.ddConst f j k)
        (fun m τ G hm _ _ => FlagEq.ddConst_psumAt_mul f j k m τ G hm) G hG c hc⟩
  have hs0 : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s ≠ 0 := by
    obtain ⟨c, -, h⟩ := hdd (monomial (FlagEq.rho f (j + k)) 1)
      (isHomogeneous_monomial _ (by rw [FlagEq.rho_degree]; rfl))
    rw [FlagEq.ddConst_monomial_rho] at h
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h
  have hIs : I s ≠ 0 := by
    obtain ⟨G0, hG0, hne⟩ := hI.ne_zero
    obtain ⟨c, h, -⟩ := hdd G0 hG0
    intro h0
    rw [h0, mul_zero] at h
    exact hne h
  refine ⟨I s / IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s, div_ne_zero hIs hs0, fun G hG => ?_⟩
  obtain ⟨c, h1, h2⟩ := hdd G hG
  rw [h1, h2]
  field_simp

end

end GroundTheory.Heights₂.Heights.RestTerms
end

