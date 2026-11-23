module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentConjCongruenceOfPowFive
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.OrderAdditiveConjugation

variable {E : Type} [Field E] [NumberField E]

private theorem oh_zero : (0 : A E) ∈ Oh E := by
  refine ⟨rfl, fun v => ?_⟩
  have h : ((0 : A E).2 v) = 0 := rfl
  rw [h, map_zero]
  exact zero_le_one

private theorem oh_add {c d : A E} (hc : c ∈ Oh E) (hd : d ∈ Oh E) : c + d ∈ Oh E := by
  refine ⟨by show c.1 + d.1 = 0; rw [hc.1, hd.1, add_zero], fun v => ?_⟩
  have h : ((c + d).2 v) = c.2 v + d.2 v := rfl
  rw [h]
  exact (Valuation.map_add_le _ (hc.2 v) (hd.2 v))

private theorem oh_neg {c : A E} (hc : c ∈ Oh E) : -c ∈ Oh E := by
  refine ⟨by show -c.1 = 0; rw [hc.1, neg_zero], fun v => ?_⟩
  have h : ((-c).2 v) = -(c.2 v) := rfl
  rw [h, Valuation.map_neg]
  exact hc.2 v

private theorem oh_nat (n : ℕ) {c : A E} (hc : c ∈ Oh E) : (n : A E) * c ∈ Oh E := by
  induction n with
  | zero => simpa using oh_zero
  | succ n ih =>
    have : ((n + 1 : ℕ) : A E) * c = (n : A E) * c + c := by push_cast; ring
    rw [this]
    exact oh_add ih hc

private theorem oh_mul_of {T c : A E} (hT : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1) (hc : c ∈ Oh E) :
    T * c ∈ Oh E := by
  refine ⟨by show T.1 * c.1 = 0; rw [hc.1, mul_zero], fun v => ?_⟩
  have h : ((T * c).2 v) = H.cp v T * c.2 v := rfl
  rw [h, map_mul]
  exact mul_le_one' (hT v) (hc.2 v)

private theorem rt_mul_nat (L : ℕ) (θ : E) :
    (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt θ := by
  have : (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = algebraMap E (A E) ((L : E) * θ) := rfl
  rw [this, map_mul, map_natCast]

private theorem nat_mul_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = (0, 1) := by
  have hq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · show (L : A ℚ).1 * 0 = 0
    exact mul_zero _
  · show (L : A ℚ).2 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    have : (L : A ℚ).2 = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ) := by
      rw [map_natCast]; rfl
    rw [this, ← map_mul, mul_inv_cancel₀ hq, map_one]

private theorem unit_mul (L : ℕ) (hL : 0 < L) {r : A E} (hr : r ∈ Oh E) :
    ((L : A E) * am E (iota L)) * r = r := by
  have h1 : (L : A E) * am E (iota L) = am E ((L : A ℚ) * iota L) := by
    rw [map_mul, map_natCast]
  rw [h1, nat_mul_iota L hL]
  refine Prod.ext ?_ ?_
  · show (am E ((0, 1) : A ℚ)).1 * r.1 = r.1
    rw [hr.1, mul_zero]
  · show (am E ((0, 1) : A ℚ)).2 * r.2 = r.2
    have : (am E ((0, 1) : A ℚ)).2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, one_mul]

private theorem conj_entry {R : Type} [CommRing R] (O : Set R) (l t : R)
    (hadd : ∀ {c d : R}, c ∈ O → d ∈ O → c + d ∈ O) (hneg : ∀ {c : R}, c ∈ O → -c ∈ O)
    (P Q W : R → R) (hP : ∀ r ∈ O, P r ∈ O) (hQ : ∀ r ∈ O, Q r ∈ O) (hW : ∀ r ∈ O, W r ∈ O)
    (eP : ∀ r ∈ O, l ^ 5 * r = l * P r) (eQ : ∀ r ∈ O, t * (l ^ 5 * r) = l * Q r)
    (eW : ∀ r ∈ O, t * (t * (l ^ 5 * r)) = l * W r)
    (K : Matrix (Fin 2) (Fin 2) R)
    (hK : ∀ i j, ∃ c ∈ O, K i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l ^ 5 * c) :
    ∀ i j, ∃ c ∈ O, (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l * c := by
  obtain ⟨c00, m00, h00⟩ := hK 0 0
  obtain ⟨c01, m01, h01⟩ := hK 0 1
  obtain ⟨c10, m10, h10⟩ := hK 1 0
  obtain ⟨c11, m11, h11⟩ := hK 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
  have q00 := eQ c00 m00
  have q10 := eQ c10 m10
  have q11 := eQ c11 m11
  have p00 := eP c00 m00
  have p01 := eP c01 m01
  have p10 := eP c10 m10
  have p11 := eP c11 m11
  have w10 := eW c10 m10
  have a00 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 = K 0 0 - t * K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a01 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 = (K 0 0 - t * K 1 0) * t + (K 0 1 - t * K 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a10 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 = K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have a11 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 = K 1 0 * t + K 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  intro i j
  fin_cases i <;> fin_cases j
  · refine ⟨P c00 + -Q c10, hadd (hP _ m00) (hneg (hQ _ m10)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 - (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = _
    rw [a00, Matrix.one_apply_eq]
    linear_combination h00 - t * h10 + p00 - q10
  · refine ⟨Q c00 + P c01 + -W c10 + -Q c11, hadd (hadd (hadd (hQ _ m00) (hP _ m01)) (hneg (hW _ m10))) (hneg (hQ _ m11)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 - (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = _
    rw [a01, Matrix.one_apply_ne (by simp)]
    linear_combination t * h00 + h01 - t * t * h10 - t * h11 + q00 + p01 - w10 - q11
  · refine ⟨P c10, hP _ m10, ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 - (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = _
    rw [a10, Matrix.one_apply_ne (by simp)]
    linear_combination h10 + p10
  · refine ⟨Q c10 + P c11, hadd (hQ _ m10) (hP _ m11), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 - (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = _
    rw [a11, Matrix.one_apply_eq]
    linear_combination t * h10 + h11 + q10 + p11

end UpperTheory.OrderAdditiveConjugation

open UpperTheory.OrderAdditiveConjugation in
theorem UpperTheory.unipotent_conj_congruence_of_pow_five :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ), 0 < L → (∀ w : H.P E, Valued.v (H.cp w (rt ((L : E) * D.θ))) ≤ 1) → ∀ κ : GL (Fin 2) (A E), CongE (L ^ 5) κ → CongE L ((nu D ((a : A ℚ) * iota L))⁻¹ * κ * nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a hL hT κ hκ
  obtain ⟨t, htd⟩ : ∃ t, t = D.mkE 0 ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  obtain ⟨ν, hνd⟩ : ∃ ν, ν = nu D ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  rw [← hνd]
  have hν : (ν : Matrix (Fin 2) (Fin 2) (A E)) = !![1, t; 0, 1] := by rw [hνd, htd]; rfl
  have hνi : ((ν⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, -t; 0, 1] := by
    rw [Matrix.coe_units_inv, hν]
    apply Matrix.inv_eq_right_inv
    simp [Matrix.one_fin_two]
  have ht : t = (a : A E) * am E (iota L) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by
    rw [htd, Dat.mkE_def, map_zero, map_mul, map_natCast, zero_add]
  obtain ⟨T, hTd⟩ : ∃ T : A E, T = UpperTheory.ConvolutionTheory.R2.rt ((L : E) * D.θ) := ⟨_, rfl⟩
  have hT' : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1 := by rw [hTd]; exact hT
  have hTe : T = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by rw [hTd, rt_mul_nat]
  have key : ∀ r ∈ Oh E, (L : A E) ^ 2 * t * r = (a : A E) * (T * r) := by
    intro r hr
    have hu := unit_mul L hL hr
    rw [ht, hTe]
    linear_combination ((a : A E) * ((L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ)) * hu
  have main := conj_entry (Oh E) (L : A E) t oh_add oh_neg
    (fun r => ((L ^ 4 : ℕ) : A E) * r)
    (fun r => ((L ^ 2 * a : ℕ) : A E) * (T * r))
    (fun r => ((a ^ 2 : ℕ) : A E) * (T * (T * r)))
    (fun r hr => oh_nat _ hr)
    (fun r hr => oh_nat _ (oh_mul_of hT' hr))
    (fun r hr => oh_nat _ (oh_mul_of hT' (oh_mul_of hT' hr)))
    (fun r _ => by push_cast; ring)
    (fun r hr => by
      have := key r hr
      push_cast
      linear_combination (L : A E) ^ 3 * this)
    (fun r hr => by
      have h1 := key r hr
      have h2 := key (T * r) (oh_mul_of hT' hr)
      push_cast
      linear_combination ((L : A E) ^ 3 * t) * h1 + ((L : A E) * (a : A E)) * h2)
  have cast5 : ∀ {x : A E} {c : A E}, x = ((L ^ 5 : ℕ) : A E) * c → x = (L : A E) ^ 5 * c := by
    intro x c h; rw [h, Nat.cast_pow]
  have hinv : (ν⁻¹ * κ * ν)⁻¹ = ν⁻¹ * κ⁻¹ * ν := by group
  intro i j
  constructor
  · obtain ⟨c, hc, e⟩ := main (κ : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).1
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, Units.val_mul, Units.val_mul, hν, hνi]
  · obtain ⟨c, hc, e⟩ := main ((κ⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).2
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, hinv, Units.val_mul, Units.val_mul, hν, hνi]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentNatDivMemMaximalCompactOfNotBadPrime
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : H.Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma map_gl_nU {K : Type} [Field K] [NumberField K] (v : H.P K) (z : A K) :
    Matrix.GeneralLinearGroup.map (H.cp v) (gl (nU z)) = H.nL (H.cp v z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact map_one (H.cp v)
  · rfl
  · exact map_zero (H.cp v)
  · exact map_one (H.cp v)

private lemma val_nat_one {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (hL : (L : 𝓞 E) ∉ w.asIdeal) : Valued.v (L : H.Kv w) = 1 := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (L : 𝓞 E)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hL] at h1
  simpa using h1

private lemma val_nat_le {E : Type} [Field E] [NumberField E] (w : H.P E) (a : ℕ) :
    Valued.v (a : H.Kv w) ≤ 1 :=
  show (a : H.Kv w) ∈ w.adicCompletionIntegers E from natCast_mem _ a

private lemma not_mem_of_bad {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (h : ¬ Bad L (w.under (𝓞 ℚ))) : (L : 𝓞 E) ∉ w.asIdeal := by
  intro hm
  apply h
  show (L : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal
  change (L : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact hm

private lemma cp_iota (v : H.P ℚ) (L : ℕ) : H.cp v (iota L) = (L : H.Kv v)⁻¹ := by
  have h := eq_ratCast ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹
  have e : H.cp v (iota L) = ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹ := rfl
  rw [e, h]
  push_cast
  rfl

private lemma completion_adele_natural {E : Type} [Field E] [NumberField E] (w : H.P E) (L a : ℕ) :
    H.cp w (AdeleBaseChange.adeleMap ℚ E ((a : A ℚ) * iota L)) = (a : H.Kv w) * (L : H.Kv w)⁻¹ := by
  have h : ((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w) =
      (a : H.Kv (AdeleBaseChange.below ℚ w)) * (L : H.Kv (AdeleBaseChange.below ℚ w))⁻¹ := by
    have := map_mul (H.cp (AdeleBaseChange.below ℚ w)) (a : A ℚ) (iota L)
    rw [cp_iota, map_natCast] at this
    exact this
  show SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w)) = _
  rw [h, map_mul, map_inv₀, map_natCast, map_natCast]

theorem UpperTheory.unipotent_natDiv_mem_maximalCompact_of_not_badPrime :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ) (w : H.P E), ¬ Bad L (w.under (𝓞 ℚ)) → Valued.v (H.cp w (rt D.θ)) ≤ 1 → H.KAt w (nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a w hL hθ
  have hL1 := val_nat_one w L (not_mem_of_bad w L hL)
  have hz : Valued.v (H.cp w (D.mkE 0 ((a : A ℚ) * iota L))) ≤ 1 := by
    rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, completion_adele_natural, map_mul, map_inv₀, hL1, inv_one, mul_one]
    calc _ ≤ (1 : _) * 1 := mul_le_mul' (val_nat_le w a) hθ
      _ = 1 := mul_one 1
  show Matrix.GeneralLinearGroup.map (H.cp w) (gl (nU (D.mkE 0 ((a : A ℚ) * iota L)))) ∈ GlobalTheory.LFun.KGL w (n := 2)
  rw [map_gl_nU]
  exact nL_memK hz
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentThetaMemCongruenceOfIntegral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.unipotentTheta_mem_congruence_of_integral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (M d : ℕ), (∀ w : H.P E, Valued.v (H.cp w (rt ((d : E) * D.θ))) ≤ 1) → ∀ c ∈ Oh ℚ, CongE M (nu D ((M : A ℚ) * (d : A ℚ) * c)) := by
  intro E _ _ D M d hd c hc
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  have h0 : (0 : A E) ∈ Oh E := ⟨rfl, fun w => by
    change Valued.v (0 : H.Kv w) ≤ 1
    simp⟩
  have hneg : ∀ s : A E, s ∈ Oh E → -s ∈ Oh E := fun s hs => ⟨by
    change -s.1 = 0
    rw [hs.1, neg_zero], fun w => by
    have e : (-s).2 w = -(s.2 w) := rfl
    rw [e, Valuation.map_neg]
    exact hs.2 w⟩
  have hfst : (AdeleBaseChange.adeleMap ℚ E c).1 = 0 := by
    obtain ⟨c1, c2⟩ := c
    obtain rfl : c1 = 0 := hc.1
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have hb : AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ) ∈ Oh E := by
    refine ⟨?_, fun w => ?_⟩
    · change (AdeleBaseChange.adeleMap ℚ E c).1 * _ = 0
      rw [hfst, zero_mul]
    · have h1 : Valued.v ((AdeleBaseChange.adeleMap ℚ E c).2 w) ≤ 1 :=
        GroundTheory.Global.AdeleBaseChange.mapsTo_completionMap _ w (hc.2 _)
      have e : (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)).2 w =
          (AdeleBaseChange.adeleMap ℚ E c).2 w * H.cp w (rt ((d : E) * D.θ)) := rfl
      rw [e, map_mul]
      exact mul_le_one' h1 (hd w)
  have hx : D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c) = (M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)) := by
    have hr : rt ((d : E) * D.θ) = (d : A E) * rt D.θ := by
      change algebraMap E (A E) ((d : E) * D.θ) = _
      rw [map_mul, map_natCast]
    rw [hk, map_zero, zero_add, map_mul, map_mul, map_natCast, map_natCast, hr]
    ring
  have key : ∀ s : A E, s ∈ Oh E → ∀ i j, ∃ c ∈ Oh E,
      (!![1, (M : A E) * s; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c := by
    intro s hs i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, h0, by simp⟩
    · exact ⟨s, hs, by simp⟩
    · exact ⟨0, h0, by simp⟩
    · exact ⟨0, h0, by simp⟩
  have hinv : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := by
    intro q
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    change (!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) * !![1, -q; 0, 1] = 1
    simp [Matrix.mul_fin_two, Matrix.one_fin_two]
  have hn : nu D ((M : A ℚ) * (d : A ℚ) * c) = gl (nU ((M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)))) := by
    change gl (nU (D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c))) = _
    rw [hx]
  intro i j
  rw [hn, hinv, ← mul_neg]
  exact ⟨key _ hb i j, key _ (hneg _ hb) i j⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem volume_fundamental_domain_two : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
  GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

private theorem int_Wo {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {f : GL (Fin 2) (A E) → ℂ}
    (hf : Continuous f) (h : GL (Fin 2) (A E)) :
    IntegrableOn (fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
  have hg : Continuous fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1) :=
    (hf.comp ((cont_nE D).mul continuous_const)).mul
      (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp (continuous_apply 1))
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hsub : FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C := Set.pi_mono fun _ _ => hs
  unfold adeleMeasurePi
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

theorem UpperTheory.whittakerPeriod_add_smul_and_norm_le :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E),
        (∀ f f' : GL (Fin 2) (A E) → ℂ, Continuous f → Continuous f' → ∀ h, Wo D (f + f') h = Wo D f h + Wo D f' h) ∧
        (∀ (c : ℂ) (f : GL (Fin 2) (A E) → ℂ) h, Wo D (c • f) h = c * Wo D f h) ∧
        ∀ (f : GL (Fin 2) (A E) → ℂ) (B : ℝ) h, (∀ g, ‖f g‖ ≤ B) → ‖Wo D f h‖ ≤ B := by
  intro E _ _ D
  refine ⟨fun f f' hf hf' h => ?_, fun c f h => ?_, fun f B h hB => ?_⟩
  · unfold Wo
    rw [← integral_add (int_Wo D hf h) (int_Wo D hf' h)]
    simp only [Pi.add_apply, add_mul]
  · unfold Wo
    rw [← integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasurePi (ι := Fin 2) ℚ) (s := FS2 ℚ)
      (f := fun u => f (nE D u * h) * ψ (u 1)) (C := B) (by rw [volume_fundamental_domain_two]; exact ENNReal.one_lt_top)
      fun u _ => by rw [norm_mul, UpperTheory.ConvolutionTheory.R2.Pp.norm_ψ, mul_one]; exact hB _
    rwa [measureReal_def, volume_fundamental_domain_two, ENNReal.toReal_one, mul_one] at this
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerScalarMulEqCentralCharSqMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (x : IdeleGroup ℚ) (g : GL (Fin 2) (A E)),
        Wo D φ (em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) * g) = ((ω.1 x : ℂˣ) : ℂ) ^ 2 * Wo D φ g := by
  intro E _ _ D ω φ hφ x g
  have h1 : em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E x) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change AdeleBaseChange.adeleMap ℚ E (Matrix.scalar (Fin 2) (x : A ℚ) i j) =
      Matrix.scalar (Fin 2) (AdeleBaseChange.adeleMap ℚ E (x : A ℚ)) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h2 : ∀ (z : (A E)ˣ) (n : GL (Fin 2) (A E)),
      n * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = Matrix.GeneralLinearGroup.scalar (Fin 2) z * (n * g) := by
    intro z n
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext (Matrix.scalar_commute (z : A E) (fun _ => Commute.all _ _) n.val).symm.eq
  have h3 : ideleNorm ℚ E (ideleEmbedding ℚ E x) = x ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  unfold Wo
  rw [h1, ← integral_const_mul]
  congr 1
  funext u
  rw [h2, hφ.cen, h3, map_pow, Units.val_pow_eq_pow_val, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerSumMulEqSumMulWhittaker
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_sum_mul_eq_sum_mul_whittaker :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ), (∀ i, Continuous (φ i)) → (∀ i, ∃ B : ℝ, ∀ g, ‖φ i g‖ ≤ B) → ∀ h : GL (Fin 2) (A E), Wo D (fun g => ∑ i ∈ s, c i * φ i g) h = ∑ i ∈ s, c i * Wo D (φ i) h := by
  intro E _ _ D ι s c φ hc hb h
  haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    have h1 : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
      GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
    rw [h1]
    exact ENNReal.one_lt_top⟩
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hn : Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
    UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))
  have hi : ∀ i, Integrable (fun u : Fin 2 → A ℚ => φ i (nE D u * h) * ψ (u 1))
      ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := by
    intro i
    obtain ⟨B, hB⟩ := hb i
    refine Integrable.of_bound (C := B)
      (((hc i).comp (hn.mul continuous_const)).mul
        (hψ.comp (continuous_apply 1))).aestronglyMeasurable ?_
    refine ae_of_all _ fun u => ?_
    rw [norm_mul, show ‖ψ (u 1)‖ = 1 from Circle.norm_coe _, mul_one]
    exact hB _
  have e : ∀ u : Fin 2 → A ℚ, (∑ i ∈ s, c i * φ i (nE D u * h)) * ψ (u 1) =
      ∑ i ∈ s, c i * (φ i (nE D u * h) * ψ (u 1)) := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  simp only [Wo, e]
  rw [integral_finsetSum _ fun i _ => (hi i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
end

