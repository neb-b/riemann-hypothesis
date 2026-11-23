module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory.KZ.CoefVal

variable {l : ℕ} [Fact l.Prime]

private theorem norm_le_one_of_int' (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : PadicAlgCl l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI := c.fin
  exact norm_le_one_of_int' x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem c (u : c.O).2
  have h3 := norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  have h5 := norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)
  refine le_antisymm h2 ?_
  nlinarith

theorem norm_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_p]

theorem exists_unif (c : Coef l) : ∃ ϖ : PadicAlgCl l, ∃ s : ℕ, 0 < s ∧ ‖((l : ℕ) : PadicAlgCl l)‖ = ‖ϖ‖ ^ s ∧
    ∀ x ∈ c.O, x = 0 ∨ ∃ j : ℕ, ‖x‖ = ‖ϖ‖ ^ j := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ y : c.O, y ≠ 0 → ∃ j : ℕ, ‖(y : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ j := by
    intro y hy
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    refine ⟨n, ?_⟩
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlp : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hnorm : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n := by
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((u : c.O) : PadicAlgCl l) * (ϖ : PadicAlgCl l) ^ n := by
      rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
    have h'' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) := by simp
    rw [← h'', h', norm_mul, norm_pow, norm_unit, one_mul]
  refine ⟨ϖ, n, ?_, hnorm, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, norm_l] at hnorm
      linarith
    · exact h
  · intro x hx
    by_cases h : x = 0
    · exact Or.inl h
    · right
      exact key ⟨x, hx⟩ (fun h' => h (congrArg Subtype.val h'))

theorem norm_eq_one_of_pow {z : PadicAlgCl l} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ N = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this

theorem norm_one_sub_pow_le {z : PadicAlgCl l} (hz : ‖z‖ = 1) (b : ℕ) : ‖1 - z ^ b‖ ≤ ‖1 - z‖ := by
  have : 1 - z ^ b = (1 - z) * ∑ i ∈ Finset.range b, z ^ i := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [this, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun i _ => by rw [norm_pow, hz, one_pow])

theorem norm_one_sub_prim {z : PadicAlgCl l} {m : ℕ} (hz : IsPrimitiveRoot z (l ^ (m + 1))) :
    ‖1 - z‖ ^ Nat.totient (l ^ (m + 1)) = ‖((l : ℕ) : PadicAlgCl l)‖ := by
  have hpos : 0 < l ^ (m + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : Polynomial.eval 1 (Polynomial.cyclotomic (l ^ (m + 1)) (PadicAlgCl l)) = l :=
    Polynomial.eval_one_cyclotomic_prime_pow m
  rw [hcyc, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  have hz1 : ‖z‖ = 1 := norm_eq_one_of_pow hpos hz.pow_eq_one
  have h2 : ∀ μ ∈ primitiveRoots (l ^ (m + 1)) (PadicAlgCl l), ‖1 - μ‖ = ‖1 - z‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hpos).1 hμ
    have hμ1 : ‖μ‖ = 1 := norm_eq_one_of_pow hpos hμ'.pow_eq_one
    obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact norm_one_sub_pow_le hz1 i
    · calc ‖1 - z‖ = ‖1 - μ ^ j‖ := by rw [hj]
        _ ≤ ‖1 - μ‖ := norm_one_sub_pow_le hμ1 j
  rw [← h1, norm_prod, Finset.prod_congr rfl h2, Finset.prod_const, hz.card_primitiveRoots]

theorem coeff_cg_of_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ),
    (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) →
    ∀ n, Cg k (F.coeff n) 0 := by
  intro l _ c F k m₁ hF hval n₀
  have hlP : l.Prime := Fact.out
  unfold Cg
  rw [sub_zero]
  by_contra hlt
  push_neg at hlt
  obtain ⟨ϖ, s, hs, hls, hdisc⟩ := exists_unif c
  set q := ‖ϖ‖ with hq
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by have := hlP.pos; positivity
  have hlone : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hlP.one_lt)
  have hl0 : 0 < q ^ s := by rw [← hls, norm_l]; exact hlpos
  have hl1 : q ^ s < 1 := by rw [← hls, norm_l]; exact hlone
  have hq0 : 0 < q := by
    by_contra hc
    push_neg at hc
    have h0 : q = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow hs.ne'] at hl0
    exact lt_irrefl _ hl0
  have hq1 : q < 1 := (pow_lt_one_iff_of_nonneg hq0.le hs.ne').1 hl1
  have hlk : ‖((l : ℕ) : Qbar l) ^ k‖ = q ^ (s * k) := by
    rw [norm_pow, pow_mul]; congr 1
  have hex : ∃ J, ∃ n, ‖F.coeff n‖ = q ^ J := by
    rcases hdisc _ (hF n₀) with h | ⟨j, hj⟩
    · exfalso; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg _))
    · exact ⟨j, n₀, hj⟩
  classical
  have hJ := Nat.find_spec hex
  set J := Nat.find hex with hJdef
  have hle : ∀ n, ‖F.coeff n‖ ≤ q ^ J := by
    intro n
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]; exact pow_le_pow_of_le_one hq0.le hq1.le (Nat.find_min' hex ⟨n, hj⟩)
  have hd := Nat.find_spec hJ
  set d := Nat.find hJ with hddef
  have hbefore : ∀ n < d, ‖F.coeff n‖ ≤ q ^ (J + 1) := by
    intro n hn
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]
      apply pow_le_pow_of_le_one hq0.le hq1.le
      have h1 : J ≤ j := Nat.find_min' hex ⟨n, hj⟩
      have h2 : j ≠ J := fun h => Nat.find_min hJ hn (by rw [hj, h])
      omega
  have hJk : J + 1 ≤ s * k := by
    have h1 : q ^ (s * k) < q ^ J := by
      rw [← hlk]; exact lt_of_lt_of_le hlt (hle n₀)
    have := (pow_lt_pow_iff_right_of_lt_one₀ hq0 hq1).1 h1
    omega

  set M := m₁ + d * s + 1 with hM
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ hlP.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (M + 1))
  have h := hval (M + 1) (by omega) z hz
  unfold Cg at h
  rw [sub_zero, hlk] at h
  set a := ‖z - 1‖ with ha
  have hphi := norm_one_sub_prim hz
  rw [norm_sub_rev, ← ha, hls] at hphi
  have htot : d * s < Nat.totient (l ^ (M + 1)) := by
    rw [Nat.totient_prime_pow_succ hlP]
    have h1 : M < l ^ M := Nat.lt_pow_self hlP.one_lt
    have h2 : 1 ≤ l - 1 := by have := hlP.two_le; omega
    calc d * s < M := by omega
      _ < l ^ M := h1
      _ ≤ l ^ M * (l - 1) := Nat.le_mul_of_pos_right _ h2
  have htpos : 0 < Nat.totient (l ^ (M + 1)) := by omega
  have ha0 : 0 < a := by
    by_contra hc
    push_neg at hc
    have h0 : a = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow htpos.ne'] at hphi
    rw [← hphi] at hl0
    exact lt_irrefl _ hl0
  have ha1 : a < 1 := by
    have : a ^ Nat.totient (l ^ (M + 1)) < 1 := by rw [hphi]; exact hl1
    exact (pow_lt_one_iff_of_nonneg ha0.le htpos.ne').1 this
  have hqa : q < a ^ d := by
    by_contra hc
    push_neg at hc
    have h1 : a ^ (d * s) ≤ a ^ Nat.totient (l ^ (M + 1)) := by
      rw [hphi, pow_mul]; exact pow_le_pow_left₀ (by positivity) hc s
    have := (pow_le_pow_iff_right_of_lt_one₀ ha0 ha1).1 h1
    omega

  set N := l ^ (3 * (M + 1)) with hN
  have hdN : d < N := by
    have : 3 * (M + 1) < l ^ (3 * (M + 1)) := Nat.lt_pow_self hlP.one_lt
    have : d ≤ d * s := Nat.le_mul_of_pos_right d hs
    omega
  have hdmem : d ∈ Finset.range N := Finset.mem_range.2 hdN
  have hsplit : tval F N z = F.coeff d * (z - 1) ^ d +
      ∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n := by
    unfold tval
    exact (Finset.add_sum_erase _ _ hdmem).symm
  have hmain : ‖F.coeff d * (z - 1) ^ d‖ = q ^ J * a ^ d := by
    rw [norm_mul, norm_pow, hd]
  have hB : max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) < q ^ J * a ^ d := by
    have hqJ : 0 < q ^ J := pow_pos hq0 J
    apply max_lt
    · rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa hqJ
    · rw [pow_succ, ← mul_assoc]
      exact mul_lt_of_lt_one_right (mul_pos hqJ (pow_pos ha0 d)) ha1
  have hrest : ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ ≤
      max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
    have hnd : n ≠ d := (Finset.mem_erase.1 hn).1
    rw [norm_mul, norm_pow, ← ha]
    rcases lt_or_gt_of_ne hnd with h' | h'
    · refine le_max_of_le_left ?_
      calc ‖F.coeff n‖ * a ^ n ≤ q ^ (J + 1) * 1 :=
            mul_le_mul (hbefore n h') (pow_le_one₀ ha0.le ha1.le) (by positivity) (by positivity)
        _ = q ^ (J + 1) := mul_one _
    · refine le_max_of_le_right ?_
      exact mul_le_mul (hle n) (pow_le_pow_of_le_one ha0.le ha1.le h') (by positivity) (by positivity)
  have hval' : ‖tval F N z‖ = q ^ J * a ^ d := by
    rw [hsplit, ← hmain]
    have hne : ‖F.coeff d * (z - 1) ^ d‖ ≠ ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ := by
      rw [hmain]; exact (lt_of_le_of_lt hrest hB).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left]
    rw [hmain]; exact hrest.trans hB.le
  rw [hval'] at h
  have h1 : q ^ (s * k) ≤ q ^ (J + 1) := pow_le_pow_of_le_one hq0.le hq1.le hJk
  have h2 : q ^ (J + 1) < q ^ J * a ^ d := by
    rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa (pow_pos hq0 J)
  linarith

end GlobalTheory.KZ.CoefVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.PerFix

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l) : ‖σ y‖ = ‖y‖ :=
  (spectralNorm_eq_of_equiv σ y).symm

def inertiaC (c : Coef l) : Subgroup (Qbar l ≃ₐ[ℚ_[l]] Qbar l) where
  carrier := {σ | (∀ b ∈ c.O, σ b = b) ∧ ∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := ⟨fun b _ => rfl, fun y _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ (τ b) = b
      rw [hτ1 b hb, hσ1 b hb]
    · show ‖σ (τ y) - y‖ < 1
      have e : σ (τ y) - y = (σ (τ y) - τ y) + (τ y - y) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hσ2 _ ((norm_aut τ y).le.trans hy)) (hτ2 y hy))
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ.symm b = b
      exact σ.symm_apply_eq.2 (hσ1 b hb).symm
    · show ‖σ.symm y - y‖ < 1
      have e : σ.symm y - y = σ.symm (y - σ y) := by simp
      rw [e, norm_aut, norm_sub_rev]
      exact hσ2 y hy

theorem exists_fixed_near : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  intro l _ c
  obtain ⟨C, -, hC⟩ := GlobalTheory.AxLemma.ax_lemma l
  have hl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    rw [show ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : Qbar l) from (map_natCast _ _).symm,
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c₁, fun k x hx hfix => ?_⟩
  by_cases hk : k ≤ c₁
  · refine ⟨0, by simp, fun σ _ _ => map_zero σ, ?_⟩
    have h0 : k - c₁ = 0 := by omega
    simpa [Cg, h0] using hx
  · obtain ⟨y, hyH, hxy⟩ := hC (inertiaC c) x ‖((l : ℕ) : Qbar l) ^ k‖ (fun g hg => hfix g hg.1 hg.2)
    have hlpos : (0 : ℝ) < l := by linarith
    have key : C * ‖((l : ℕ) : Qbar l) ^ k‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ := by
      rw [norm_pow, norm_pow, hl]
      have e : (l : ℝ)⁻¹ ^ k = (l : ℝ)⁻¹ ^ (k - c₁) * (l : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm, mul_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hxy' := hxy.trans key
    have hle1 : ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ ≤ 1 := by
      rw [norm_pow, hl]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)
    refine ⟨y, ?_, fun σ h1 h2 => hyH σ ⟨h1, h2⟩, hxy'⟩
    have e : y = x + (y - x) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ((norm_sub_rev y x).le.trans (hxy'.trans hle1)))

end GlobalTheory.PerFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  first | exact @GlobalTheory.CocWildTame.eq_zero_on_Ine | exact GlobalTheory.CocWildTame.eq_zero_on_Ine | (intros; apply GlobalTheory.CocWildTame.eq_zero_on_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoCocycleModPowCoboundaryOfFrobeniusSplitStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_of_cocycle_cong_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n))) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), 0 < m → ((φ ^ m : ↥D) : G ℚ Ω) ∈ K → IsOpen (d.ker : Set ↥D) → (∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K) → (∀ k ∈ K, Cg n (eps l k) 1) → (∀ s t, ξ s t ∈ c.O) → (∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) → (∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) → Cob2 c n D ξ := by
  first | exact @GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | exact GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | (intros; apply GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split <;> assumption)
end

