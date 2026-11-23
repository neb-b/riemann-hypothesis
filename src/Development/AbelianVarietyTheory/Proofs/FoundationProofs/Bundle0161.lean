module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevel
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kc_val_one_of_inv {V : ValuationSubring Ω} {x : Ω} (hx : x ∈ V) (hi : x⁻¹ ∈ V) (h0 : x ≠ 0) :
    V.valuation x = 1 := by
  have h1 := (V.valuation_le_one_iff x).2 hx
  have h2 := (V.valuation_le_one_iff x⁻¹).2 hi
  rw [map_inv₀] at h2
  have hne : V.valuation x ≠ 0 := by simpa using h0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

theorem kc_inv_of_val_one {V : ValuationSubring Ω} {x : Ω} (h : V.valuation x = 1) :
    x ∈ V ∧ x⁻¹ ∈ V ∧ x ≠ 0 := by
  have h0 : x ≠ 0 := by rintro rfl; simp at h
  refine ⟨(V.valuation_le_one_iff x).1 h.le, (V.valuation_le_one_iff x⁻¹).1 ?_, h0⟩
  rw [map_inv₀, h, inv_one]

theorem kc_prim_gal (X : Tower Ω ε) (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x ∈ V, s x ∈ V)
    {a : X.K} (ha : Prim X V a) : Prim X V (X.gal s a) := by
  obtain ⟨hI, r, hr⟩ := ha
  refine ⟨fun r' => by rw [X.gal_exp]; exact hs _ (hI r'), r, ?_⟩
  rw [X.gal_exp]
  obtain ⟨h1, h2, h3⟩ := kc_inv_of_val_one hr
  exact kc_val_one_of_inv (hs _ h1) (by rw [← map_inv₀]; exact hs _ h2) (by simpa using h3)

theorem kc_ne_zero_of_prim {X : Tower Ω ε} {V : ValuationSubring Ω} {a : X.K} (ha : Prim X V a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨_, r, hr⟩ := ha
  simp at hr

theorem kc_Nq_mul (X : Tower Ω ε) (M q : ℕ) (f g : X.K) : Nq X M q (f * g) = Nq X M q f * Nq X M q g := by
  simp only [Nq, map_mul, Finset.prod_mul_distrib]

theorem kc_Nq_const (X : Tower Ω ε) (M q : ℕ) (c : Ω) (a : X.K) :
    Nq X M q (algebraMap Ω X.K c * a) = algebraMap Ω X.K c ^ q * Nq X M q a := by
  simp only [Nq, map_mul, AlgEquiv.commutes, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem kc_Nq_ne_zero (X : Tower Ω ε) (M q : ℕ) {f : X.K} (hf : f ≠ 0) : Nq X M q f ≠ 0 := by
  simp only [Nq]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hf

theorem kc_gal_const (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes]
  have e : ∀ x : Ω, (algebraMap Ω (HahnSeries ℚ Ω) x).coeff r = if r = 0 then x else 0 := by
    intro x
    rw [HahnSeries.algebraMap_apply']
    have : algebraMap Ω (PowerSeries Ω) x = PowerSeries.C x := rfl
    rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
    simp
  rw [e, e]
  split_ifs <;> simp

theorem kc_div_sub_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hy : W.valuation y = 1)
    (h : W.valuation (x - y) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
  exact h

theorem kc_quot_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy1 : W.valuation y = 1 := by
    have := Valuation.map_one_add_of_lt W.valuation hy
    simpa using this
  apply kc_div_sub_one W hy1
  have e : x - y = (x - 1) - (y - 1) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)

theorem kron_cong_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_primitive_quotient_level_prime_to ε X hj l M₀ hl hM₀
  refine ⟨S, fun q hq hqS V s hF W hD k f hf hlev => ?_⟩
  obtain ⟨M', a, b, c, hM', hcop, hdvd, hla, hlb, hpa, hpb, hc, hfb⟩ := hS q hq hqS V hF.1 k f hf hlev
  have ha0 := kc_ne_zero_of_prim hpa
  have hb0 := kc_ne_zero_of_prim hpb
  have hsV : ∀ x ∈ V, s x ∈ V := fun x hx => (hF.2 x hx).1
  have hsV' : ∀ x ∈ V, s.symm x ∈ V := fun x hx => (hF.2 x hx).2.1
  have hC : algebraMap Ω X.K c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (g : X.K), g ≠ 0 → X.gal t g ≠ 0 := fun t g hg => by simpa using hg
  have hE : ∀ t : Ω ≃ₐ[ℚ] Ω, X.gal t f = algebraMap Ω X.K (t c) * X.gal t a / X.gal t b := fun t => by
    rw [eq_div_iff (hgal t b hb0), ← map_mul, hfb, map_mul, kc_gal_const]
  have hC' : ∀ t : Ω ≃ₐ[ℚ] Ω, algebraMap Ω X.K (t c) ≠ 0 := fun t => (_root_.map_ne_zero _).2 (by simpa using hc)
  constructor
  · refine ⟨s c / c ^ q, ?_⟩
    have hN : Nq X (M₀ * l ^ k) q f = Nq X M' q f := _root_.GlobalTheory.KZ.ES.Nq_eq_of_dvd ε X _ _ q f hq.pos hdvd hcop hlev
    have A1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpa))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF a hla hpa.1))
    have B1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpb))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF b hlb hpb.1))
    have hNb := kc_Nq_ne_zero X M' q hb0
    have E1 : Nq X M' q f = algebraMap Ω X.K c ^ q * Nq X M' q a / Nq X M' q b := by
      rw [eq_div_iff hNb, ← kc_Nq_mul, hfb, kc_Nq_const]
    have key : algebraMap Ω X.K (s c / c ^ q) * Nq X (M₀ * l ^ k) q f / X.gal s f
        = (Nq X M' q a / X.gal s a) / (Nq X M' q b / X.gal s b) := by
      have h1 := hgal s a ha0
      have h2 := hgal s b hb0
      have h3 := hC' s
      rw [hN, E1, hE s, map_div₀, map_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1
  · refine ⟨(s.symm c) ^ q / c, ?_⟩
    have A1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpa), one_pow])
      (hD.2.1 _ (_root_.GlobalTheory.KZ.ES.kron_frob_diag ε X q hq V s hF a hpa.1))
    have B1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpb), one_pow])
      (hD.2.1 _ (_root_.GlobalTheory.KZ.ES.kron_frob_diag ε X q hq V s hF b hpb.1))
    generalize toGQ !![(q : ℤ), 0; 0, 1] = T at A1 B1 ⊢
    have hTb : X.sl T b ≠ 0 := by simpa using hb0
    have E1 : X.sl T f = algebraMap Ω X.K c * X.sl T a / X.sl T b := by
      rw [eq_div_iff hTb, ← map_mul, hfb, map_mul, AlgEquiv.commutes]
    have key : algebraMap Ω X.K ((s.symm c) ^ q / c) * X.sl T f / (X.gal s.symm f) ^ q
        = (X.sl T a / (X.gal s.symm a) ^ q) / (X.sl T b / (X.gal s.symm b) ^ q) := by
      have h1 := hgal s.symm a ha0
      have h2 := hgal s.symm b hb0
      have h3 := hC' s.symm
      rw [E1, hE s.symm, map_div₀, map_pow, div_pow, mul_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ

theorem B_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hcop hw
  have L1 : ∀ x : X.Khat l, (l : ℤ_[l]) • x = 0 → x = 0 := fun x hx => _root_.GlobalTheory.KZ.BettiB.khat_no_l_torsion X l x hx
  have Ladd : ∀ b b' c c', BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := fun b b' c c' h h' => _root_.GlobalTheory.KZ.BettiB.Add.btZ_add X N l b b' c c' h h'
  have Lsmul : ∀ (r : ℤ_[l]) b c, BtZ X N l b c → BtZ X N l (r • b) (r • c) := fun r b c h => GlobalTheory.T.bettiKummerRelationPadic_smul X N l r b c h
  have Lzero : BtZ X N l 0 0 := btZ_zero X N l
  have L3 : ∀ b, BtZ X N l b 0 → b = 0 := fun b h => _root_.GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero ε X hε hj N l (by omega) b h
  have L4 : Module.Finite ℤ_[l] (Z1 N l w) := _root_.GlobalTheory.KZ.BettiB.module_finite_z1_padicInt N l w (by omega)
  have L5 : ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := GlobalTheory.T.exists_betti_cocycle_kummer_relation ε X hε hj N l w hl2 hN hcop hw

  let S : Submodule ℤ_[l] (X.Fn l × Z1 N l w) :=
    { carrier := {p | BtZ X N l p.1 (p.2 : Gam N l → MvPolynomial (Fin 2) ℤ_[l])}
      add_mem' := fun {p q} hp hq => by simpa using Ladd _ _ _ _ hp hq
      zero_mem' := by simpa using Lzero
      smul_mem' := fun r p hp => by simpa using Lsmul r _ _ hp }
  have hinj : Function.Injective ((LinearMap.snd ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
    intro p q hpq
    have hd : (p : X.Fn l × Z1 N l w) - q ∈ S := S.sub_mem p.2 q.2
    have h2 : ((p : X.Fn l × Z1 N l w) - q).2 = 0 := by simpa [sub_eq_zero] using hpq
    have h1 : ((p : X.Fn l × Z1 N l w) - q).1 = 0 := by
      apply L3
      have := hd
      simp only [S, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rwa [h2] at this
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  haveI : IsNoetherian ℤ_[l] (Z1 N l w) := inferInstance
  haveI hSf : Module.Finite ℤ_[l] S := Module.Finite.of_injective _ hinj
  have hle : X.B N l w ≤ S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) := by
    refine Submodule.span_le.mpr ?_
    intro b hb
    obtain ⟨c, hc, hbc⟩ := L5 b hb
    exact ⟨(b, ⟨c, hc⟩), hbc, rfl⟩
  have hfg : (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))).FG := by
    have e : S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) =
        LinearMap.range ((LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [e]
    exact Module.Finite.iff_fg.mp inferInstance
  have hB : (X.B N l w).FG := by
    haveI : IsNoetherian ℤ_[l] (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))) := isNoetherian_of_fg_of_noetherian _ hfg
    have := (isNoetherian_submodule.mp this) (X.B N l w) ?_
    · exact this
    · exact hle
  haveI hBf : Module.Finite ℤ_[l] (X.B N l w) := Module.Finite.iff_fg.mpr hB

  have Lpow : ∀ (k : ℕ) (x : X.Khat l), ((l : ℤ_[l]) ^ k) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply L1
      rw [← mul_smul, ← pow_succ']; exact hx
  haveI : NoZeroSMulDivisors ℤ_[l] (X.B N l w) := by
    refine ⟨fun {r b} h => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrw := PadicInt.unitCoeff_spec hr
    apply Subtype.ext
    funext u
    have h' : (r • (b : X.Fn l)) u = 0 := by
      have := congrArg (fun y : X.B N l w => (y : X.Fn l) u) h
      simpa using this
    have h'' : ((l : ℤ_[l]) ^ r.valuation) • (((PadicInt.unitCoeff hr : ℤ_[l]ˣ) : ℤ_[l]) • (b : X.Fn l) u) = 0 := by
      rw [smul_smul, mul_comm, ← hrw]; simpa using h'
    have := Lpow _ _ h''
    simpa using this
  exact ⟨Module.free_of_finite_type_torsion_free', hBf⟩

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableMulDivisorSum
section
open Complex Filter Topology

namespace GlobalTheory.DivConvSum

theorem norm_divisorSum_le (k n : ℕ) (ψ θ : ℕ → ℂ) (h : ∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) :
    ‖∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ k * θ p.2‖
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  refine (norm_sum_le _ _).trans ?_
  rw [← hc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
  have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hle' : (p.1 : ℝ) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) k
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 := (h p.1).1
  have h2 := (h p.2).2
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) ^ k := by positivity
  calc ‖ψ p.1‖ * (p.1 : ℝ) ^ k * ‖θ p.2‖ ≤ 1 * (p.1 : ℝ) ^ k * 1 := by
        gcongr
    _ ≤ (n : ℝ) ^ k := by simpa using hle'

theorem lSeriesSummable_mul_divisorSum :
    ∀ (e : ℕ) (ψ θ g b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n : ℕ => g n * b n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ θ g b s he hs hψ hg hb
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h1 := hg s hs
  have h2 := GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow s hs
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hbn : ‖b n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
      rw [hb n hn, Nat.add_sub_cancel]
      exact norm_divisorSum_le k n ψ θ hψ
    have e1 : (n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, show (2 * ((k + 1 : ℕ) : ℝ)) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      ring
    have e2 : (n : ℝ) ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n * (n : ℝ) ^ s) := by
      rw [Real.rpow_add hN, Real.rpow_natCast]
      ring
    have e3 : (n : ℝ) ^ (1 + s) = n * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, Real.rpow_one]
    rw [Complex.ofReal_re, norm_mul, e1, e2, e3]
    have hu : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos hN s
    have hP : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    generalize (n : ℝ) ^ s = u at *
    generalize (n : ℝ) ^ k = P at *
    generalize (n.divisors.card : ℝ) = d at *
    have hG : 0 ≤ ‖g n‖ := norm_nonneg _
    generalize ‖g n‖ = G at *
    generalize (n : ℝ) = N at *
    calc G * ‖b n‖ / ((P * N) ^ 2 * u) ≤ G * (d * P) / ((P * N) ^ 2 * u) := by gcongr
      _ = (G / (P * N) * d) / (N * u) := by field_simp
      _ ≤ ((G / (P * N)) ^ 2 + d ^ 2) / (N * u) := by
          gcongr
          nlinarith [sq_nonneg (G / (P * N) - d), sq_nonneg (G / (P * N)), sq_nonneg d]
      _ = G ^ 2 / ((P * N) ^ 2 * (N * u)) + d ^ 2 / (N * u) := by field_simp

end GlobalTheory.DivConvSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrime
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocIneq

theorem term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) = b (p ^ e) * ((1 / (p : ℝ) ^ (1 + s) : ℝ) : ℂ) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne]
  have h1 : ((p ^ e : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) = ((((p : ℝ) ^ (1 + s)) ^ e : ℝ) : ℂ) := by
    rw [show ((p ^ e : ℕ) : ℂ) = (((p ^ e : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0]
  rw [h1, div_eq_mul_inv]
  congr 1
  push_cast
  rw [one_div, inv_pow]

theorem real_term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (e : ℕ) :
    ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) = ‖b (p ^ e)‖ ^ 2 * (1 / (p : ℝ) ^ (1 + s)) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0, div_eq_mul_inv,
    one_div, inv_pow]

theorem local_positivity_eulerFactor : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  intro b ω s C p hs hp hb1 hω hrec hbd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hbd 1
    rw [hb1] at this
    simp at this
    linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b p ^ 2 - 4 * ω p)
  set x : ℂ := (b p + z) / 2 with hx
  set y : ℂ := (b p - z) / 2 with hy
  have hxy : x + y = b p := by rw [hx, hy]; ring
  have hxy' : x * y = ω p := by rw [hx, hy]; linear_combination (1 / 4 : ℂ) * hz
  have hc0 : b (p ^ 0) = 1 := by simpa using hb1
  have hc1 : b (p ^ 1) = x + y := by rw [pow_one, hxy]
  have hcr : ∀ r, b (p ^ (r + 2)) = (x + y) * b (p ^ (r + 1)) - x * y * b (p ^ r) := by
    intro r; rw [hxy, hxy']; exact hrec r
  have hroots := GlobalTheory.roots_norm_le_of_bounded_two_step_recursion x y (fun r => b (p ^ r))
    (Real.sqrt C) (Real.sqrt p) (Real.sqrt_nonneg _) hc0 hc1 hcr (by
      intro r
      have h := hbd (p ^ r)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hC, Real.sq_sqrt hp0.le]
      simpa using h)
  have hP : (p : ℝ) < (p : ℝ) ^ (1 + s) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (1 + s) := by linarith
  have hsq : 1 / (p : ℝ) ^ (2 * (1 + s)) = (1 / (p : ℝ) ^ (1 + s)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_two, div_pow, one_pow]
  simp only [term_prime_pow b s p hp, real_term_prime_pow b s p, hsq]
  rw [div_eq_mul_one_div (‖1 + b p‖ ^ 2)]
  have hT0 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
  have hpT : p * (1 / (p : ℝ) ^ (1 + s)) < 1 := by
    rw [mul_one_div, div_lt_one hP0]; exact hP
  generalize 1 / (p : ℝ) ^ (1 + s) = T at hT0 hpT ⊢
  have hT1 : T < 1 := by nlinarith
  have hb : ∀ w : ℂ, ‖w‖ ≤ Real.sqrt p → ‖w‖ ^ 2 * T < 1 := by
    intro w hw
    have : ‖w‖ ^ 2 ≤ p := by
      rw [← Real.sq_sqrt hp0.le]
      exact pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hxT := hb x hroots.1
  have hyT := hb y hroots.2
  obtain ⟨hL, hR⟩ := _root_.GlobalTheory.LocSer.twoStep_eulerFactors x y (fun r => b (p ^ r)) T hT0.le hT1 hxT hyT hc0 hc1 hcr
  have hI := GlobalTheory.EisM.locineq x y T hT0.le hT1 hxT hyT
  rw [add_assoc, hxy] at hI
  rw [hxy', hω] at hR
  have hR0 : 0 ≤ ∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r := tsum_nonneg fun r => by positivity
  have hLn := congrArg (fun w : ℂ => ‖w‖ ^ 2) hL
  simp only [norm_one, one_pow] at hLn
  rw [norm_mul, mul_pow] at hLn
  have hL0 : 0 ≤ ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 := by positivity
  generalize (∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r) = R at hR hR0 ⊢
  generalize ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 = L at hLn hL0 ⊢
  generalize ‖(1 - x * T) * (1 - y * T)‖ ^ 2 = D at hLn hI
  generalize (1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2 = E at hR hI
  generalize Real.exp (‖1 + b p‖ ^ 2 * T) = A at hI ⊢
  have h1 : 0 < 1 - T := by linarith
  have h2 : 0 < 1 - T ^ 2 := by nlinarith
  rw [one_pow, one_mul] at hR
  have hK : 0 ≤ (1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹ := by positivity
  have hone : ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹) = 1 := by
    calc ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹)
        = ((1 - T) * (1 - T)⁻¹) * (L * D) * ((R * E) * (1 - T ^ 2)⁻¹) := by ring
      _ = 1 := by rw [hLn, hR, mul_inv_cancel₀ h1.ne', mul_inv_cancel₀ h2.ne']; ring
  have h3 := mul_le_mul_of_nonneg_right hI hK
  rwa [mul_assoc, hone, mul_one, one_mul] at h3

end GlobalTheory.LocIneq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOne
section
open UpperHalfPlane Complex
open scoped Real

namespace GlobalTheory.EisM

private theorem norm_cexp_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-(2 * π * n * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : (2 * π * Complex.I * n * τ : ℂ) = ((2 * π * n : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem qs_bdd_above_one : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  intro b hb
  obtain ⟨hs, -⟩ := qs_summable_continuous b hb
  refine ⟨∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖, fun τ hτ => ?_⟩
  have hpt : ∀ n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_cexp_qterm, norm_cexp_qterm]
    gcongr
    simp only [UpperHalfPlane.I_im, mul_one]
    have h0 : (0 : ℝ) ≤ 2 * π * n := by positivity
    nlinarith
  calc ‖qs b τ‖ ≤ ∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ := by
        unfold qs; exact norm_tsum_le_tsum_norm (hs τ)
    _ ≤ _ := Summable.tsum_le_tsum hpt (hs τ) (hs _)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => _root_.GlobalTheory.Sieg.admissible_act_SL2 c x γ h)
    (fun x τ h => _root_.GlobalTheory.Sieg.sg_S c x τ h) (fun x τ _ => _root_.GlobalTheory.Sieg.sg_T_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
end

