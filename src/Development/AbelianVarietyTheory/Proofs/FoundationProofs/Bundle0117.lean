module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.NTr

theorem zt_prim {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p n : ℕ) (hp : 0 < p) :
    IsPrimitiveRoot (zt ε p n) (p ^ n) := by
  have h := GlobalTheory.Glue.KTExp.map_eOm ε (1 / (p : ℚ) ^ n)
  have hn : p ^ n ≠ 0 := pow_ne_zero _ hp.ne'
  have hc := Complex.isPrimitiveRoot_exp (p ^ n) hn
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (p : ℚ) ^ n : ℚ)) : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / ((p ^ n : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [e] at h
  unfold zt
  rw [← h] at hc
  exact (IsPrimitiveRoot.map_iff_of_injective ε.injective).mp hc

theorem zt_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p L m : ℕ) (hp : 0 < p) (hm : m ≤ L) :
    zt ε p L ^ (p ^ (L - m)) = zt ε p m := by
  apply ε.injective
  unfold zt
  rw [map_pow, GlobalTheory.Glue.KTExp.map_eOm, GlobalTheory.Glue.KTExp.map_eOm, ← Complex.exp_nat_mul]
  congr 1
  have hpL : (p : ℂ) ^ L = (p : ℂ) ^ (L - m) * (p : ℂ) ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [hpL]
  field_simp

theorem exists_algEquiv_primitiveRoot_pow_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃+* Ω, σ ζ = ζ ^ k := by
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral hn).tower_top
  have hk' : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hk
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζ hn).symm
  have hroot : ζ ^ k ∈ (minpoly ℚ ζ).aroots Ω := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff).2 hk'
  let φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ ^ k, hroot⟩
  let ψ : Ω →ₐ[ℚ] Ω := φ.liftNormal Ω
  refine ⟨(AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ)).toRingEquiv, ?_⟩
  have h1 := φ.liftNormal_commutes Ω (IntermediateField.AdjoinSimple.gen ℚ ζ)
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen] at h1
  change ψ ζ = ζ ^ k
  simpa [ψ] using h1

theorem exists_aut {Ω : Type} [Field Ω] [iA : Algebra ℚ Ω] [iC : IsAlgClosure ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ k := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have e : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have i1 : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI i2 : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by convert i1 using 2; exact e.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_primitiveRoot_pow_of_isAlgClosed (Ω := Ω) ζ n hn hζ k hk
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), hσ⟩
  rw [eq_ratCast]
  exact map_ratCast σ x

open Classical in
theorem sum_reindex (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L) {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), g (a : ZMod (p ^ L)).val
      = ∑ k ∈ Finset.range (p ^ (L - m)), g (1 + p ^ m * k) := by
  have hp : p.Prime := hpf.out
  have hp1 : 1 < p := hp.one_lt
  have hpm : 1 < p ^ m := Nat.one_lt_pow (by omega) hp1
  have hN : p ^ m * p ^ (L - m) = p ^ L := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have cop : ∀ k : ℕ, Nat.Coprime (1 + p ^ m * k) (p ^ L) := by
    intro k
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ p ^ m * k := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k
    exact hp.not_dvd_one ((Nat.dvd_add_left h2).mp h)
  have hlt : ∀ k < p ^ (L - m), 1 + p ^ m * k < p ^ L := by
    intro k hk
    have : p ^ m * (k + 1) ≤ p ^ m * p ^ (L - m) := Nat.mul_le_mul_left _ hk
    rw [hN] at this
    nlinarith
  have hval : ∀ k < p ^ (L - m), ((ZMod.unitOfCoprime (1 + p ^ m * k) (cop k) : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val = 1 + p ^ m * k := by
    intro k hk
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt k hk)]
  symm
  refine Finset.sum_bij (fun k _ => ZMod.unitOfCoprime (1 + p ^ m * k) (cop k)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval k hk]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  · intro k hk k' hk' h
    rw [Finset.mem_range] at hk hk'
    have := congrArg (fun u : (ZMod (p ^ L))ˣ => (u : ZMod (p ^ L)).val) h
    rw [hval k hk, hval k' hk'] at this
    have h3 : p ^ m * k = p ^ m * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hv : (b : ZMod (p ^ L)).val % p ^ m = 1 := by
      have := hb; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hpm]
    have hvl : (b : ZMod (p ^ L)).val < p ^ L := ZMod.val_lt _
    have hdm := Nat.div_add_mod ((b : ZMod (p ^ L)).val) (p ^ m)
    rw [hv] at hdm
    set k := (b : ZMod (p ^ L)).val / p ^ m
    have hk : k < p ^ (L - m) := by
      by_contra hc
      push_neg at hc
      have : p ^ m * p ^ (L - m) ≤ p ^ m * k := Nat.mul_le_mul_left _ hc
      rw [hN] at this
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    have : 1 + p ^ m * k = (b : ZMod (p ^ L)).val := by omega
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    rw [hval k (Finset.mem_range.mp hk)]

open Classical in
theorem trace_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases hd : p ^ (L - m) ∣ i
  · obtain ⟨j, hj⟩ := hd
    refine ⟨(ζ ^ p ^ (L - m)) ^ j, Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i = 1 := by rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    have h2 : ζ ^ i = (ζ ^ p ^ (L - m)) ^ j := by rw [hj, pow_mul]
    rw [h1, h2]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in
theorem trace_closure {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact trace_pow p L m hm1 hm ζ hζ τ hτ i
  | zero => exact ⟨0, Subring.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z1, h1, e1⟩ := hx
    obtain ⟨z2, h2, e2⟩ := hy
    exact ⟨z1 + z2, Subring.add_mem _ h1 h2, by simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2]; ring⟩
  | neg x _ hx =>
    obtain ⟨z1, h1, e1⟩ := hx
    exact ⟨-z1, Subring.neg_mem _ h1, by simp only [map_neg, Finset.sum_neg_distrib, e1]; ring⟩


open Classical in
theorem normTrace_exists_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  intro Ω _ _ _ ε p hpf L m hm1 hm F hF
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := zt_prim ε p L hp.pos
  have hpow := zt_pow ε p L m hp.pos hm
  have hcop : ∀ a : (ZMod (p ^ L))ˣ, ((a : ZMod (p ^ L)).val).Coprime (p ^ L) := fun a => ZMod.val_coe_unit_coprime a
  choose τ hτ using fun a : (ZMod (p ^ L))ˣ => exists_aut (zt ε p L) (p ^ L) (pow_pos hp.pos _) hζ _ (hcop a)
  obtain ⟨D, hD, hDF⟩ := hF
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨z, hz, hT⟩ := trace_closure p L m hm1 hm (zt ε p L) hζ τ hτ _ hDF
  rw [hpow] at hz
  simp only [map_mul, map_natCast, ← Finset.mul_sum] at hT
  have hsum : ∀ σ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, σ a (zt ε p L) = zt ε p L ^ (a : ZMod (p ^ L)).val) →
      ∀ a, σ a F = τ a F := by
    intro σ hσ a
    have hagree : Set.EqOn ((σ a : Ω ≃+* Ω) : Ω →+* Ω) ((τ a : Ω ≃+* Ω) : Ω →+* Ω) (Subring.closure {zt ε p L}) := by
      apply RingHom.eqOn_set_closure
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show σ a (zt ε p L) = τ a (zt ε p L)
      rw [hσ, hτ]
    have h2 : σ a ((D : Ω) * F) = τ a ((D : Ω) * F) := hagree hDF
    rw [map_mul, map_mul, map_natCast, map_natCast] at h2
    exact mul_left_cancel₀ hD0 h2
  have hE : (p : Ω) ^ (L - m) * (z / D) = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a F := by
    rw [← mul_div_assoc, ← hT, mul_div_cancel_left₀ _ hD0]
  refine ⟨z / D, ⟨τ, hτ, hE⟩, ⟨D, hD, ?_⟩, ?_⟩
  · have : (D : Ω) * (z / D) = z := by field_simp
    rw [this]; exact hz
  · rintro F'' ⟨σ, hσ, hF''⟩
    rw [Finset.sum_congr rfl (fun a _ => hsum σ hσ a), ← hE] at hF''
    exact mul_left_cancel₀ hpN hF''

end GlobalTheory.NTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringPullbackIntegralElementsStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_pullback_integral_elements :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧
        ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have existsValuation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hp⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hp.maximalIdeal_eq]
      exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
    have := hC.alg
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr
      (O0 p) Ωl hC.inj
    refine ⟨v, hv, ?_⟩
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp⟩ := existsValuation
  let w := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    change v (j (p : Ω)) < 1
    rw [map_natCast]
    exact hp
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConverges
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_inv_converges : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  intro Ω _ ε C φ h hD hne hS
  obtain ⟨N, n₀, a, hN, ha0, hcoef, hzero⟩ := _root_.GlobalTheory.fnShape Ω h hD hne
  obtain ⟨Φ, hΦ1, hΦ0⟩ := _root_.GlobalTheory.powerSeries_to_hahnSeries_rat Ω N hN
  set p : PowerSeries Ω := PowerSeries.mk a with hpdef
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by simpa [p] using ha0
  set q : PowerSeries Ω := p⁻¹ with hqdef
  have hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N := by
    intro r m k
    rw [sub_eq_iff_eq_add]
    push_cast
    constructor <;> intro hr <;> rw [hr] <;> ring
  have hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p := by
    ext r
    rw [HahnSeries.coeff_single_mul, one_mul]
    by_cases hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]
      simp [p]
    · push_neg at hr
      rw [hzero r hr, hΦ0]
      intro k hk
      exact hr k ((hdiv r n₀ k).1 hk)
  set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef
  have hg : h⁻¹ = g := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef,
      PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]
    have : (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0 := by push_cast; ring
    rw [this, HahnSeries.single_zero_one]
  have hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q := by
    intro k
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]
  have hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0 := by
    intro r hr
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul]
    apply hΦ0
    intro k hk
    exact hr k ((hdiv r (-n₀) k).1 hk)
  refine ⟨?_, ?_⟩
  · rw [hg]
    refine ⟨N, hN, fun r hr => ?_⟩
    by_contra H
    push_neg at H
    exact hr (hgz r fun k hk => H _ hk)

  set A : ℕ → ℂ := fun k => ε (a k) with hAdef
  have hA0 : A 0 ≠ 0 := (map_ne_zero ε).2 ha0
  have hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    have hNc : ((N : ℂ)) = ((N : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc, Complex.div_ofReal_re]
    simp
    ring
  have hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := by
    intro z hz
    exact (GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)
  set t0 : ℝ := max C 0 + 1 with ht0
  set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0
  have hz0im : C < z0.im := by
    simp [z0, t0]
    have := le_max_left C 0
    linarith
  set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hsum0 := hred z0 hz0im
  have hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n := fun x hx =>
    summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx
  obtain ⟨ρ', hρ', hmain⟩ := _root_.GlobalTheory.PowerSeriesInv.hasSum_inv A ‖x0‖ hx0pos hA0 hconv
  have hmk : PowerSeries.mk A = PowerSeries.map ε p := by
    ext k
    simp [p, A]
  have hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · rw [hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]
    · simpa using hA0
  refine ⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hx : ‖x‖ < ρ' := by
    rw [hxdef, hnorm, ← Real.exp_log hρ']
    apply Real.exp_lt_exp.2
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hpi] at hzL
    have h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N := by
      rw [lt_div_iff₀ hNr]; linarith
    have h2 := neg_abs_le (Real.log ρ')
    have h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N) := rfl
    linarith
  obtain ⟨hS0, hinv⟩ := hmain x hx
  have htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)) :=
    (hred z hzC).tsum_eq
  rw [hg]
  apply (GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2
  convert (preTransparency := .reducible) hinv using 1
  · funext k
    rw [← hmapinv, PowerSeries.coeff_map]
  · rw [htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]
    congr 2
    push_cast
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQ
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ ε N f a hN hf
  obtain ⟨Φ, hΦ1, hΦ0⟩ := _root_.GlobalTheory.powerSeries_to_hahnSeries_rat Ω N hN
  set h := Φ (PowerSeries.mk a) with hh
  have hc : ∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k := fun k => by
    rw [hh, hΦ1]; simp
  have h0 : ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := fun r hr => hΦ0 _ r hr
  refine ⟨h, ⟨⟨N, hN, fun r hr => ?_⟩, 0, fun z hz => ?_⟩, hc, h0⟩
  · by_contra hne
    push_neg at hne
    exact hr (h0 r fun k hk => hne k (by rw [hk]; push_cast; rfl))
  · have hc' : ∀ k : ℕ, h.coeff (((0 + k : ℤ) : ℚ) / N) = a k := fun k => by
      simpa using hc k
    have h0' : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((0 + k : ℤ) : ℚ) / N) → h.coeff r = 0 := fun r hr =>
      h0 r fun k hk => hr k (by simpa using hk)
    rw [fn_hasSum_reindex_nat Ω ε h N 0 a z (up f z) hN hc' h0']
    have hq := (hasQ_iff N f _).mp hf ⟨z, hz⟩
    simpa [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationExtensionUniqueBertiniNoether
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.T.exists_monic_irreducible_integral_primitive_element t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation Φ hmon hirr
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have conv : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) :=
    fun W h => ⟨h.1, fun P hP ⟨i, h0, hv, hinv⟩ => h.2 P hP ⟨i, hv, h0, hinv⟩⟩
  have key : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (_root_.GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ (conv W₁ h₁) (conv W₂ h₂) (key W₁ (conv W₁ h₁)))
    (_root_.GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ (conv W₂ h₂) (conv W₁ h₁) (key W₂ (conv W₂ h₂)))

end GlobalTheory.BertiniNoether
end

