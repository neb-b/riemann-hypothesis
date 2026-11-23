module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
section
namespace PI.LocDualGen.Psi

open PI.LocDualGen.W

theorem addCharKernel : PsiKer := by
  rintro l _ t a ⟨n, hn⟩ ht
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ a.den = 1 := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [mul_comm (m : ℂ)] at hm
      have h1 : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ hI hm
      have ha : a = m := by exact_mod_cast h1
      rw [ha]
      exact Rat.den_intCast m
    · intro h1
      refine ⟨a.num, ?_⟩
      have ha : (a : ℂ) = (a.num : ℂ) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        exact_mod_cast h.symm
      rw [ha]
      ring
  have hna : ‖t‖ ≤ 1 ↔ ‖(a : ℚ_[l])‖ ≤ 1 := by
    constructor
    · intro h
      have e : (a : ℚ_[l]) = t + ((a : ℚ_[l]) - t) := by ring
      rw [e]
      refine le_trans (Padic.nonarchimedean _ _) (max_le h ?_)
      rw [norm_sub_rev]
      exact ht
    · intro h
      have e : t = (t - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
      rw [e]
      exact le_trans (Padic.nonarchimedean _ _) (max_le ht h)
  have hrat : ‖(a : ℚ_[l])‖ ≤ 1 ↔ a.den = 1 := by
    constructor
    · intro h
      by_contra hd
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hd hn
      have hlp : l.Prime := Fact.out
      have hnum : ¬ (l : ℤ) ∣ a.num := by
        intro hdvd
        have h1 : l ∣ a.num.natAbs := Int.natCast_dvd.mp hdvd
        have h2 : l ∣ a.den := by
          rw [hn]
          exact dvd_pow_self l hn0
        have h3 := Nat.dvd_gcd h1 h2
        rw [a.reduced.gcd_eq_one] at h3
        exact hlp.one_lt.ne' (Nat.dvd_one.mp h3)
      have hnum1 : ‖(a.num : ℚ_[l])‖ = 1 :=
        le_antisymm (Padic.norm_int_le_one _)
          (not_lt.mp fun h' => hnum (Padic.norm_intCast_lt_one_iff.mp h'))
      have hden : ‖(a.den : ℚ_[l])‖ = ((l : ℝ)⁻¹) ^ n := by
        rw [hn, Nat.cast_pow, norm_pow, Padic.norm_p]
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) / (a.den : ℚ_[l]) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      rw [ha, norm_div, hnum1, hden] at h
      have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
      have hgt : (1 : ℝ) < 1 / ((l : ℝ)⁻¹) ^ n := by
        rw [inv_pow, one_div, inv_inv]
        exact one_lt_pow₀ hl1 hn0
      linarith
    · intro h1
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        norm_cast
        exact h.symm
      rw [ha]
      exact Padic.norm_int_le_one _
  rw [hexp, hna, hrat]

end PI.LocDualGen.Psi
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDual
section
noncomputable section

open ValuativeRel

namespace PI.LocDualGen.FpD

open PI.LocDualGen.W

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]

def P (x : K) : Prop := ∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * (b : K))‖ ≤ 1

theorem tr_alg_mul (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

private theorem t2_lemma : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
  intro x hx
  have hv : ValuativeRel.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩

private theorem isOpen_lemma_2 : IsOpen (𝒪[K] : Set K) := by
  have h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K) := by
    refine (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩
    have hz' : ValuativeRel.valuation K z < 1 := by simpa using hz
    exact (Valuation.mem_integer_iff _ _).2 hz'.le
  exact AddSubgroup.isOpen_of_mem_nhds _ h0

private theorem trace_cont_lemma_3 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    Continuous (Algebra.trace ℚ_[l] K) := by
  haveI := t2_lemma (K := K)
  haveI : ContinuousSMul ℚ_[l] K := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  exact LinearMap.continuous_of_finiteDimensional _

private theorem int_lemma_4 (hcont : Continuous (algebraMap ℚ_[l] K)) (z : ℚ_[l]) (hz : ‖z‖ ≤ 1) :
    algebraMap ℚ_[l] K z ∈ 𝒪[K] := by
  have hcl : IsClosed (𝒪[K] : Set K) :=
    AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))
  let w : ℤ_[l] := ⟨z, hz⟩
  have key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K] := by
    refine PadicInt.denseRange_natCast.induction_on w ?_ ?_
    · exact hcl.preimage (hcont.comp continuous_subtype_val)
    · intro n
      rw [PadicInt.coe_natCast, map_natCast]
      exact natCast_mem _ n

  exact key

private theorem small_lemma_5 (hcont : Continuous (algebraMap ℚ_[l] K)) (y : K) :
    ∃ N : ℕ, ∀ k ≥ N, algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y ∈ 𝒪[K] := by
  have h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y)
      Filter.atTop (nhds 0) := by
    have := ((hcont.tendsto 0).comp h1).mul_const y
    rw [map_zero, zero_mul] at this
    exact this
  have h3 : (𝒪[K] : Set K) ∈ nhds (0 : K) := (isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)
  exact Filter.eventually_atTop.1 (h2.eventually_mem h3)

private theorem P_add_mem {x y : K} (hx : P l x) (hy : P l y) : P l (x + y) := fun b => by
  rw [add_mul, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))

private theorem mul_mem_dual₂ {x : K} (hx : P l x) (c : 𝒪[K]) : P l (x * c) := fun b => by
  rw [mul_assoc]
  exact hx (c * b)

private theorem bound_lemma_8 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  classical
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hnd := traceForm_nondegenerate ℚ_[l] K
  let B := Module.finBasis ℚ_[l] K
  choose N hN using fun i => small_lemma_5 l hcont (B i)
  let b := B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i)
    (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)
  have hb : ∀ i, b i ∈ 𝒪[K] := fun i => by
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]
    exact hN i (N i) le_rfl
  let D := (Algebra.traceForm ℚ_[l] K).dualBasis hnd b
  choose N' hN' using fun i => small_lemma_5 l hcont (D i)
  refine ⟨Finset.univ.sup N', fun x hx => ?_⟩
  have hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K] := fun i => by
    apply int_lemma_4 l hcont
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact hx ⟨b i, hb i⟩
  rw [← D.sum_repr x, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, mul_left_comm]
  exact mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))

theorem exists_ne_zero (hcont : Continuous (algebraMap ℚ_[l] K)) : ∃ x : K, x ≠ 0 ∧ P l x := by
  have hT := trace_cont_lemma_3 l hcont
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    have h : CompactSpace 𝒪[K] := inferInstance
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hT.continuousOn
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1
  refine ⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · rw [tr_alg_mul, norm_mul, norm_pow]
    have h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1 := (hC b b.2).trans (le_max_left _ _)
    calc ‖(l : ℚ_[l])‖ ^ n * ‖Algebra.trace ℚ_[l] K (b : K)‖
        ≤ ‖(l : ℚ_[l])‖ ^ n * max C 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (max C 1)⁻¹ * max C 1 := mul_le_mul_of_nonneg_right hn.le hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end

private theorem main_lemma_9 {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K] := by
  classical
  obtain ⟨m, hm⟩ := bound_lemma_8 l hcont
  obtain ⟨x0, hx0, hPx0⟩ := exists_ne_zero l hcont
  set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let I : Ideal 𝒪[K] :=
    { carrier := {c | P l ((c : K) * t⁻¹)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [add_mul]
        exact P_add_mem l ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro b
        simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        have h := mul_mem_dual₂ l ha c
        have e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K) := by
          push_cast
          ring
        rw [e]
        exact h }
  obtain ⟨g0, hg0⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹) := fun c => Iff.rfl
  have hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c := fun c => by
    rw [hg0, Submodule.mem_span_singleton]
    rfl
  have hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I := by
    rw [hmem]
    have e : t * x0 * t⁻¹ = x0 := by field_simp
    simpa only [e] using hPx0
  have hg0I : g0 ∈ I := (hspan g0).2 ⟨1, one_mul _⟩
  have hg0ne : (g0 : K) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hspan _).1 hc0
    have := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul, h, mul_zero] at this
    exact mul_ne_zero ht0 hx0 this.symm
  set g : K := (g0 : K) * t⁻¹ with hg
  have hPg : P l g := (hmem g0).1 hg0I
  have hgne : g ≠ 0 := mul_ne_zero hg0ne (inv_ne_zero ht0)
  refine ⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩
  simp only [inv_inv]
  constructor
  · intro h
    have hPa : P l (a * g) := fun b => by
      have e : a * g * (b : K) = a * (b : K) * g := by ring
      rw [e]
      exact h b
    have hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I := by
      rw [hmem]
      have e : t * (a * g) * t⁻¹ = a * g := by field_simp
      simpa only [e] using hPa
    obtain ⟨r, hr⟩ := (hspan _).1 hc
    have h2 := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul] at h2
    have h3 : (r : K) = a := by
      have e : t * (a * g) = a * (g0 : K) := by
        rw [hg]
        field_simp
      rw [e] at h2
      exact mul_right_cancel₀ hg0ne h2
    rw [← h3]
    exact r.2
  · intro ha b
    have h := mul_mem_dual₂ l hPg ⟨a, ha⟩ b
    have e : a * (b : K) * g = g * a * (b : K) := by ring
    rw [e]
    exact h

theorem existsDifferentGenerator : FpDual := by
  intro K _ _ _ l _ _ hK _ hcont hfin
  haveI := hK
  haveI := hfin
  exact main_lemma_9 l hcont

end PI.LocDualGen.FpD
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.IsClosedO
section
noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

theorem t2 : T2Space K := by
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hv : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ h0
  have hz' : valuation K z < valuation K x := hz
  have h0' : x + z = 0 := h0
  have : z = -x := by linear_combination h0'
  rw [this, Valuation.map_neg] at hz'
  exact lt_irrefl _ hz'

theorem isClosed_O : IsClosed ((𝒪[K] : Set K)) := by
  haveI : T2Space K := t2 (K := K)
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed

theorem iota_mem (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K] := by
  have hcl : IsClosed {a : ℤ_[l] | algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K]} :=
    (isClosed_O (K := K)).preimage (hcont.comp continuous_subtype_val)
  refine PadicInt.denseRange_intCast.induction_on a hcl ?_
  intro n
  simp only [Set.mem_setOf_eq, PadicInt.coe_intCast, map_intCast]
  exact intCast_mem _ n

def iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) : ℤ_[l] →+* 𝒪[K] :=
  ((algebraMap ℚ_[l] K).comp (PadicInt.Coe.ringHom (p := l))).codRestrict 𝒪[K]
    (fun a => iota_mem K l hcont a)

theorem iotaR_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    ((iotaR K l hcont a : 𝒪[K]) : K) = algebraMap ℚ_[l] K (a : ℚ_[l]) := rfl

theorem charP_res (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (residue 𝒪[K]) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 huni.not_isUnit)

theorem repr_sum {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  exact congrFun (b.repr_sum_self c) i

section Res

variable [CharP 𝓀[K] l]

abbrev algRes : Algebra (ZMod l) 𝓀[K] := ZMod.algebra _ l

attribute [local instance] algRes

theorem res_iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by
  obtain ⟨-, h⟩ := PadicInt.zmodRepr_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = ((a.zmodRepr : ℕ) : ℤ_[l]) + b * (l : ℤ_[l]) := by rw [hb]; ring
  rw [ha]
  simp [map_natCast, CharP.cast_eq_zero]

abbrev fdim : ℕ := Module.finrank (ZMod l) 𝓀[K]

def bb : Module.Basis (Fin (fdim K l)) (ZMod l) 𝓀[K] := Module.finBasis (ZMod l) 𝓀[K]

def blift (i : Fin (fdim K l)) : 𝒪[K] := (residue_surjective (bb K l i)).choose

theorem res_blift (i : Fin (fdim K l)) : residue 𝒪[K] (blift K l i) = bb K l i := by
  exact (residue_surjective (bb K l i)).choose_spec

def Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) : 𝒪[K] :=
  ∑ i, iotaR K l hcont (c i) * blift K l i

theorem Phi_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
  unfold Phi
  push_cast
  simp only [iotaR_coe]

theorem Phi_add (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by
  simp only [Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem res_Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    residue 𝒪[K] (Phi K l hcont c) = ∑ i, PadicInt.toZMod (c i) • bb K l i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Phi, map_sum, map_mul, res_iotaR, res_blift, Algebra.smul_def]

theorem one_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) * y := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set r := (bb K l).repr (residue 𝒪[K] x) with hr
  refine ?_
  have hc : residue 𝒪[K] (Phi K l hcont (fun i => ((r i).val : ℤ_[l]))) = residue 𝒪[K] x := by
    rw [res_Phi]
    have h1 : ∀ i, PadicInt.toZMod (((r i).val : ℕ) : ℤ_[l]) = r i := fun i => by
      rw [map_natCast, ZMod.natCast_zmod_val]
    simp_rw [h1]
    exact (bb K l).sum_repr (residue 𝒪[K] x)
  have hm : x - Phi K l hcont (fun i => ((r i).val : ℤ_[l])) ∈ maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 huni,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨_, y, by rw [mul_comm, hy]; ring⟩

theorem n_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (j : ℕ) (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) ^ j * y := by
  induction j with
  | zero => exact ⟨0, x, by simp [Phi]⟩
  | succ j ih =>
    obtain ⟨c, y, hxy⟩ := ih
    obtain ⟨c', y', hy⟩ := one_step K l hcont huni y
    refine ⟨c + ((l : ℤ_[l]) ^ j) • c', y', ?_⟩
    rw [Phi_add, hxy, hy]
    simp only [map_pow, map_natCast]
    ring

theorem span (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, x = Phi K l hcont c := by
  haveI : T2Space K := t2 (K := K)
  choose c y hxy using fun j => n_step K l hcont huni j x
  let F : (Fin (fdim K l) → ℤ_[l]) → K := fun c => ((Phi K l hcont c : 𝒪[K]) : K)
  have hF : Continuous F := by
    have : F = fun c => ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
      funext c
      exact Phi_coe K l hcont c
    rw [this]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (hcont.comp (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have hcl : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  have h0 : Filter.Tendsto (fun j => (l : K) ^ j * (y j : K)) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun j => (l : ℚ_[l]) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have hp' : Filter.Tendsto (fun j => (l : K) ^ j) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto 0).comp hp
      simpa [Function.comp_def, map_pow, map_natCast] using this
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff] at hp' ⊢
    intro γ _
    filter_upwards [hp' γ trivial] with j hj
    have hj' : valuation K ((l : K) ^ j) < γ := hj
    show valuation K ((l : K) ^ j * (y j : K)) < γ
    rw [map_mul]
    have hy1 : valuation K (y j : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (y j).2
    calc valuation K ((l : K) ^ j) * valuation K (y j : K) ≤ valuation K ((l : K) ^ j) * 1 :=
          by gcongr
      _ = valuation K ((l : K) ^ j) := mul_one _
      _ < _ := hj'
  have heq : (fun j => F (c j)) = fun j => (x : K) - (l : K) ^ j * (y j : K) := by
    funext j
    have := congrArg (fun z : 𝒪[K] => (z : K)) (hxy j)
    push_cast at this
    simp only [F]
    rw [this]
    ring
  have hlim : Filter.Tendsto (fun j => F (c j)) Filter.atTop (nhds (x : K)) := by
    rw [heq]
    simpa using (tendsto_const_nhds (x := (x : K))).sub h0
  obtain ⟨c0, hc0⟩ := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => ⟨c j, rfl⟩)
  exact ⟨c0, Subtype.ext hc0.symm⟩

end Res

end PI.LocDualGen.FpU
end
end

