module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LocalIntegralOfSubstitution
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem local_integral_of_substitution : LocInt := by
  intro F _ _ t z c u hu hz
  by_cases hc : (c : F) = 0
  · refine ⟨1, t.asIdeal.primeCompl.one_mem, 0, ?_⟩
    rw [hc, map_zero, zero_mul] at hz
    have hz0 : z = 0 := (algebraMap F (t.adicCompletion F)).injective (by rw [hz, map_zero])
    simp [hz0]
  · have hxu : algebraMap F (t.adicCompletion F) (z / (c : F)) = u := by
      rw [map_div₀, hz, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hc)]
    have hu' : algebraMap F (t.adicCompletion F) (z / (c : F)) ∈ t.adicCompletionIntegers F :=
      hxu ▸ hu
    have e : ∀ x : F, Valued.v (algebraMap F (t.adicCompletion F) x) = t.valuation F x := by
      intro x
      first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation x
      | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      | rfl
    have hv : t.valuation F (z / (c : F)) ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hu'
      rw [← e]
      exact hu'
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (z / (c : F))
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hvm : t.intValuation m ≠ 0 := HeightOneSpectrum.intValuation_ne_zero t m hm0
    have hnm' : t.intValuation n ≤ t.intValuation m := by
      rw [← hnm, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap] at hv
      exact (div_le_one₀ (zero_lt_iff.2 hvm)).1 hv
    have hI0 : Ideal.span {m} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hm0
    obtain ⟨k, J, hJt, hmJ⟩ := WfDvdMonoid.max_power_factor hI0 t.irreducible
    have hnk : n ∈ t.asIdeal ^ k := by
      have hdm : t.asIdeal ^ k ∣ Ideal.span {m} := ⟨J, hmJ⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hdm
      have hdn := (HeightOneSpectrum.intValuation_le_pow_iff_dvd t n k).1 (hnm'.trans hdm)
      exact Ideal.dvd_span_singleton.1 hdn
    have hJ : ¬ J ≤ t.asIdeal := fun h => hJt (Ideal.dvd_iff_le.2 h)
    obtain ⟨d, hdJ, hdt⟩ := SetLike.not_le_iff_exists.1 hJ
    have hdn : d * n ∈ Ideal.span {m} := by
      rw [hmJ, mul_comm d n]
      exact Ideal.mul_mem_mul hnk hdJ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hdn
    refine ⟨d, hdt, a, ?_⟩
    have hmF : algebraMap (𝓞 F) F m ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have ha' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F m =
        algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F n := by
      rw [← map_mul, ← map_mul, ha]
    have hzm : z * algebraMap (𝓞 F) F m = (c : F) * algebraMap (𝓞 F) F n := by
      have h3 : z = (c : F) * (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F m) := by
        rw [hnm]
        field_simp
      rw [h3, mul_assoc, div_mul_cancel₀ _ hmF]
    show z * algebraMap (𝓞 F) F d = (c : F) * algebraMap (𝓞 F) F a
    apply mul_right_cancel₀ hmF
    linear_combination (algebraMap (𝓞 F) F d) * hzm - (c : F) * ha'

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PLatStep
section
namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lattice_modification : LatStep := latStep_of_parts lsLat lsOne lsLoc

end PI.UnitaryGroupMassFormula.UJClassMass
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.TcoordBound
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

namespace HX

section T

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tensA (t : HeightOneSpectrum (𝓞 F)) : AddSubgroup (E ⊗[F] t.adicCompletion F) :=
  AddSubgroup.closure {w | ∃ x ∈ PI.UnitaryApproxDefs.intOE E, ∃ y ∈ t.adicCompletionIntegers F, w = x ⊗ₜ[F] y}

theorem tensA_mul (t : HeightOneSpectrum (𝓞 F)) {a b : E ⊗[F] t.adicCompletion F}
    (ha : a ∈ tensA (E := E) t) (hb : b ∈ tensA (E := E) t) : a * b ∈ tensA (E := E) t := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha' =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb' =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ha'
      obtain ⟨x', hx', y', hy', rfl⟩ := hb'
      apply AddSubgroup.subset_closure
      exact ⟨x * x', (PI.UnitaryApproxDefs.intOE E).mul_mem hx hx', y * y',
        mul_mem hy hy', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
    | zero => rw [mul_zero]; exact (tensA (E := E) t).zero_mem
    | add b c _ _ hb hc => rw [mul_add]; exact (tensA (E := E) t).add_mem hb hc
    | neg b _ hb => rw [mul_neg]; exact (tensA (E := E) t).neg_mem hb
  | zero => rw [zero_mul]; exact (tensA (E := E) t).zero_mem
  | add a c _ _ ha hc => rw [add_mul]; exact (tensA (E := E) t).add_mem ha hc
  | neg a _ ha => rw [neg_mul]; exact (tensA (E := E) t).neg_mem ha

theorem tensInt_le (t : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] t.adicCompletion F}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring) :
    s ∈ tensA (E := E) t := by
  unfold PI.UnitaryApproxDefs.tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact AddSubgroup.subset_closure ⟨x, hx, 1, (t.adicCompletionIntegers F).one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, y, hy, rfl⟩
  | zero => exact (tensA (E := E) t).zero_mem
  | one => exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, 1,
      (t.adicCompletionIntegers F).one_mem, rfl⟩
  | add a b _ _ ha hb => exact (tensA (E := E) t).add_mem ha hb
  | neg a _ ha => exact (tensA (E := E) t).neg_mem ha
  | mul a b _ _ ha hb => exact tensA_mul t ha hb

theorem intInt (t : HeightOneSpectrum (𝓞 F)) {z : F} (hz : IsIntegral ℤ z) :
    algebraMap F (t.adicCompletion F) z ∈ t.adicCompletionIntegers F := by
  obtain ⟨r, rfl⟩ : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = z := ⟨⟨z, hz⟩, rfl⟩
  first
  | exact HeightOneSpectrum.coe_mem_adicCompletionIntegers t r
  | (rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
     exact HeightOneSpectrum.intValuation_le_one t r)
  | (rw [HeightOneSpectrum.mem_adicCompletionIntegers]
     simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
       HeightOneSpectrum.intValuation_le_one])

theorem tcoord_bound {ι : Type} (B : Module.Basis ι F E) (m : ℤ)
    (hm : ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x)) (t : HeightOneSpectrum (𝓞 F))
    (c : 𝓞 F) (k : ι) {s : E ⊗[F] t.adicCompletion F} (hs : s ∈ tensA (E := E) t) :
    ∃ u ∈ t.adicCompletionIntegers F, (m : t.adicCompletion F) *
        tcoord B k (t.adicCompletion F) (PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) =
      algebraMap F (t.adicCompletion F) (c : F) * u := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hs'
    refine ⟨algebraMap F (t.adicCompletion F) ((m : F) * B.coord k x) * y,
      mul_mem (intInt t (hm x hx k)) hy, ?_⟩
    have e1 : PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) *
        (x ⊗ₜ[F] y) = (algebraMap F E (c : F) * x) ⊗ₜ[F] y := by
      simp [PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, tcoord_tmul, ← Algebra.smul_def (c : F) x, map_smul, smul_eq_mul, Algebra.smul_def]
    simp only [map_mul, map_intCast]
    ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u1, hu1, e1⟩ := ha
    obtain ⟨u2, hu2, e2⟩ := hb
    refine ⟨u1 + u2, add_mem hu1 hu2, ?_⟩
    rw [mul_add, map_add (f := _), mul_add, e1, e2, mul_add]
  | neg a _ ha =>
    obtain ⟨u1, hu1, e1⟩ := ha
    refine ⟨-u1, neg_mem hu1, ?_⟩
    rw [mul_neg, map_neg, mul_neg, e1, mul_neg]

private theorem exists_int_mul_isIntegral' {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * e) := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hI : Ideal.span {d} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hc : (Ideal.span {d}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ := fun h =>
    hI (Ideal.eq_bot_of_comap_eq_bot h)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hm
  obtain ⟨k, hk⟩ := hm
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hmE : (m : E) = algebraMap (𝓞 E) E k * algebraMap (𝓞 E) E d := by
    rw [← map_mul, hk]
    simp
  have hw : algebraMap (𝓞 E) E (k * n) = (m : E) * e := by
    rw [← hnd, hmE, map_mul]
    field_simp
    try ring
  refine ⟨m, hm0, ?_⟩
  rw [← hw]
  exact NumberField.RingOfIntegers.isIntegral_coe (k * n)

theorem coordBound {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x) := by
  classical
  let bw := NumberField.RingOfIntegers.basis E
  choose m hm hmi using fun (p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × ι) =>
    exists_int_mul_isIntegral' (B.coord p.2 (algebraMap (𝓞 E) E (bw p.1)))
  refine ⟨∏ p, m p, Finset.prod_ne_zero_iff.2 fun p _ => hm p, fun x hx k => ?_⟩
  obtain ⟨w, rfl⟩ := hx
  have hx' : algebraMap (𝓞 E) E w = ∑ i, ((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i) := by
    conv_lhs => rw [← bw.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [show B.coord k (((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i)) =
      ((bw.repr w i : ℤ) : F) * B.coord k (algebraMap (𝓞 E) E (bw i)) by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, k))
  have hq' : IsIntegral ℤ (((q * (bw.repr w i) : ℤ)) : F) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F (q * bw.repr w i)))
  convert hq'.mul (hmi (i, k)) using 1
  rw [hq]
  push_cast
  ring

theorem basisInt {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k, IsIntegral ℤ ((n : E) * B k) := by
  classical
  choose m hm hmi using fun k => exists_int_mul_isIntegral' (B k)
  refine ⟨∏ k, m k, Finset.prod_ne_zero_iff.2 fun k _ => hm k, fun k => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
  have hq' : IsIntegral ℤ ((q : E)) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E q))
  rw [hq, Int.cast_mul, mul_comm ((m k : ℤ) : E), mul_assoc]
  exact hq'.mul (hmi k)

end T

end HX


open HX in
theorem tensLocX_of (hI : LocInt) : TensLoc := by
  intro F E _ _ _ _ _
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨m, hm0, hm⟩ := coordBound B
  obtain ⟨n, hn0, hn⟩ := basisInt B
  refine ⟨((m * n : ℤ) : 𝓞 F), Int.cast_ne_zero.2 (mul_ne_zero hm0 hn0), ?_⟩
  rintro t e c ⟨s, hs, hse⟩
  have hsA := tensInt_le t hs
  have hk : ∀ k, ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F,
      ((m : F) * B.coord k e) * (d : F) = (c : F) * (a : F) := by
    intro k
    obtain ⟨u, hu, hue⟩ := tcoord_bound B m hm t c k hsA
    rw [← hse] at hue
    have h2 : tcoord B k (t.adicCompletion F)
        (PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e) =
          algebraMap F (t.adicCompletion F) (B.coord k e) := by
      simp [PI.UnitaryApproxDefs.inclE, tcoord_tmul, Algebra.smul_def]
    rw [h2] at hue
    exact hI F t ((m : F) * B.coord k e) c u hu (by rw [map_mul, map_intCast]; exact hue)
  choose d hd a ha using hk
  let D : 𝓞 F := ∏ k, d k
  have hD : D ∈ t.asIdeal.primeCompl := prod_mem fun k _ => hd k
  choose q hq using fun k => Finset.dvd_prod_of_mem d (Finset.mem_univ k)
  let β : _ → 𝓞 E := fun k => ⟨(n : E) * B k, hn k⟩
  have hcoeF : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (x : F) := by
    intro x
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have key : ∀ k, ((D : 𝓞 F) : F) * ((m : F) * B.coord k e) = (c : F) * ((a k * q k : 𝓞 F) : F) := by
    intro k
    have h1 : ((D : 𝓞 F) : F) = ((d k * q k : 𝓞 F) : F) := congrArg (fun x : 𝓞 F => (x : F)) (hq k)
    rw [h1]
    push_cast
    linear_combination (q k : F) * ha k
  refine ⟨algebraMap (𝓞 F) (𝓞 E) D, Submonoid.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hD,
    ∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k, ?_⟩
  have hy : ((∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k : 𝓞 E) : E) =
      ∑ k, algebraMap F E ((a k * q k : 𝓞 F) : F) * ((n : E) * B k) := by
    show algebraMap (𝓞 E) E (∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) (hcoeF _) rfl
  rw [hcoeF, hy]
  conv_lhs => rw [← B.sum_repr e]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, ← Module.Basis.coord_apply]
  have hk2 := congrArg (algebraMap F E) (key k)
  push_cast at hk2 ⊢
  simp only [map_mul, map_intCast] at hk2 ⊢
  linear_combination ((n : E) * B k) * hk2

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

