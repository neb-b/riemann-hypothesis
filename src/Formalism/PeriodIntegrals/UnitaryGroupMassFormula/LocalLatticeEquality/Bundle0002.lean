module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0014

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.AvoidP
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

theorem unitP : UnitP := by
  intro F E _ _ _ _ _ sig p A d hd
  have hv1 : p.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) p).2 hd
  have h1 : A.ιF (algebraMap (𝓞 F) F d) ≤ᵥ A.ιF 1 := (A.val _ _).2 (by rw [hv1, map_one])
  have h2 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F d) := (A.val _ _).2 (by rw [hv1, map_one])
  rw [map_one] at h1 h2
  have hcv : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F d)) = 1 :=
    le_antisymm ((Valuation.vle_one_iff _).1 h1) ((Valuation.one_vle_iff _).1 h2)
  have hc0 : A.ιF (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact zero_ne_one hcv
  have hinv : (A.ιF (algebraMap (𝓞 F) F d))⁻¹ ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hcv, inv_one]
  refine ⟨algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹, ?_, ?_⟩
  · rw [A.O_def]
    have hu : algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d))⁻¹ =
        algebraMap 𝒪[A.Fp] A.Ep ⟨_, hinv⟩ := rfl
    rw [hu]
    exact isIntegral_algebraMap
  · have hd' : A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) =
        algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F d)) := by
      rw [← A.compat]
      rfl
    rw [hd', ← map_mul, inv_mul_cancel₀ hc0, map_one]

theorem avoidP : AvoidP := by
  intro F E _ _ _ _ _ p I hI
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ p.asIdeal := by
    intro d hd
    by_contra hdp
    exact hne d hdp hd
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := by
    intro a b hab
    have hE : algebraMap F E (a : F) = algebraMap F E (b : F) := congrArg (fun x : 𝓞 E => (x : E)) hab
    exact Subtype.ext ((algebraMap F E).injective hE)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [← hQp, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  exact hI ⟨Q, hQ, hQ0⟩ hQp hIQ

end PI.LocLatEq.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreGenIdeal
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem core_gen_ideal (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 E)) :
    ∃ a ∈ 𝔞, ∀ b ∈ 𝔞, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d * b = r * a := by
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · refine ⟨0, 𝔞.zero_mem, fun b hb => ⟨1, ?_, 0, ?_⟩⟩
    · exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · rw [h𝔞, Ideal.mem_bot] at hb
      simp [hb]
  have h𝔞0 : 𝔞 ≠ 0 := h𝔞
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hpE0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
    exact p.ne_bot
  have hle : 𝔞 * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ 𝔞 :=
    Ideal.mul_le_inf.trans inf_le_left
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle (mul_ne_zero h𝔞0 hpE0)
  have haa : a ∈ 𝔞 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨𝔠, h𝔠⟩ : 𝔞 ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haa)
  have hav : ∀ P : HeightOneSpectrum (𝓞 E),
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ¬ 𝔠 ≤ P.asIdeal := by
    intro P hP hcP
    have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ P.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hP.ge
    have h2 : 𝔞 ≤ 𝔞 * P.asIdeal := by
      conv_lhs => rw [← ha]
      refine sup_le (Ideal.mul_mono_right h1) ?_
      rw [h𝔠]
      exact Ideal.mul_mono_right hcP
    have h3 : 𝔞 * P.asIdeal ∣ 𝔞 * 1 := by
      rw [mul_one]
      exact Ideal.dvd_iff_le.mpr h2
    have h4 := (mul_dvd_mul_iff_left h𝔞0).mp h3
    exact P.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h4))
  obtain ⟨d, hdp, hd⟩ := hA F E p 𝔠 hav
  refine ⟨a, haa, fun b hb => ⟨d, hdp, ?_⟩⟩
  have hmem : algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {a} := by
    rw [h𝔠, mul_comm (algebraMap (𝓞 F) (𝓞 E) d) b]
    exact Ideal.mul_mem_mul hb hd
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨r, hr.symm⟩

theorem core_gen (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (I : Submodule (𝓞 E) E)
    (hI : I.FG) : ∃ a ∈ I, ∀ b ∈ I, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d • b = r • a := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S
  have hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)
  have hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E),
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hc x hx
      exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hz
      exact ⟨y1 + y2, by rw [map_add (f := _), h1, h2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨y, h⟩ := hx
      refine ⟨r * y, ?_⟩
      rw [map_mul, h]
      simp only [Algebra.smul_def]
      ring
  obtain ⟨a0, ha0, hgen⟩ := core_gen_ideal (F := F) hA p
    ((Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at ha0
  refine ⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b := by
    rw [Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0,
      one_mul]
  have hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹) := by
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]
    exact hb
  obtain ⟨d, hd, r, hr⟩ := hgen y hy𝔞
  refine ⟨d, hd, r, ?_⟩
  rw [← hyb, smul_smul, smul_smul, hr]

end PI.LocLatEq.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.EpNontrivial
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem int_of_val (A : LocAt F E sig p) (x : F) (hx : A.ιF x ∈ 𝒪[A.Fp]) :
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * x = n := by
  rw [Valuation.mem_integer_iff] at hx
  have h1 : A.ιF x ≤ᵥ A.ιF 1 := by
    rw [map_one, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A.Fp), map_one]
    exact hx
  have hv : p.valuation F x ≤ 1 := by
    have := (A.val x 1).mp h1
    rwa [map_one] at this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p x hv
  refine ⟨d, d.2, n, ?_⟩
  rw [mul_comm]
  exact hnd

theorem ep_nontrivial (A : LocAt F E sig p) : Nontrivial A.Ep := by
  have := A.free
  exact Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

theorem coeff_mem (h2 : Module.finrank F E = 2) (A : LocAt F E sig p) (a : E)
    (ha : IsIntegral 𝒪[A.Fp] (A.ιE a)) (hnot : a ∉ (algebraMap F E).range) (i : ℕ) :
    A.ιF ((minpoly F a).coeff i) ∈ 𝒪[A.Fp] := by
  classical
  haveI := ep_nontrivial A
  haveI := A.free
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    apply hnot
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hspanP : ⊤ ≤ Submodule.span A.Fp (Set.range ![(1 : A.Ep), A.ιE a]) := by
    rw [← A.span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx := B.sum_repr x
    rw [hB, Fin.sum_univ_two] at hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
    have : A.ιE x = A.ιF (B.repr x 0) • (1 : A.Ep) + A.ιF (B.repr x 1) • A.ιE a := by
      conv_lhs => rw [← hx]
      simp only [map_add (f := _), map_mul, map_one, Algebra.smul_def, A.compat, mul_one]
    rw [SetLike.mem_coe, this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hliP : LinearIndependent A.Fp ![(1 : A.Ep), A.ιE a] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanP (by simp [A.rank])
  have hnotP : A.ιE a ∉ (algebraMap A.Fp A.Ep).range := by
    rintro ⟨c, hc⟩
    rw [LinearIndependent.pair_iff' one_ne_zero] at hliP
    apply hliP c
    rw [← hc, Algebra.algebraMap_eq_smul_one]
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  have hintP : IsIntegral A.Fp (A.ιE a) := Algebra.IsIntegral.isIntegral _
  have hdegP : 2 ≤ (minpoly A.Fp (A.ιE a)).natDegree := by
    have h0 := minpoly.natDegree_pos hintP
    have h1 : (minpoly A.Fp (A.ιE a)).natDegree ≠ 1 := fun h => hnotP (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
  have hdegF : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  set g : A.Fp[X] := (minpoly F a).map A.ιF with hg
  have hgmon : g.Monic := (minpoly.monic hintF).map _
  have hgdeg : g.natDegree ≤ 2 := by
    rw [hg, natDegree_map]
    exact hdegF
  have hgα : aeval (A.ιE a) g = 0 := by
    rw [hg, aeval_def, eval₂_map]
    have hcomp : (algebraMap A.Fp A.Ep).comp A.ιF = A.ιE.comp (algebraMap F E) := by
      ext y
      simp [A.compat]
    rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hdvd : minpoly A.Fp (A.ιE a) ∣ g := minpoly.dvd A.Fp _ hgα
  have hgeq : g = minpoly A.Fp (A.ιE a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintP) hgmon hdvd (by omega)
  have hdvd2 : minpoly A.Fp (A.ιE a) ∣ (minpoly 𝒪[A.Fp] (A.ιE a)).map (algebraMap 𝒪[A.Fp] A.Fp) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, minpoly.aeval]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd A.Fp (minpoly.monic ha) hdvd2
  rw [(minpoly.monic hintP).leadingCoeff, C_1, mul_one] at hg'
  have hc := congrArg (fun q => q.coeff i) (hg'.trans hgeq.symm)
  simp only [coeff_map, hg] at hc
  rw [← hc]
  exact (g'.coeff i).2

theorem intP : IntP := by
  intro F E _ _ _ _ _ h2 sig p A a ha
  rw [A.O_def] at ha
  have := ep_nontrivial A
  by_cases hr : a ∈ (algebraMap F E).range
  · obtain ⟨f, rfl⟩ := hr
    have hf : A.ιF f ∈ 𝒪[A.Fp] := by
      rw [A.compat] at ha
      have hi : IsIntegral 𝒪[A.Fp] (A.ιF f) :=
        (isIntegral_algebraMap_iff ).mp ha
      exact (Valuation.integer.integers _).mem_of_integral hi
    obtain ⟨d, hd, n, hn⟩ := int_of_val A f hf
    refine ⟨d, hd, algebraMap (𝓞 F) (𝓞 E) n, ?_⟩
    change algebraMap F E (d : F) * algebraMap F E f = algebraMap F E (n : F)
    rw [← map_mul, hn]
  · have hc : ∀ i, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * (minpoly F a).coeff i = n :=
      fun i => int_of_val A _ (coeff_mem h2 A a ha hr i)
    obtain ⟨d0, hd0, n0, hn0⟩ := hc 0
    obtain ⟨d1, hd1, n1, hn1⟩ := hc 1
    have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
    have hdeg : (minpoly F a).natDegree = 2 := by
      have h1 : (minpoly F a).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.mp h)
      have h0 := minpoly.natDegree_pos hintF
      have := minpoly.natDegree_le (A := F) a
      rw [h2] at this
      omega
    have hlead : (minpoly F a).coeff 2 = 1 := by
      have := (minpoly.monic hintF).leadingCoeff
      rwa [leadingCoeff, hdeg] at this
    have hrel : algebraMap F E ((minpoly F a).coeff 0) + algebraMap F E ((minpoly F a).coeff 1) * a
        + a ^ 2 = 0 := by
      have := minpoly.aeval F a
      rw [aeval_eq_sum_range' (n := 3) (by omega)] at this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, Algebra.smul_def,
        map_one, pow_zero, pow_one, one_mul, mul_one, zero_add] at this
      linear_combination this
    have hd : d0 * d1 ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd0 hd1
    have hint : IsIntegral (𝓞 F) (algebraMap F E ((d0 * d1 : 𝓞 F) : F) * a) := by
      refine ⟨X ^ 2 + C (d0 * n1) * X + C (d0 * d1 * d1 * n0), by monicity!, ?_⟩
      simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
      have e0 := congrArg (algebraMap F E) hn0
      have e1 := congrArg (algebraMap F E) hn1
      simp only [map_mul] at e0 e1
      simp only [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_mul] at *
      change _ = algebraMap F E (n0 : F) at e0
      linear_combination (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) ^ 2 * hrel
        - (algebraMap F E (d0 : F) * (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) * a) * e1
        - (algebraMap F E (d0 : F) * algebraMap F E (d1 : F) ^ 2) * e0
    obtain ⟨b, hb⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := 𝓞 F) (B := E) |>.mp hint
    refine ⟨d0 * d1, hd, b, ?_⟩
    rw [show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, hb]
    rfl

end PI.LocLatEq.W
end
end

