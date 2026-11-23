module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0002
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsBox
section
noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

section Fac

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem exists_box_alt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) :
    ∃ S : ∀ i, Set (α i), (∀ i, MeasurableSet (S i)) ∧ (∀ i, μ i (S i) ≠ 0) ∧ ∀ i, μ i (S i) ≠ ∞ := by
  have key : ∀ i, ∃ s : Set (α i), MeasurableSet s ∧ μ i s ≠ 0 ∧ μ i s ≠ ∞ := by
    intro i
    by_contra hc
    push_neg at hc
    apply hne i
    have hz : ∀ n, μ i (spanningSets (μ i) n) = 0 := fun n => by
      by_contra h0
      exact (measure_spanningSets_lt_top (μ i) n).ne (hc _ (measurableSet_spanningSets _ n) h0)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ i)]
    exact measure_iUnion_null hz
  choose S hS1 hS2 hS3 using key
  exact ⟨S, hS1, hS2, hS3⟩

theorem pi_box_eval (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (S : ∀ i, Set (α i)) (v : ι) (A : Set (α v)) :
    Measure.pi μ (Set.univ.pi (Function.update S v A)) = μ v A * ∏ w ∈ Finset.univ.erase v, μ w (S w) := by
  rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem factor_eq (μ μ' : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)]
    (hne : ∀ i, μ i ≠ 0) (v : ι) (hw : ∀ w, w ≠ v → μ' w = μ w) (h : Measure.pi μ' = Measure.pi μ) : μ' v = μ v := by
  obtain ⟨S, -, hS0, hSt⟩ := exists_box_alt μ hne
  ext A _
  have h1 := pi_box_eval μ' S v A
  have h2 := pi_box_eval μ S v A
  have hP : ∏ w ∈ Finset.univ.erase v, μ' w (S w) = ∏ w ∈ Finset.univ.erase v, μ w (S w) :=
    Finset.prod_congr rfl fun w hm => by rw [hw w (Finset.ne_of_mem_erase hm)]
  rw [h, h2, hP] at h1
  have hP0 : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hS0 w
  have hPt : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ ∞ := ENNReal.prod_ne_top fun w _ => hSt w
  exact ((ENNReal.mul_left_inj hP0 hPt).mp h1).symm

theorem factor_conc (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) (N : ∀ i, Set (α i))
    (hc : Measure.pi μ (Set.univ.pi N)ᶜ = 0) (v : ι) : μ v (N v)ᶜ = 0 := by
  have hsub : Set.univ.pi (Function.update (fun w => (Set.univ : Set (α w))) v (N v)ᶜ) ⊆
      (Set.univ.pi N)ᶜ := by
    intro x hx hxN
    have hv := hx v (Set.mem_univ v)
    rw [Function.update_self] at hv
    exact hv (hxN v (Set.mem_univ v))
  have h0 := measure_mono_null hsub hc
  rw [pi_box_eval] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exfalso
    obtain ⟨w, -, hw⟩ := Finset.prod_eq_zero_iff.mp h
    exact hne w (Measure.measure_univ_eq_zero.mp hw)

theorem factor_ne (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : Measure.pi μ ≠ 0) (v : ι) : μ v ≠ 0 := by
  intro hv
  apply h
  rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ Set.univ, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

end Fac

section FacG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, SecondCountableTopology (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, BorelSpace (G v)]

theorem factor_uniq (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (H : ∀ v, Subgroup (G v))
    (hH : ∀ v, IsClosed (H v : Set (G v))) (ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (ν v)]
    (hνc : ∀ v, ν v (H v : Set (G v))ᶜ = 0) (hνi : ∀ v, ∀ h ∈ H v, (ν v).map (fun x => h * x) = ν v)
    (hν0 : ∀ v, ν v ≠ 0) (h0 : Measure.pi μ ≠ 0)
    (hc : Measure.pi μ (Set.univ.pi fun v => (H v : Set (G v)))ᶜ = 0)
    (hi : ∀ g : (v : ι) → G v, (∀ v, g v ∈ H v) → (Measure.pi μ).map (fun x => g * x) = Measure.pi μ) (v : ι) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • ν v := by
  have hne : ∀ w, μ w ≠ 0 := fun w => factor_ne μ h0 w
  have hμc : μ v (H v : Set (G v))ᶜ = 0 := factor_conc μ hne (fun w => (H w : Set (G w))) hc v
  have hμi : ∀ h ∈ H v, (μ v).map (fun x => h * x) = μ v := by
    intro h hh
    let g : (w : ι) → G w := Pi.mulSingle v h
    have hg : ∀ w, g w ∈ H w := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [g] using hh
      · simp [g, Pi.mulSingle_eq_of_ne hw, (H w).one_mem]
    let μ' : ∀ w, Measure (G w) := fun w => (μ w).map (fun x => g w * x)
    haveI hσ : ∀ w, SigmaFinite (μ' w) := fun w =>
      (MeasurableEquiv.mulLeft (g w)).sigmaFinite_map (μ := μ w)
    have hpi : Measure.pi μ' = Measure.pi μ := by
      rw [← Measure.pi_map_pi (fun w => (measurable_const_mul (g w)).aemeasurable)]
      exact hi g hg
    have hw : ∀ w, w ≠ v → μ' w = μ w := by
      intro w hw
      simp [μ', g, Pi.mulSingle_eq_of_ne hw]
    have := factor_eq μ μ' hne v hw hpi
    simpa [μ', g] using this
  exact uniq_on_closed (H v) (hH v) (μ v) (ν v) hμc (hνc v) hμi (hνi v) (hne v) (hν0 v)

end FacG

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem liesOver_natCast (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hne : Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal ≠ ⊤ := Ideal.comap_ne_top _ v.isPrime.ne_top
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hv
  constructor
  exact hmax.eq_of_le hne hle

theorem image_places_primesOver (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_natCast p hp v hv⟩
  · rintro ⟨hP, hPo⟩
    have h' : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [hPo.over] at h'
    have h'' : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := h'
    have hmem : ((p : ℕ) : 𝓞 K) ∈ P := by simpa using h''
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hmem
      exact hp.ne_zero (by exact_mod_cast hmem)
    exact ⟨⟨P, hP, hne⟩, hmem, rfl⟩

theorem ram_inertia_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _
    (fun v w h => HeightOneSpectrum.ext h), image_places_primesOver p hp,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones] at hsum
  have hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hql⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q) (Ideal.inertiaDeg_pos q ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm
    ⟨v.asIdeal, v.isPrime, liesOver_natCast p hp v hv⟩ (Finset.mem_univ _)
  exact ⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩

theorem card_quot_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := liesOver_natCast p hp v hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  have hf := (ram_inertia_split p hp hs v hv).2
  have h2 : (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal = 1 := by
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, hf]
  rw [h2, pow_one] at h
  rw [← h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem intValuation_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  have := v.isPrime
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have := liesOver_natCast p hp v hv
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    v.asIdeal hne
  rw [hmap, (ram_inertia_split p hp hs v hv).1] at he
  rw [v.intValuation_eq_exp_neg_multiplicity hr, ← he]
  rfl

end Deg

theorem ram_inertia_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_natCast p hp v hv
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
      rw [hPZ.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))
    exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
  have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [← hPZ.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  obtain ⟨he, hf⟩ := ram_inertia_split (K := E) p hp hs ⟨P, hPp, hP0⟩ hPmem
  change P.ramificationIdx ℤ = 1 at he
  change P.inertiaDeg ℤ = 1 at hf
  rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P] at he
  rw [Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩

theorem split_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E) :
    {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 F)
  have hone : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    rintro ⟨q, hq, hql⟩
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hql.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    have hqmem : ((p : ℕ) : 𝓞 F) ∈ q := by
      have : (p : ℤ) ∈ q.under ℤ := by rw [← hql.over]; exact Ideal.mem_span_singleton_self _
      simpa using this
    obtain ⟨h1, h2⟩ := ram_inertia_sub (E := E) p hp hs ⟨q, hq, hq0⟩ hqmem
    change q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [RingOfIntegers.rank] at hsum
  rw [← hsum, ← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h),
    image_places_primesOver p hp, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem split_prime_local_holds : SplitPrimeLoc := by
  intro F E _ _ _ _ _ p hp hs
  have hF := split_sub (F := F) (E := E) p hp hs
  refine ⟨fun v hv => ⟨card_quot_split p hp hF v hv, ?_⟩, hF⟩
  have h1 := intValuation_split p hp hF v hv
  first
  | exact h1
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; norm_cast; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; rfl)

end Formalism.L2.SG.Pf.SatGramLoc

end
end

