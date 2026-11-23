module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

@[expose] public section

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SFewOfCut
section
noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain UpperTheory.V.KL UpperTheory.V.ZK

namespace LateralTheory.Q.SFewOfCut

theorem one_add_pow_eq (w : ℤ) (d : ℕ) : ∃ t : ℤ, (1 + w) ^ d = 1 + w * (d + w * t) := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + d + w * t, by rw [pow_succ, ht]; push_cast; ring⟩

theorem not_dvd_pow_sub_one (l c M d : ℕ) (hl : l.Prime) (hM : M < l ^ c) (hd0 : 0 < d) (hd : d < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ d - 1 := by
  obtain ⟨t, ht⟩ := one_add_pow_eq ((l : ℤ) ^ c) d
  have hl0 : (l : ℤ) ^ c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  rw [ht, add_sub_cancel_left, pow_add, mul_dvd_mul_iff_left hl0]
  intro h
  have key : ∀ j, j ≤ c → j ≤ M → l ^ j ≤ d := by
    intro j hjc hjM
    have h1 : (l : ℤ) ^ j ∣ (d : ℤ) + (l : ℤ) ^ c * t := (pow_dvd_pow _ hjM).trans h
    have h2 : (l : ℤ) ^ j ∣ (d : ℤ) := (dvd_add_left ((pow_dvd_pow _ hjc).mul_right t)).1 h1
    exact Nat.le_of_dvd hd0 (by exact_mod_cast h2)
  rcases le_total c M with h1 | h1
  · have := key c le_rfl h1; omega
  · have := key M h1 le_rfl
    have := Nat.lt_pow_self (n := M) hl.one_lt
    omega

theorem cast_dvd_of_not_dvd (l ν w : ℕ) (hl : l.Prime) (f : ℤ) (hf : ¬ (l : ℤ) ^ w ∣ f) :
    (f : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ w := by
  induction w generalizing f with
  | zero => simp at hf
  | succ w ih =>
    by_cases h : (l : ℤ) ∣ f
    · obtain ⟨g, rfl⟩ := h
      have hg : ¬ (l : ℤ) ^ w ∣ g := fun h => hf (by rw [pow_succ']; exact mul_dvd_mul_left _ h)
      rw [pow_succ']
      push_cast
      exact mul_dvd_mul_left _ (ih g hg)
    · have hc : IsCoprime f ((l : ℤ) ^ ν) :=
        (((Nat.prime_iff_prime_int.1 hl).irreducible.coprime_iff_not_dvd.2 h).symm).pow_right
      obtain ⟨a, b, hab⟩ := hc
      have h0 : ((l : ZMod (l ^ ν))) ^ ν = 0 := by exact_mod_cast ZMod.natCast_self (l ^ ν)
      have h1 : (f : ZMod (l ^ ν)) * a = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod (l ^ ν)) hab
        push_cast at this
        rw [h0] at this
        linear_combination this
      exact (Dvd.intro _ h1).trans (one_dvd _)

theorem not_dvd_sub (l c M i j : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hij : j < i) (hi : i < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ i - (1 + (l : ℤ) ^ c) ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  intro h
  have h1 : (1 + (l : ℤ) ^ c) ^ (j + d) - (1 + (l : ℤ) ^ c) ^ j =
      (1 + (l : ℤ) ^ c) ^ j * ((1 + (l : ℤ) ^ c) ^ d - 1) := by ring
  rw [h1] at h
  have hco : IsCoprime (l : ℤ) (1 + (l : ℤ) ^ c) := by
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
    exact ⟨-(l : ℤ) ^ c', 1, by ring⟩
  exact not_dvd_pow_sub_one l c M d hl hM (by omega) (by omega) (hco.pow.dvd_of_dvd_mul_left h)

theorem pe_dvd (l c ν M E : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hE : E < M) :
    (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ (M * (c + M)) := by
  have h1 : (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣
      ∏ _j ∈ (Finset.range M).erase E, (l : ZMod (l ^ ν)) ^ (c + M) := by
    unfold pe
    rw [Int.cast_prod]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun j hj => cast_dvd_of_not_dvd l ν _ hl _ ?_
    rw [Finset.mem_erase, Finset.mem_range] at hj
    push_cast
    rcases lt_or_gt_of_ne hj.1 with h | h
    · exact not_dvd_sub l c M E j hl hc hM h hE
    · rw [dvd_sub_comm]
      exact not_dvd_sub l c M j E hl hc hM h hj.2
  refine h1.trans ?_
  rw [Finset.prod_const, ← pow_mul, mul_comm]
  refine pow_dvd_pow _ (Nat.mul_le_mul_right _ ?_)
  exact (Finset.card_erase_le).trans (Finset.card_range M).le

theorem exists_index (G : Type) [CommGroup G] [Finite G] [IsCyclic G] (q : ℕ) (hq : q ∣ Nat.card G) :
    ∃ v : G →* Cq q, ∀ u, v u = 1 → ∃ s, u = s ^ q := by
  let e : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv inferInstance
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(AddMonoidHom.toMultiplicative (ZMod.castHom hq (ZMod q)).toAddMonoidHom).comp e.symm.toMonoidHom, ?_⟩
  intro u hu
  obtain ⟨x, rfl⟩ := e.surjective u
  have h1 : ZMod.castHom hq (ZMod q) (Multiplicative.toAdd x) = 0 := by
    simpa using congrArg Multiplicative.toAdd hu
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (Multiplicative.toAdd x)
  rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, rfl⟩ := h1
  refine ⟨e (Multiplicative.ofAdd (m : ZMod _)), ?_⟩
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, hn, ofAdd_toAdd]

theorem prim_map {R k : Type} [CommRing R] [IsDomain R] [Field k] (r : R →+* k) (l ν : ℕ) (hl : l.Prime)
    (hν : 1 ≤ ν) (hr : r l ≠ 0) (ζ : Rˣ) (hζ : IsPrimitiveRoot ζ (l ^ ν)) :
    IsPrimitiveRoot (Units.map (r : R →* k) ζ) (l ^ ν) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hν
  have h1 : Units.map (r : R →* k) ζ ^ l ^ (n + 1) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ¬ Units.map (r : R →* k) ζ ^ l ^ n = 1 := by
    intro h
    have h3 : IsPrimitiveRoot ((ζ : R) ^ l ^ n) l :=
      (IsPrimitiveRoot.coe_units_iff.2 hζ).pow (pow_pos hl.pos _) (pow_succ l n)
    have h4 := congrArg r (h3.geom_sum_eq_zero hl.one_lt)
    have h5 : r ((ζ : R) ^ l ^ n) = 1 := by simpa using congrArg Units.val h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h4
    simp only [map_pow r ((ζ : R) ^ l ^ n), h5] at h4
    apply hr
    simpa using h4
  rw [← orderOf_eq_prime_pow h2 h1]
  exact IsPrimitiveRoot.orderOf _

section Res

variable {F : Type} [Field F] {k : Type} [Field k] {r : 𝓞 F →+* k}

theorem res_one : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem res_mul {α β : Fˣ} {u w : kˣ} (h : Res r α u) (h' : Res r β w) : Res r (α * β) (u * w) := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  obtain ⟨a', b', hb', h1', h2'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · have e1 : ((b * b' : 𝓞 F) : F) = (b : F) * (b' : F) := rfl
    have e2 : ((a * a' : 𝓞 F) : F) = (a : F) * (a' : F) := rfl
    rw [e1, e2, ← h1, ← h1', Units.val_mul]; ring
  · rw [map_mul, map_mul, h2, h2', Units.val_mul]; ring

theorem res_inv {α : Fˣ} {u : kˣ} (h : Res r α u) : Res r α⁻¹ u⁻¹ := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  refine ⟨b, a, by rw [h2]; exact mul_ne_zero u.ne_zero hb, ?_, ?_⟩
  · rw [← h1, Units.inv_mul_cancel_left]
  · rw [h2, Units.inv_mul_cancel_left]

theorem res_pow {α : Fˣ} {u : kˣ} (h : Res r α u) (n : ℕ) : Res r (α ^ n) (u ^ n) := by
  induction n with
  | zero => simpa using res_one
  | succ n ih => rw [pow_succ, pow_succ]; exact res_mul ih h

end Res

theorem isPrimFam_pi {R A I : Type} [CommRing R] [CommRing A] {m : ℕ}
    (Φ : I → ∀ n : ℕ, Ch A (GL (Fin n) R) (m + 1) →ₗ[A] A) (h : ∀ i, IsPrimFam (Φ i)) :
    IsPrimFam fun n => LinearMap.pi fun i => Φ i n :=
  ⟨fun n z hz => funext fun i => (h i).bdry n z hz, fun n n' hn z hz => funext fun i => (h i).stab n n' hn z hz,
    fun d n z hz => funext fun i => (h i).psi d n z hz⟩

theorem sFewOf : SFewOf := by
  classical
  intro hT hP hC hU hD L F _ _ _ _ _ hL l c ν e hl ζ γ hlay hc hr S hS hinj
  choose 𝔡 h𝔡 using hS
  choose N y b hy hb hval using fun α : S => hC L F l c ν e ζ γ hlay hc α (𝔡 α α.2) (h𝔡 α α.2)
  have hl0 : (l : 𝓞 F) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hb0 : (l : 𝓞 F) * ∏ α, b α ≠ 0 := mul_ne_zero hl0 (Finset.prod_ne_zero_iff.2 fun α _ => hb α)
  let I : Type := {P : HeightOneSpectrum (𝓞 F) // (l : 𝓞 F) * ∏ α, b α ∉ P.asIdeal ∧
    Function.Surjective ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F)))}
  have main : ∀ P : I, ∃ Φ : ∀ n : ℕ, Ch (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) (2 * e + 2 + 1) →ₗ[ZMod (l ^ ν)]
      ZMod (l ^ ν), IsPrimFam Φ ∧ ∀ α α' : S, l ^ (2 * e + 2) • Φ _ (y α) = l ^ (2 * e + 2) • Φ _ (y α') →
        letI := P.1.isMaximal
        letI := Ideal.Quotient.field P.1.asIdeal
        ∃ s : (𝓞 F ⧸ P.1.asIdeal)ˣ, Res (Ideal.Quotient.mk P.1.asIdeal)
          (nrm γ ((1 + l ^ c) ^ (e + 1)) α ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
            (nrm γ ((1 + l ^ c) ^ (e + 1)) α' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (s ^ l ^ ν) := by
    rintro ⟨P, hPb, hPs⟩
    letI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    haveI : Finite (𝓞 F ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    have hlP : Ideal.Quotient.mk P.asIdeal (l : 𝓞 F) ≠ 0 := fun h =>
      hPb (Ideal.mul_mem_right _ _ (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hbP : ∀ α, Ideal.Quotient.mk P.asIdeal (b α) ≠ 0 := fun α h =>
      hPb (Ideal.mem_of_dvd _ ((Finset.dvd_prod_of_mem b (Finset.mem_univ α)).mul_left _)
        (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hz := prim_map (Ideal.Quotient.mk P.asIdeal) l ν hl.out (hlay.c_pos.trans hlay.c_le) hlP ζ hlay.prim
    obtain ⟨v, hv⟩ := exists_index (𝓞 F ⧸ P.asIdeal)ˣ (l ^ ν) (by rw [hz.eq_orderOf]; exact orderOf_dvd_natCard _)
    obtain ⟨θ, hθ, hθv⟩ := hT _ (l ^ ν) e _ hz v
    refine ⟨_, hP _ _ _ θ hθ (𝓞 L) ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F))), ?_⟩
    intro α α' hαα
    obtain ⟨u, hu, hu1⟩ := hval α _ _ hPs (hbP α) _ v θ hθ hθv
    obtain ⟨u', hu', hu1'⟩ := hval α' _ _ hPs (hbP α') _ v θ hθ hθv
    simp only [LinearMap.comp_apply] at hαα
    rw [hu1, hu1'] at hαα
    obtain ⟨x, hx⟩ := pe_dvd l c ν (2 * e + 3) (e + 1) hl.out hlay.c_pos hc (by omega)
    obtain ⟨s, hs⟩ := hv (u ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
        (u' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (by
      rw [map_mul, map_inv, map_pow, map_pow, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_pow]
      simp only [nsmul_eq_mul, Nat.cast_pow] at hαα ⊢
      rw [pow_add, hx]
      linear_combination x * hαα)
    exact ⟨s, hs ▸ res_mul (res_pow hu _) (res_inv (res_pow hu' _))⟩
  choose Φ hΦ hsep using main
  let f : S → (I → ZMod (l ^ ν)) := fun α => l ^ (2 * e + 2) • (LinearMap.pi fun i => Φ i (N α)) (y α)
  have hf : Function.Injective f := by
    intro α α' h
    obtain ⟨δ, hδ⟩ := hD L F l ν hl.out ζ hlay.prim _ _ hb0 fun P _ hPb hPs =>
      hsep ⟨P, hPb, hPs⟩ α α' (congrFun h ⟨P, hPb, hPs⟩)
    exact Subtype.ext (hinj _ α.2 _ α'.2 ⟨δ, (mul_inv_eq_iff_eq_mul.1 hδ).trans (mul_comm _ _)⟩)
  have hcard := hU L hL (2 * e + 2) ⟨e + 1, by ring⟩ hr l ν (I → ZMod (l ^ ν)) _ (isPrimFam_pi Φ hΦ)
    (Finset.univ.image f) (by
      intro s hs
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hs
      exact ⟨N α, y α, hy α, rfl⟩)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe,
    show 2 * (2 * e + 2 + 1) + 4 = 4 * e + 10 by ring] at hcard
  exact hcard

end LateralTheory.Q.SFewOfCut

end
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SSteinTPf
section
noncomputable section

open NumberField IsDedekindDomain FractionalIdeal Matrix
open scoped nonZeroDivisors

namespace LateralTheory.Q.SSteinT

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem val_eq_count (P : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-count K P (spanSingleton R⁰ x)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx
  have h : spanSingleton R⁰ (algebraMap R K r / algebraMap R K s) =
      spanSingleton R⁰ (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [count_well_defined K P (spanSingleton_ne_zero_iff.mpr hx) h, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg P hr0, HeightOneSpectrum.intValuation_if_neg P hs0,
    ← WithZero.exp_sub]
  congr 1
  ring

theorem val_le_of_mem (P : HeightOneSpectrum R) {I : FractionalIdeal R⁰ K} {x : K} (hx : x ∈ I) :
    P.valuation K x ≤ WithZero.exp (-count K P I) := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [val_eq_count P x h0, WithZero.exp_le_exp, neg_le_neg_iff]
  exact count_mono K P (spanSingleton_ne_zero_iff.mpr h0) (spanSingleton_le_iff_mem.mpr hx)

theorem exists_frac (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ ∀ P, count K P I = d P := by
  refine ⟨d.prod fun P n => (P.asIdeal : FractionalIdeal R⁰ K) ^ n, ?_, fun P => count_finsuppProd K P d⟩
  refine Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ ?_
  exact coeIdeal_ne_zero.mpr P.ne_bot

theorem exists_sl2_with_valuation_bounds (d e : HeightOneSpectrum R →₀ ℤ) :
    ∃ p q r s : K, p ≠ 0 ∧ p * s - q * r = 1 ∧ ∀ P : HeightOneSpectrum R,
      P.valuation K p ≤ WithZero.exp (-d P) ∧ P.valuation K q ≤ WithZero.exp (-e P) ∧
      P.valuation K r ≤ WithZero.exp (-(-e P)) ∧ P.valuation K s ≤ WithZero.exp (-(-d P)) := by
  obtain ⟨C, hC, hCd⟩ := exists_frac (K := K) d
  obtain ⟨D, hD, hDe⟩ := exists_frac (K := K) e
  obtain ⟨p, hp0, hp⟩ := exists_ne_zero_mem_isInteger hC
  set p' := algebraMap R K p with hp'
  have hp'0 : p' ≠ 0 := by
    rw [hp']
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp0
  have h1 : spanSingleton R⁰ p' * C⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hC]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.mpr hp) _
  obtain ⟨q, hq⟩ := exists_add_spanSingleton_mul_eq h1
    (mul_ne_zero (spanSingleton_ne_zero_iff.mpr hp'0) (inv_ne_zero hC)) (inv_ne_zero hD)
  have hqD : q ∈ D := by
    have h2 : spanSingleton R⁰ q * D⁻¹ ≤ 1 := by
      rw [← hq]
      exact le_sup_right
    have h3 : spanSingleton R⁰ q * D⁻¹ * D ≤ 1 * D := mul_le_mul_left h2 _
    rw [inv_mul_cancel_right₀ hD, one_mul] at h3
    exact spanSingleton_le_iff_mem.mp h3
  have h4 : (1 : K) ∈ spanSingleton R⁰ p' * C⁻¹ + spanSingleton R⁰ q * D⁻¹ := by
    rw [hq]
    exact one_mem_one _
  obtain ⟨u, hu, w, hw, huw⟩ := (mem_add _ _ _).mp h4
  obtain ⟨s, hs, rfl⟩ := mem_singleton_mul.mp hu
  obtain ⟨r, hr, rfl⟩ := mem_singleton_mul.mp hw
  refine ⟨p', q, -r, s, hp'0, by rw [← huw]; ring, fun P => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← hCd]; exact val_le_of_mem P hp
  · rw [← hDe]; exact val_le_of_mem P hqD
  · rw [← hDe, ← count_inv, Valuation.map_neg]; exact val_le_of_mem P hr
  · rw [← hCd, ← count_inv]; exact val_le_of_mem P hs

theorem val_comb (P : HeightOneSpectrum R) {u x u' x' : K} {m a m' a' c : ℤ}
    (hu : P.valuation K u ≤ WithZero.exp (-m)) (hx : P.valuation K x ≤ WithZero.exp (-a))
    (hu' : P.valuation K u' ≤ WithZero.exp (-m')) (hx' : P.valuation K x' ≤ WithZero.exp (-a'))
    (h : c = m + a) (h' : c = m' + a') : P.valuation K (u * x + u' * x') ≤ WithZero.exp (-c) := by
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, h, neg_add, WithZero.exp_add]; exact mul_le_mul' hu hx
  · rw [map_mul, h', neg_add, WithZero.exp_add]; exact mul_le_mul' hu' hx'

variable {J : Type} [Fintype J] [DecidableEq J]

def Lat (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (x : J → K) : Prop :=
  ∀ j P, P.valuation K (x j) ≤ WithZero.exp (-𝔞 j P)

def Rel (𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ) (β : K) : Prop :=
  ∃ M : Matrix J J K, M.det = β ∧ ∀ x : J → K, Lat 𝔞 x ↔ Lat 𝔟 (M *ᵥ x)

theorem Rel.refl (𝔞 : J → HeightOneSpectrum R →₀ ℤ) : Rel 𝔞 𝔞 (1 : K) :=
  ⟨1, det_one, fun x => by rw [one_mulVec]⟩

theorem Rel.trans {𝔞 𝔟 𝔠 : J → HeightOneSpectrum R →₀ ℤ} {β γ : K} (h : Rel 𝔞 𝔟 β) (h' : Rel 𝔟 𝔠 γ) :
    Rel 𝔞 𝔠 (γ * β) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨N, hN, h'⟩ := h'
  exact ⟨N * M, by rw [det_mul, hM, hN], fun x => by rw [h, h', mulVec_mulVec]⟩

theorem exists_block {i j : J} (hij : i ≠ j) {p q r s : K} (hp : p ≠ 0) (h : p * s - q * r = 1) :
    ∃ M : Matrix J J K, M.det = 1 ∧ ∀ x : J → K, (M *ᵥ x) i = p * x i + q * x j ∧
      (M *ᵥ x) j = r * x i + s * x j ∧ ∀ k, k ≠ i → k ≠ j → (M *ᵥ x) k = x k := by
  refine ⟨transvection j i (r / p) * diagonal (Pi.mulSingle i p * Pi.mulSingle j p⁻¹) *
    transvection i j (q / p), ?_, fun x => ?_⟩
  · rw [det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, det_diagonal]
    simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hp]
  · have hs : s = (1 + q * r) / p := by
      rw [← h]; field_simp; ring
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine ⟨?_, ?_, fun k hk hk' => ?_⟩
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm]
      field_simp
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm, hs]
      field_simp
      ring
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hk, hk']

theorem rel_move {i j : J} (hij : i ≠ j) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) :
    Rel 𝔞 (𝔞 + Pi.single i d - Pi.single j d) (1 : K) := by
  obtain ⟨p, q, r, s, hp, h, hv⟩ := exists_sl2_with_valuation_bounds (K := K) d (𝔞 i + d - 𝔞 j)
  obtain ⟨M, hM, hx⟩ := exists_block hij hp h
  refine ⟨M, hM, fun x => ?_⟩
  obtain ⟨hi, hj, hk⟩ := hx x
  constructor
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      rw [hi]
      refine val_comb P h1 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij] <;> ring
    by_cases hkj : k = j
    · subst hkj
      rw [hj]
      refine val_comb P h3 (H i P) h4 (H k P) ?_ ?_ <;> simp [hij.symm] <;> ring
    · rw [hk k hki hkj]
      simpa [hki, hkj] using H k P
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      have : x k = s * (M *ᵥ x) k + (-q) * (M *ᵥ x) j := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h2
      refine val_comb P h4 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    by_cases hkj : k = j
    · subst hkj
      have : x k = (-r) * (M *ᵥ x) i + p * (M *ᵥ x) k := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h3
      refine val_comb P h3 (H i P) h1 (H k P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    · have := H k P
      rw [hk k hki hkj] at this
      simpa [hki, hkj] using this

theorem rel_of_sum_eq (j₀ : J) (S : Finset J) : ∀ 𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ,
    (∀ j, j ∉ S → j ≠ j₀ → 𝔞 j = 𝔟 j) → ∑ j, 𝔞 j = ∑ j, 𝔟 j → Rel 𝔞 𝔟 (1 : K) := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝔞 𝔟 h hs
    have : 𝔞 = 𝔟 := by
      funext j
      by_cases hj : j = j₀
      · subst hj
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ 𝔟 (Finset.mem_univ j),
          Finset.sum_congr rfl fun k hk => h k (by simp) (Finset.ne_of_mem_erase hk)] at hs
        exact add_right_cancel hs
      · exact h j (by simp) hj
    rw [this]
    exact Rel.refl 𝔟
  | insert i S hi ih =>
    intro 𝔞 𝔟 h hs
    by_cases hi₀ : i = j₀
    · exact ih 𝔞 𝔟 (fun j hj hj' => h j (by simp [hj, hi₀, hj']) hj') hs
    have h1 := rel_move (K := K) hi₀ 𝔞 (𝔟 i - 𝔞 i)
    have h2 := ih (𝔞 + Pi.single i (𝔟 i - 𝔞 i) - Pi.single j₀ (𝔟 i - 𝔞 i)) 𝔟 (fun j hj hj' => by
      by_cases hji : j = i
      · subst hji; simp [hj']
      · simpa [hji, hj'] using h j (by simp [hj, hji]) hj') (by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs])
    simpa using h1.trans h2

theorem rel_scale (j₀ : J) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) (β : K)
    (hβ : ∀ P : HeightOneSpectrum R, P.valuation K β = WithZero.exp (-d P)) :
    Rel 𝔞 (𝔞 + Pi.single j₀ d) β := by
  refine ⟨diagonal (Pi.mulSingle j₀ β), by simp [det_diagonal, Finset.prod_pi_mulSingle'], fun x => ?_⟩
  refine forall_congr' fun j => forall_congr' fun P => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [mulVec_diagonal, Pi.mulSingle_eq_same, map_mul, hβ, Pi.add_apply, Pi.single_eq_same, Finsupp.add_apply,
      neg_add, WithZero.exp_add, mul_comm, mul_le_mul_iff_left₀ WithZero.exp_pos]
  · simp [mulVec_diagonal, hj]

open UpperTheory.V.ZK in
theorem SStein_of : UpperTheory.V.ZK.SStein := by
  intro F _ _ J _ 𝔞 𝔟 β hJ hβ
  classical
  have key : Rel (R := 𝓞 F) (K := F) 𝔞 𝔟 (β : F) := by
    rcases isEmpty_or_nonempty J with hE | ⟨⟨j₀⟩⟩
    · have h1 : β = 1 := hJ.resolve_left (not_nonempty_iff.mpr hE)
      rw [h1, Units.val_one, Subsingleton.elim 𝔞 𝔟]
      exact @Rel.refl _ _ _ _ _ _ _ _ _ (_) 𝔟
    · have h1 := rel_scale (K := F) j₀ 𝔞 (∑ j, (𝔟 j - 𝔞 j)) β fun P => by
        have h0 : P.valuation F (β : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr β.ne_zero
        have h2 : (∑ j, (𝔟 j - 𝔞 j)) P = ordP P β := by
          rw [hβ, Finsupp.finsetSum_apply]; rfl
        rw [h2, ordP, neg_neg, WithZero.exp_log h0]
      have h2 := rel_of_sum_eq (K := F) j₀ Finset.univ (𝔞 + Pi.single j₀ (∑ j, (𝔟 j - 𝔞 j))) 𝔟 (by simp)
        (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])
      simpa using h1.trans h2
  obtain ⟨M, hM, h⟩ := key
  have hU : IsUnit M.det := hM ▸ β.isUnit
  refine ⟨Matrix.toLinearEquiv (Pi.basisFun F J) M hU, ?_, fun x => ?_⟩
  · ext
    rw [LinearEquiv.coe_det, ← hM, ← LinearMap.det_toLin (Pi.basisFun F J) M]
    congr 1
  · have : Matrix.toLinearEquiv (Pi.basisFun F J) M hU x = M *ᵥ x := by
      rw [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [this]
    exact h x

end LateralTheory.Q.SSteinT
end
end

