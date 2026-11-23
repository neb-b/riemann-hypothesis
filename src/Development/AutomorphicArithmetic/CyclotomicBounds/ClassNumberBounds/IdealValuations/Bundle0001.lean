module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocDefY
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY
section
open NumberField IsDedekindDomain
open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E] [NumberField E]

private theorem mem_of_adjoin_top {K : Type*} [Field K] [CharZero K] {S : Set K}
    (hS : Algebra.adjoin ℚ S = ⊤) (j : K →+* PadicAlgCl l)
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (h : ∀ s ∈ S, j s ∈ F) (x : K) : j x ∈ F :=
  _root_.UpperTheory.Reformulated.B.Qj1.mem_of_adjoin_top hS j F h x

omit [NumberField E] in
private theorem norm_int_le_one (j : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖j (x : E)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (j (x : E)) := x.isIntegral_coe.map j.toIntAlgHom
  have h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E)) := h1.tower_top
  have h3 := (Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2
  rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

private def indPrime (j : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖j (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one j c) (norm_nonneg _) hx

private theorem mem_indPrime (j : E →+* PadicAlgCl l) (x : 𝓞 E) :
    x ∈ indPrime j ↔ ‖j (x : E)‖ < 1 := Iff.rfl

private theorem indPrime_isPrime (j : E →+* PadicAlgCl l) : (indPrime j).IsPrime := by
  refine ⟨?_, fun {x y} h => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_indPrime]; simp
  · simp only [mem_indPrime, map_mul, norm_mul] at *
    by_contra hc
    push Not at hc
    have := one_le_mul_of_one_le_of_one_le hc.1 hc.2
    linarith

private theorem l_mem_indPrime (j : E →+* PadicAlgCl l) : (l : 𝓞 E) ∈ indPrime j := by
  rw [mem_indPrime]
  have : j ((l : 𝓞 E) : E) = ((l : ℚ_[l]) : PadicAlgCl l) := by
    rw [show ((l : 𝓞 E) : E) = (l : E) from map_natCast (algebraMap (𝓞 E) E) l, map_natCast]
    exact (map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l).symm
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem liesOver_of_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [hP : P.IsPrime] (h : (l : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(l : ℤ)}) := by
  have hl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hl.ne_zero).mpr hl).isMaximal (by simpa using hl.ne_zero)
  refine ⟨hm.eq_of_le (Ideal.comap_isPrime _ _).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

private theorem finiteDimensional_complField (j : E →+* PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (complField j) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have hα' : Algebra.adjoin ℚ {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα]
    rfl
  have h : complField j = IntermediateField.adjoin ℚ_[l] {j α} := by
    apply le_antisymm
    · rw [complField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      refine mem_of_adjoin_top hα' j _ ?_ x
      rintro _ rfl
      exact IntermediateField.mem_adjoin_simple_self _ _
    · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr ⟨α, rfl⟩)
  rw [h]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

theorem exists_embedding_place (v : HeightOneSpectrum (𝓞 E)) (hv : (l : 𝓞 E) ∈ v.asIdeal) :
    ∃ j : E →+* PadicAlgCl l, ∀ x : 𝓞 E, ‖j (x : E)‖ < 1 ↔ x ∈ v.asIdeal := by
  let L := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) :=
    Algebra.IsAlgebraic.trans ℚ E (AlgebraicClosure E)
  have : IsAlgClosure ℚ (AlgebraicClosure E) := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ (AlgebraicClosure E) := IsAlgClosure.isGalois ℚ _
  have : IsGalois ℚ L := IsGalois.normalClosure ℚ E (AlgebraicClosure E)
  have : NumberField L := {}
  let j0 : L →ₐ[ℚ] PadicAlgCl l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have := v.isPrime
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L)
    v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 E) (𝓞 L))).mp
        (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L))]
      exact bot_le)
  have := indPrime_isPrime j0.toRingHom
  have := liesOver_of_mem (l := l) _ (l_mem_indPrime j0.toRingHom)
  have := liesOver_of_mem (l := l) Q (by
    rw [← hQv, Ideal.mem_comap] at hv
    simpa using hv)
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)})
    Q (indPrime j0.toRingHom) Gal(L/ℚ)
  refine ⟨j0.toRingHom.comp ((σ : L →+* L).comp (algebraMap E L)), fun x => ?_⟩
  rw [← hQv, Ideal.mem_comap, ← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, mem_indPrime]
  rfl

private theorem lt_one_iff_of_place (v : HeightOneSpectrum (𝓞 E)) {A B : Type*}
    [NormedField A] [NormedField B] (i : E →+* A) (j : E →+* B)
    (hi1 : ∀ x : 𝓞 E, ‖i (x : E)‖ ≤ 1) (hj1 : ∀ x : 𝓞 E, ‖j (x : E)‖ ≤ 1)
    (hi : ∀ x : 𝓞 E, ‖i (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (hj : ∀ x : 𝓞 E, ‖j (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (x : E) (hx : ‖i x‖ < 1) :
    ‖j x‖ < 1 := by
  obtain ⟨n, ⟨d, hd⟩, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq x
  have hid : ‖i (d : E)‖ = 1 := le_antisymm (hi1 d) (not_lt.mp fun h => hd ((hi d).mp h))
  have hjd : ‖j (d : E)‖ = 1 := le_antisymm (hj1 d) (not_lt.mp fun h => hd ((hj d).mp h))
  rcases h with h | h
  · have h : x * (d : E) = (n : E) := h
    have h1 : ‖i x‖ = ‖i (n : E)‖ := by rw [← h, map_mul, norm_mul, hid, mul_one]
    have h2 : ‖j x‖ = ‖j (n : E)‖ := by rw [← h, map_mul, norm_mul, hjd, mul_one]
    rw [h2, hj, ← hi, ← h1]
    exact hx
  · have h : x * (n : E) = (d : E) := h
    rw [← h, map_mul, norm_mul] at hid
    exact absurd hid (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hi1 n)).ne

omit [NumberField E] in
private theorem eps_delta_of_place {A B : Type*}
    [NormedField A] [NormedField B] (i : E →+* A) (j : E →+* B)
    (h : ∀ x, ‖i x‖ < 1 → ‖j x‖ < 1) (p : E) (hp : p ≠ 0) (hp1 : ‖j p‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : E, dist (i a) (i b) < δ → dist (j a) (j b) < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp
  have hi : 0 < ‖i (p ^ n)‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr hpn)
  have hj : 0 < ‖j (p ^ n)‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hpn)
  refine ⟨_, hi, fun a b hab => ?_⟩
  rw [dist_eq_norm, ← map_sub] at hab ⊢
  have := h ((a - b) / p ^ n) (by rwa [map_div₀, norm_div, div_lt_one hi])
  rw [map_div₀, norm_div, div_lt_one hj, map_pow, norm_pow] at this
  exact this.trans hn

theorem exists_completion_map (v : HeightOneSpectrum (𝓞 E)) (j : E →+* PadicAlgCl l)
    (hj : ∀ x : 𝓞 E, ‖j (x : E)‖ < 1 ↔ x ∈ v.asIdeal) :
    ∃ J : v.adicCompletion E →+* PadicAlgCl l, Continuous J ∧
      (∀ x : E, J (algebraMap E _ x) = j x) ∧ J.fieldRange = (complField j).toSubfield := by
  let i : E →+* v.adicCompletion E := algebraMap E _
  have hi1 : ∀ x : 𝓞 E, ‖i (x : E)‖ ≤ 1 := fun x => FinitePlace.norm_le_one E v x
  have hi : ∀ x : 𝓞 E, ‖i (x : E)‖ < 1 ↔ x ∈ v.asIdeal :=
    fun x => FinitePlace.norm_lt_one_iff_mem E v x
  obtain ⟨p, hpv, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0' : (p : E) ≠ 0 := by exact_mod_cast hp0
  have := finiteDimensional_complField j
  have : CompleteSpace (complField j) := FiniteDimensional.complete ℚ_[l] _
  let f : E →+* complField j :=
    j.codRestrict (complField j) fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  let : NormedField E := NormedField.induced E _ i i.injective
  have hiso : Isometry i := fun _ _ => rfl
  have hf : IsUniformInducing f := by
    rw [Metric.isUniformInducing_iff, Metric.uniformContinuous_iff]
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, h⟩ := eps_delta_of_place i j
        (lt_one_iff_of_place v i j hi1 (norm_int_le_one j) hi hj) p hp0' ((hj p).mpr hpv) ε hε
      exact ⟨δ, hδ, fun {a b} hab => h a b hab⟩
    · intro ε hε
      obtain ⟨δ, hδ, h⟩ := eps_delta_of_place j i
        (lt_one_iff_of_place v j i (norm_int_le_one j) hi1 hj hi) p hp0' ((hi p).mpr hpv) ε hε
      exact ⟨δ, hδ, fun {a b} hab => h a b hab⟩
  have hd : DenseRange i := v.denseRange_algebraMap E
  let J' : v.adicCompletion E →+* complField j :=
    IsDenseInducing.extendRingHom hiso.isUniformInducing hd hf.uniformContinuous
  have hJ' : IsUniformInducing J' :=
    (hiso.isUniformInducing.isDenseInducing hd).isUniformInducing_extend hiso.isUniformInducing hf
  have hJi : ∀ x, J' (i x) = f x := fun x =>
    (hiso.isUniformInducing.isDenseInducing hd).extend_eq hf.uniformContinuous.continuous x
  let J : v.adicCompletion E →+* PadicAlgCl l := (complField j).subtype.comp J'
  have hJ : IsUniformInducing J := isUniformEmbedding_subtype_val.isUniformInducing.comp hJ'
  have hJj : ∀ x : E, J (algebraMap E _ x) = j x := fun x => congrArg Subtype.val (hJi x)
  refine ⟨J, hJ.uniformContinuous.continuous, hJj, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (J' x).2
  · have hcl : IsClosed (J.fieldRange : Set (PadicAlgCl l)) := hJ.isComplete_range.isClosed
    rw [complField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨x, rfl⟩)
    · refine (Padic.denseRange_ratCast l).induction_on q
        (hcl.preimage (continuous_algebraMap _ _)) fun r => ?_
      rw [map_ratCast]
      exact SubfieldClass.ratCast_mem J.fieldRange r
    · exact ⟨_, hJj x⟩

end KStar.IdealValuations
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocRootsY
section
open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable {l : ℕ} [Fact l.Prime]

private noncomputable def lrO (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (Valued.v : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem lr_mem (x : PadicAlgCl l) : x ∈ lrO l ↔ ‖x‖ ≤ 1 := by
  rw [lrO, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl

private theorem lr_max (x : lrO l) :
    x ∈ IsLocalRing.maximalIdeal (lrO l) ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  unfold lrO at x ⊢
  rw [Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe, PadicAlgCl.valuation_coe]
  rfl

private theorem lr_res (x y : lrO l) :
    IsLocalRing.residue (lrO l) x = IsLocalRing.residue (lrO l) y ↔
      ‖(x : PadicAlgCl l) - y‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, lr_max]
  rfl

private theorem lr_char : CharP (IsLocalRing.ResidueField (lrO l)) l := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue (lrO l)), IsLocalRing.residue_eq_zero_iff, lr_max]
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  have h2 : ((l : lrO l) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp
  rw [h2]
  exact h.trans_lt Padic.norm_p_lt_one

private theorem lr_aut (g : Gal(PadicAlgCl l/ℚ_[l])) (x : PadicAlgCl l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

private theorem lr_norm_root {m : ℕ} {ζ : PadicAlgCl l} (hm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ‖ζ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp h1

private theorem lr_field_pow {k : Type*} [Field k] [CharP k l] (φ : k →+* k) {m : ℕ}
    (hm : ¬ l ∣ m) : ∃ j : ℕ, ∀ a : k, a ^ m = 1 → φ a = a ^ l ^ j := by
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hf : m.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)).ne'
  let F : Subfield k := RingHom.eqLocusField (iterateFrobenius k l m.totient) (RingHom.id k)
  have hF : ∀ a, a ∈ F ↔ a ^ l ^ m.totient = a := fun a => Iff.rfl
  have : Finite F := by
    classical
    have hne := FiniteField.X_pow_card_pow_sub_X_ne_zero k hf hl.one_lt
    refine Set.Finite.subset (s := (((Polynomial.X ^ l ^ m.totient - Polynomial.X :
      Polynomial k).roots.toFinset : Finset k) : Set k)) (Finset.finite_toSet _) ?_
    intro a ha
    have ha' := (hF a).mp ha
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hne]
    simp [ha']
  let ψ : F →+* F := φ.restrict F F fun a ha => by
    rw [hF] at ha ⊢
    rw [← map_pow, ha]
  let : Algebra (ZMod l) F := ZMod.algebra _ _
  let ψ' : F →ₐ[ZMod l] F :=
    { ψ with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (ψ.comp (algebraMap _ _))
        (algebraMap (ZMod l) F)) r }
  let e : F ≃ₐ[ZMod l] F :=
    AlgEquiv.ofBijective ψ' (Finite.injective_iff_bijective.mp ψ.injective)
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod l) l F e
  refine ⟨j, fun a ha => ?_⟩
  have haF : a ∈ F := by
    rw [hF]
    have h1 : l ^ m.totient ≡ 1 [MOD m] :=
      Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm)
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.pos)).mp h1.symm
    have h2 : l ^ m.totient = m * c + 1 := by
      have := Nat.one_le_pow m.totient _ hl.pos
      omega
    rw [h2, pow_succ, pow_mul, ha, one_pow, one_mul]
  have h := congrArg Subtype.val (hj ⟨a, haF⟩)
  rw [Nat.card_zmod] at h
  exact h

theorem norm_aut_and_roots :
    (∀ (g : Gal(PadicAlgCl l/ℚ_[l])) (x : PadicAlgCl l), ‖g x‖ = ‖x‖) ∧
      ∀ (m : ℕ) (ζ ζ' : PadicAlgCl l), ¬ l ∣ m → ζ ^ m = 1 → ζ' ^ m = 1 → ‖ζ - ζ'‖ < 1 →
        ζ = ζ' := by
  refine ⟨lr_aut, fun m ζ ζ' hm h h' hlt => ?_⟩
  by_contra hne
  have := lr_char (l := l)
  let a : lrO l := ⟨ζ, (lr_mem _).mpr (lr_norm_root hm h).le⟩
  let b : lrO l := ⟨ζ', (lr_mem _).mpr (lr_norm_root hm h').le⟩
  have hab : a - b ≠ 0 := fun hh => hne (congrArg Subtype.val (sub_eq_zero.mp hh))
  have ha : a ^ m = 1 := Subtype.ext h
  have hb : b ^ m = 1 := Subtype.ext h'
  have h1 := geom_sum₂_mul a b m
  rw [ha, hb, sub_self, mul_eq_zero_iff_right hab] at h1
  have h2 := congrArg (IsLocalRing.residue (lrO l)) h1
  have h3 := (lr_res a b).mpr hlt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_zero, h3] at h2
  rw [geom_sum₂_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hm ((CharP.cast_eq_zero_iff _ l m).mp h2)
  · have h4 := (lr_res b 0).mp (by rw [map_zero]; exact eq_zero_of_pow_eq_zero h2)
    simp only [b, ZeroMemClass.coe_zero, sub_zero, lr_norm_root hm h', lt_irrefl] at h4

theorem exists_pow_of_aut (g : Gal(PadicAlgCl l/ℚ_[l])) {m : ℕ} (hm : ¬ l ∣ m) :
    ∃ j : ℕ, ∀ ζ : PadicAlgCl l, ζ ^ m = 1 → g ζ = ζ ^ l ^ j := by
  have := lr_char (l := l)
  let gO : lrO l →+* lrO l := (g : PadicAlgCl l →+* PadicAlgCl l).restrict (lrO l) (lrO l)
    fun x hx => (lr_mem _).mpr ((lr_aut g x).trans_le ((lr_mem _).mp hx))
  have : IsLocalHom gO := ⟨fun x hx => by
    rw [← IsLocalRing.notMem_maximalIdeal, lr_max] at hx ⊢
    rw [← lr_aut g]
    exact hx⟩
  obtain ⟨j, hj⟩ := lr_field_pow (IsLocalRing.ResidueField.map gO) hm
  refine ⟨j, fun ζ h => ?_⟩
  let a : lrO l := ⟨ζ, (lr_mem _).mpr (lr_norm_root hm h).le⟩
  have ha : a ^ m = 1 := Subtype.ext h
  have h1 := hj (IsLocalRing.residue _ a) (by rw [← map_pow, ha, map_one])
  rw [IsLocalRing.ResidueField.map_residue, ← map_pow, lr_res] at h1
  refine norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, h, map_one]) ?_ h1
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem exists_root_congr {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬ l ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr hx

end KStar.IdealValuations
end

