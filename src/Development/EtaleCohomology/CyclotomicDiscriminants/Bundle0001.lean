module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317

@[expose] public section

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SChainPf
section
noncomputable section
open UpperTheory.V.ZK

namespace LateralTheory.Q.SChainPf

variable {A : Type} [CommRing A]

lemma bd_single {G : Type} [Group G] (m : ℕ) (g : Fin (m + 1) → G) (a : A) :
    bd A G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  simp only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma bd_eq {G : Type} [Group G] (m : ℕ) :
    bd A G m = (groupHomology.inhomogeneousChains.d (Rep.trivial A G A) m).hom := by
  refine Finsupp.lhom_ext fun g a => ?_
  rw [bd_single, groupHomology.inhomogeneousChains.d_single]
  simp

lemma bd_bd {G : Type} [Group G] (m : ℕ) (z : Ch A G (m + 2)) : bd A G m (bd A G (m + 1) z) = 0 := by
  rw [bd_eq, bd_eq]
  have h := groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m
  have := congrArg (fun φ => φ.hom z) h
  simpa using this

lemma cm_single {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (g : Fin m → G) (a : A) :
    cm A f m (Finsupp.single g a) = Finsupp.single (fun i => f (g i)) a := by
  simp [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma contract_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (j : Fin (m + 1))
    (g : Fin (m + 1) → G) :
    (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) := by
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp [map_mul]

lemma bd_cm {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)) :
    bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z) := by
  have : (bd A H m).comp (cm A f (m + 1)) = (cm A f m).comp (bd A G m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, cm_single, bd_single, map_add (f := _), map_sum, map_smul]
    simp only [contract_map]
  exact LinearMap.congr_fun this z

lemma cm_comp {G H K : Type} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ)
    (z : Ch A G m) : cm A (g.comp f) m z = cm A g m (cm A f m z) := by
  have : cm A (g.comp f) m = (cm A g m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun x a => ?_
    simp [cm_single]
  exact LinearMap.congr_fun this z

lemma prism_single {G : Type} [Group G] (k : G) (m : ℕ) (g : Fin m → G) (a : A) :
    prism A k m (Finsupp.single g a) = ∑ i : Fin (m + 1), ((-1 : A) ^ (i : ℕ)) •
      Finsupp.single (Fin.insertNth (α := fun _ => G) i k
        fun j => if (j : ℕ) < i then g j else k⁻¹ * g j * k) a := by
  simp only [prism, Finsupp.linearCombination_single, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma insert_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (h : Fin m → G) :
    (fun j => f (Fin.insertNth (α := fun _ => G) i k h j)) =
      Fin.insertNth (α := fun _ => H) i (f k) (fun j => f (h j)) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun j => ?_) j <;> simp

lemma conj_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (g : Fin m → G) :
    (fun j : Fin m => f (if (j : ℕ) < i then g j else k⁻¹ * g j * k)) =
      fun j : Fin m => if (j : ℕ) < i then f (g j) else (f k)⁻¹ * f (g j) * f k := by
  funext j
  split_ifs <;> simp [map_mul, map_inv]

lemma cm_prism {G H : Type} [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m) :
    cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z) := by
  have : (cm A f (m + 1)).comp (prism A k m) = (prism A (f k) m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, cm_single, prism_single, map_sum, map_smul]
    simp only [insert_map, conj_map]
  exact LinearMap.congr_fun this z

def S (n : ℕ) : A := ∑ j : Fin n, (-1 : A) ^ ((j : ℕ) + 1)

lemma S_pair (n : ℕ) : (S n : A) + S (n + 1) = -1 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have h2 : (S (n + 2) : A) = S n := by
      simp only [S, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      ring
    rw [h2, add_comm]; exact ih

lemma bd_single_triv {G : Type} [Group G] [Subsingleton G] (m : ℕ) (g : Fin (m + 1) → G)
    (h : Fin m → G) (a : A) : bd A G m (Finsupp.single g a) = Finsupp.single h ((1 + S (m + 1)) * a) := by
  rw [bd_single]
  have e1 : (fun i => g i.succ) = h := Subsingleton.elim _ _
  have e2 : ∀ j : Fin (m + 1), Fin.contractNth j (· * ·) g = h := fun _ => Subsingleton.elim _ _
  simp only [e1, e2, Finsupp.smul_single, smul_eq_mul, ← Finsupp.single_finsetSum, ← Finsupp.single_add,
    S, add_mul, Finset.sum_mul, one_mul]

lemma triv_bd {G : Type} [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  let g1 : Fin (m + 1) → G := fun _ => 1
  let g0 : Fin m → G := fun _ => 1
  let g2 : Fin (m + 2) → G := fun _ => 1
  have hz1 : z = Finsupp.single g1 (z g1) := by
    ext x; rw [Subsingleton.elim x g1]; simp
  generalize z g1 = c at hz1
  subst hz1
  have hc : (1 + S (m + 1)) * c = 0 := by
    have := hz
    unfold Cyc at this
    rw [bd_single_triv m g1 g0] at this
    simpa using congrArg (fun w => w g0) this
  refine ⟨Finsupp.single g2 (c), ?_⟩
  rw [bd_single_triv (m + 1) g2 g1]
  congr 1
  have := S_pair (A := A) (m + 1)
  linear_combination (-1 : A) * hc + (c) * this

theorem SChain_of : UpperTheory.V.ZK.SChain :=
  fun _ _ => ⟨fun _ _ m z => bd_bd m z, fun _ _ _ _ f m z => bd_cm f m z,
    fun _ _ _ _ _ _ f g m z => cm_comp f g m z, fun _ _ _ _ f k m z => cm_prism f k m z,
    fun _ _ _ m z hz => triv_bd m z hz⟩

end LateralTheory.Q.SChainPf
end
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SDetectCut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.ZK

namespace LateralTheory.Q.SDetectCut

theorem root_eq_one {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) (q : ℕ) (η : R) (hη : η ^ q = 1)
    (h1 : η - 1 ∈ P) (hq : (q : R) ∉ P) : η = 1 := by
  by_contra hne
  apply hq
  have h0 : ∑ i ∈ Finset.range q, η ^ i = 0 := by
    have := mul_geom_sum η q
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h2 : Ideal.Quotient.mk P η = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact h1
  have h3 := congrArg (Ideal.Quotient.mk P) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, h2, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    map_zero] at h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h3

theorem surj_of_prime {A k : Type} [CommRing A] [CommRing k] (f : A →+* k) (hp : (Nat.card k).Prime) :
    Function.Surjective f := by
  intro y
  have : Fact (Nat.card k).Prime := ⟨hp⟩
  have : Finite k := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial k := Finite.one_lt_card_iff_nontrivial.1 hp.one_lt
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := k) (p := Nat.card k) rfl (g := 1) (g' := y) one_ne_zero
  exact ⟨n, by simpa using hn⟩

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem val_le (B : ValuationSubring Ω) (x : 𝓞 F) : B.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hz : IsIntegral ℤ (algebraMap F Ω (x : F)) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
  exact (Valuation.integer.integers B.valuation).mem_of_integral hz.tower_top


omit [NumberField F] in
theorem frob_fix {v : HeightOneSpectrum (𝓞 F)} {B : ValuationSubring Ω} (hB : IsPlaceOver B v) {N : ℕ} (hN : N ≠ 0)
    {σ : G F Ω} (hσ : IsFrob B N σ) {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 F) ∉ v.asIdeal) {ζ : 𝓞 F}
    (hζ : IsPrimitiveRoot ζ q) {β : F} {x : Ω} (hx : x ^ q = algebraMap F Ω β) {a b t : 𝓞 F}
    (hb : b ∉ v.asIdeal) (ht : t ∉ v.asIdeal) (hab : β * b = a) (hc : a - t ^ q * b ∈ v.asIdeal) : σ x = x := by
  have : NeZero q := ⟨hq0⟩
  let ι : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, ι y = algebraMap F Ω (y : F) := fun _ => rfl
  have hinj : Function.Injective ι := (algebraMap F Ω).injective.comp (RingOfIntegers.coe_injective)
  have hone : ∀ y : 𝓞 F, y ∉ v.asIdeal → B.valuation (ι y) = 1 := fun y hy =>
    le_antisymm (val_le B y) (not_lt.1 fun h => hy ((hB y).1 h))
  have hζ' : IsPrimitiveRoot (ι ζ) q := hζ.map_of_injective hinj
  have h1 : B.valuation (x ^ q - ι t ^ q) < 1 := by
    have e : (x ^ q - ι t ^ q) * ι b = ι (a - t ^ q * b) := by
      rw [hx, map_sub, map_mul, map_pow, sub_mul, hι a, hι b, ← hab, map_mul]
    have := (hB _).2 hc
    rw [← hι, ← e, map_mul, hone b hb, mul_one] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i : ℕ, B.valuation (x - ι (ζ ^ i * t)) < 1 := by
    by_contra! h
    have e := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ' (Nat.pos_of_ne_zero hq0) (rfl : ι t ^ q = ι t ^ q))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod] at e
    rw [e, map_prod] at h1
    refine absurd h1 (not_lt.2 (Finset.one_le_prod' fun i _ => ?_))
    have := h i
    rwa [map_mul, map_pow] at this
  set c := ζ ^ i * t with hcdef
  have hcv : c ∉ v.asIdeal := fun h =>
    ht ((v.isPrime.mem_or_mem h).resolve_left fun h' =>
      v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' ((hζ.isUnit hq0).pow i)))
  have hxv : B.valuation x = 1 := by
    rw [← hone c hcv]
    exact Valuation.map_eq_of_sub_lt _ (by rw [hone c hcv]; exact hi)
  have h2 : B.valuation (σ (x - ι c)) < 1 := by
    have e : σ (x - ι c) = (σ (x - ι c) - (x - ι c) ^ N) + (x - ι c) ^ N := by ring
    rw [e]
    refine Valuation.map_add_lt _ (hσ.2 _ hi.le) ?_
    rw [map_pow]
    exact pow_lt_one' hi hN
  have h3 : B.valuation (σ x - x) < 1 := by
    have e : σ x - x = σ (x - ι c) - (x - ι c) := by
      rw [map_sub, hι, AlgEquiv.commutes]; ring
    rw [e]
    exact Valuation.map_sub_lt _ h2 hi
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxv
  have h4 : (σ x / x) ^ q = 1 := by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ hx0)]
  obtain ⟨j, -, hj⟩ := hζ'.eq_pow_of_pow_eq_one h4
  have h5 : σ x = ι (ζ ^ j) * x := by rw [map_pow, hj, div_mul_cancel₀ _ hx0]
  have h6 : ζ ^ j - 1 ∈ v.asIdeal := by
    rw [← hB, ← hι]
    have e : σ x - x = ι (ζ ^ j - 1) * x := by rw [h5, map_sub, map_one]; ring
    rwa [e, map_mul, hxv, mul_one] at h3
  have h7 : ζ ^ j = 1 := root_eq_one v.asIdeal q _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h6 hq
  rw [h5, h7, map_one, one_mul]

theorem goal : SDetect := by
  intro L F _ _ _ _ _ l ν hl ζ hζ β b hb H
  have hq0 : l ^ ν ≠ 0 := pow_ne_zero _ hl.ne_zero
  generalize l ^ ν = q at *
  let Ω := AlgebraicClosure F
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (β : F)) (Nat.pos_of_ne_zero hq0)
  have hS : {v : HeightOneSpectrum (𝓞 F) | b * (q : 𝓞 F) ∈ v.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors (by simp [hb, hq0])
  have : IsGalois F Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, g x = x := by
    intro g
    have hV : IsOpen {σ : G F Ω | σ x = g x} := by
      have h1 : IsOpen (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := stabilizer_isOpen_of_isIntegral x
      have h2 := h1.preimage (continuous_const_mul g⁻¹)
      convert h2 using 1
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        inv_smul_eq_iff]
      rfl
    obtain ⟨σ, hσV, v, hv, hd, B, hB, hσ⟩ :=
      (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
        hS).inter_open_nonempty _ hV ⟨g, rfl⟩
    have hp : (Nat.card (𝓞 F ⧸ v.asIdeal)).Prime := by
      have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    have := v.isMaximal
    obtain ⟨s, a, b', hb', hab, hr⟩ := H v (fun h => hv (Ideal.mul_mem_right _ _ h)) (surj_of_prime _ hp)
    let := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : 𝓞 F ⧸ v.asIdeal)
    rw [← hσV]
    refine frob_fix hB hp.ne_zero hσ hq0 (fun h => hv (Ideal.mul_mem_left _ _ h))
      (IsPrimitiveRoot.coe_units_iff.2 hζ) hx (a := a) (b := b') (t := t)
      (fun h => hb' (Ideal.Quotient.eq_zero_iff_mem.2 h))
      (fun h => s.ne_zero (ht ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)) hab ?_
    rw [← Ideal.Quotient.eq, map_mul, map_pow, ht, hr, Units.val_pow_eq_pow_val]
  obtain ⟨δ, hδ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hd : (β : F) = δ ^ q := (algebraMap F Ω).injective (by rw [map_pow, hδ, hx])
  have h0 : δ ≠ 0 := by
    rintro rfl
    exact β.ne_zero (by rw [hd, zero_pow hq0])
  exact ⟨Units.mk0 δ h0, Units.ext (by simpa using hd)⟩

end LateralTheory.Q.SDetectCut
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SZcTPf
section
noncomputable section

namespace LateralTheory.Q.SZcT

open UpperTheory.V.ZK

def wd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

theorem zc_eq (q : ℕ) [NeZero q] (e : ℕ) :
    zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (wd e j) 1 := rfl

theorem alt_range {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (T : ℕ → M) (n : ℕ)
    (h : ∀ a, a < n → T (2 * a) = T (2 * a + 1)) :
    ∑ p ∈ Finset.range (2 * n), ((-1 : A) ^ (p + 1)) • T p = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih fun a ha => h a (by omega), ← h n (by omega), pow_succ (-1 : A) (2 * n + 1)]
    simp

theorem alt_fin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (e : ℕ) (S : Fin (2 * e + 1 + 1) → M)
    (h : ∀ (a : ℕ) (ha : a < e + 1), S ⟨2 * a, by omega⟩ = S ⟨2 * a + 1, by omega⟩) :
    ∑ p : Fin (2 * e + 1 + 1), ((-1 : A) ^ ((p : ℕ) + 1)) • S p = 0 := by
  have key := alt_range (A := A) (fun p => if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0) (e + 1) (by
    intro a ha
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact h a ha)
  rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ← Fin.sum_univ_eq_sum_range
    (fun p => ((-1 : A) ^ (p + 1)) • (if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0))] at key
  rw [← key]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dite_eq_left p.2]

theorem wd_even {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1)) (k : Fin (e + 1))
    (h : (i : ℕ) = 2 * k) : wd e j i = Multiplicative.ofAdd (j k) := by
  unfold wd
  rw [if_pos (by omega)]
  congr 2
  ext
  show (i : ℕ) / 2 = k
  omega

theorem wd_odd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : (i : ℕ) % 2 = 1) : wd e j i = Multiplicative.ofAdd 1 := by
  unfold wd
  rw [if_neg (by omega)]

theorem wd_congr {q : ℕ} (e : ℕ) (j j' : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : ∀ k : Fin (e + 1), (i : ℕ) = 2 * k → j k = j' k) : wd e j i = wd e j' i := by
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have hk : (i : ℕ) = 2 * ((⟨i / 2, by omega⟩ : Fin (e + 1)) : ℕ) := by
      show (i : ℕ) = 2 * (i / 2)
      omega
    rw [wd_even e j i _ hk, wd_even e j' i _ hk, h _ hk]
  · rw [wd_odd e j i hi, wd_odd e j' i hi]

theorem tail_sum (q : ℕ) [NeZero q] (e : ℕ) :
    (∑ j : Fin (e + 1) → ZMod q, Finsupp.single (fun i : Fin (2 * e + 1) => wd e j i.succ) 1 :
      Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : ∀ x : ZMod q, (fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (x, j)) i.succ) =
      fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (0, j)) i.succ := by
    intro x
    funext i
    refine wd_congr e _ _ _ fun k hk => ?_
    induction k using Fin.cases with
    | zero => simp at hk
    | succ k => simp [Fin.consEquiv]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, Finsupp.smul_single]
  simp

def sh (q e a : ℕ) : Fin (e + 1) → ZMod q := fun k => if (k : ℕ) = a then 1 else if (k : ℕ) = a + 1 then -1 else 0

theorem contract_eq {q : ℕ} (e a : ℕ) (ha : a < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * a, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e j) =
      Fin.contractNth (⟨2 * a + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e (j + sh q e a)) := by
  funext i
  have hi := i.2
  rcases lt_trichotomy (i : ℕ) (2 * a) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega)]
    refine wd_congr e _ _ _ fun k hk => ?_
    rw [Fin.val_castSucc] at hk
    rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega),
      wd_even e j i.castSucc ⟨a, ha⟩ h, wd_even e _ i.castSucc ⟨a, ha⟩ h,
      wd_odd e j i.succ (by rw [Fin.val_succ]; omega), Pi.add_apply, sh, if_pos rfl, ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases (show (i : ℕ) = 2 * a + 1 ∨ 2 * a + 1 < i by omega) with h' | h'
    · have hk : ((i.succ : Fin (2 * e + 1 + 1)) : ℕ) = 2 * ((⟨a + 1, by omega⟩ : Fin (e + 1)) : ℕ) := by
        rw [Fin.val_succ]
        show (i : ℕ) + 1 = 2 * (a + 1)
        omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h', wd_even e j _ _ hk, wd_even e _ _ _ hk,
        wd_odd e _ i.castSucc (by rw [Fin.val_castSucc]; omega), Pi.add_apply, sh, if_neg (by simp), if_pos rfl,
        ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      refine wd_congr e _ _ _ fun k hk => ?_
      rw [Fin.val_succ] at hk
      rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]

theorem SZc_of : SZc := by
  intro q _ e
  unfold Cyc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [zc_eq, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, tail_sum, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  refine alt_fin (A := ZMod q) e (fun p => ∑ j : Fin (e + 1) → ZMod q,
    (Finsupp.single (Fin.contractNth p (· * ·) (wd e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))) fun a ha => ?_
  refine Fintype.sum_equiv (Equiv.addRight (sh q e a)) _ _ fun j => ?_
  rw [contract_eq e a ha j]
  rfl

end LateralTheory.Q.SZcT

end
end

