module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.IsFrobSq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b by ring]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' ha m)) h
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) ih

private theorem isFrob_sq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {q : ℕ} {g : G k Ω} (hg : IsFrob (F := k) A q g) : IsFrob (F := k) A (q ^ 2) (g * g) := by
  refine ⟨Subgroup.mul_mem _ hg.1 hg.1, fun x hx => ?_⟩
  have hgx : A.valuation (g x) ≤ 1 :=
    (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec (F := k) hg.1 x).2 ((A.valuation_le_one_iff _).1 hx))
  have h1 := hg.2 _ hgx
  have h2 := pow_cong A hgx (b := x ^ q) (by rw [map_pow]; exact pow_le_one' hx _) (hg.2 x hx) q
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [sub_add_sub_cancel, ← pow_mul, ← sq] at h3
  rw [AlgEquiv.mul_apply]
  exact h3

theorem UpperTheory.V.Sd.Tw.inert :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
        Module.finrank ℚ K = 2 → ∀ (p : ℕ), p.Prime → ∀ (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
        Ine (F := ℚ) A ≤ galOf ℚ K Ω → ∀ t : G ℚ Ω, IsFrob (F := ℚ) A p t → t ∉ galOf ℚ K Ω →
        ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w ∧ w.asIdeal = Ideal.span {(p : 𝓞 K)} ∧
          ∀ s : G K Ω, galEmb ℚ K Ω s = t * t → IsFrob (F := K) A (normV w) s := by
  intro K Ω _ _ _ _ _ _ hK p hp A hA hI t ht htK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places K Ω p A
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hA
  have hpw : (p : 𝓞 K) ∈ w.asIdeal := (h3 w hw).1 hA
  have hle : Ideal.span {(p : 𝓞 K)} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hpw
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK]
  have hn : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : normV w = p ^ 2 := by
    obtain ⟨j, hj, e⟩ := (Nat.dvd_prime_pow hp).1 (hN ▸ Ideal.absNorm_dvd_absNorm_of_le hle)
    interval_cases j
    · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using e)) w.isPrime.ne_top
    · exfalso
      obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hw
      rw [hn, e, pow_one] at hφ
      have hφ' : IsFrob (F := ℚ) A p (galEmb ℚ K Ω φ) := ⟨hφ.1, hφ.2⟩
      have h := hI (inv_mul_mem_Ine_of_isFrob hφ' ht)
      exact htK (by simpa using (galOf ℚ K Ω).mul_mem (galEmb_mem ℚ K Ω φ) h)
    · rw [hn, e]
  refine ⟨w, hw, ?_, fun s hs => ?_⟩
  · obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
    have e := congrArg Ideal.absNorm hJ
    rw [map_mul, hN, ← hn, hq] at e
    have hJ1 : Ideal.absNorm J = 1 := by
      have := pow_pos hp.pos 2
      exact (Nat.mul_eq_left this.ne').1 e.symm
    rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]
  · have h := isFrob_sq ht
    rw [← hs, ← hq] at h
    exact ⟨h.1, h.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.NotDvdTorsionOrder
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

private theorem all_torsion (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by
  have hc : Fintype.card (InfinitePlace K) = 1 := by
    have := IsTotallyComplex.finrank K
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  haveI : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.1 hc.le
  rw [← Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff]
  funext w
  exact absurd (Subsingleton.elim _ _) w.2

private theorem not_dvd_torsionOrder (K : Type) [Field K] [NumberField K] (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2)
    (hd : ¬ (l : ℤ) ∣ discr K) : ¬ l ∣ Units.torsionOrder K := by
  intro h
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Units.torsion K) l h
  have h1 : IsPrimitiveRoot x l := hx ▸ IsPrimitiveRoot.orderOf x
  have h2 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((x : (𝓞 K)ˣ) : 𝓞 K)) l :=
    (IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.coe_submonoidClass_iff.2 h1)).map_of_injective
      (RingOfIntegers.coe_injective)
  have h3 := h2.intermediateField_adjoin_isCyclotomicExtension ℚ
  refine hd (Dvd.dvd.trans ?_ (discr_dvd_discr (IntermediateField.adjoin ℚ
    {algebraMap (𝓞 K) K ((x : (𝓞 K)ˣ) : 𝓞 K)}) K))
  rw [@IsCyclotomicExtension.Rat.discr_prime l _ _ _ _ (by convert h3 <;> first | rfl | exact Subsingleton.elim _ _)]
  have := hl.two_le
  exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _

private theorem unit_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {N : ℕ} (hN : 3 ≤ N) (u : (𝓞 K)ˣ) (n : ℕ)
    (h : (N : 𝓞 K) ∣ (u : 𝓞 K) - n) : u = 1 ∨ u = -1 := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h2 }
  haveI : IsCMField K := IsCMField.ofCMExtension ℚ K
  have hu := all_torsion K h2 u
  obtain ⟨y, hy⟩ := h
  have hyK : ((u : 𝓞 K) : K) - n = N * (y : K) := by
    simpa using congrArg (algebraMap (𝓞 K) K) hy
  have hc : ((u : 𝓞 K) : K)⁻¹ - n = N * IsCMField.complexConj K (y : K) := by
    have := congrArg (IsCMField.complexConj K) hyK
    rw [map_sub, map_mul, map_natCast, map_natCast] at this
    rw [← this]
    congr 1
    exact (IsCMField.complexConj_torsion K ⟨u, hu⟩).symm
  have hint : IsIntegral ℤ ((y : K) - IsCMField.complexConj K (y : K)) :=
    (y - IsCMField.ringOfIntegersComplexConj K y).isIntegral_coe
  have e : ((u : 𝓞 K) : K) - ((u : 𝓞 K) : K)⁻¹ = N * ((y : K) - IsCMField.complexConj K (y : K)) := by
    linear_combination hyK - hc
  have hlt : ∀ φ : K →+* ℂ, ‖φ ((y : K) - IsCMField.complexConj K (y : K))‖ < 1 := fun φ => by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : ‖φ ((u : 𝓞 K) : K)‖ = 1 := (Units.mem_torsion K).1 hu (InfinitePlace.mk φ)
    have h4 := congrArg (fun t => ‖φ t‖) e
    simp only [map_mul, norm_mul, map_natCast, Complex.norm_natCast] at h4
    have h5 := norm_sub_le (φ ((u : 𝓞 K) : K)) (φ ((u : 𝓞 K) : K))⁻¹
    rw [norm_inv, h1, ← map_inv₀, ← map_sub, h4] at h5
    have := norm_nonneg (φ ((y : K) - IsCMField.complexConj K (y : K)))
    nlinarith
  have h0 : (y : K) - IsCMField.complexConj K (y : K) = 0 := by
    by_contra hb0
    obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hb0 hint fun φ => (hlt φ).le
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hlt φ).ne (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp, map_one]) hn.ne')
  rw [h0, mul_zero, sub_eq_zero, eq_comm, inv_eq_iff_eq_inv, eq_comm, inv_eq_self₀] at e
  rcases e with e | e | e
  · right
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using e
  · exact absurd e (by simp)
  · left
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using e

private theorem int_dvd (K : Type) [Field K] [NumberField K] (N : ℕ) (a : ℤ) (h : (N : 𝓞 K) ∣ (a : 𝓞 K)) :
    (N : ℤ) ∣ a := by
  have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := 𝓞 K) (Ideal.span {(N : ℤ)})
  rw [← Ideal.mem_span_singleton, ← this, Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton]
  simpa using h

theorem UpperTheory.V.Sd.Tw.fin :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (l : ℕ), l.Prime → l ≠ 2 →
        ¬ (l : ℤ) ∣ discr K → ∀ (N : ℕ), 3 ≤ N → ∀ (χ : (ZMod N)ˣ →* ℂˣ), χ ^ 2 = 1 → χ (-1) = -1 → ∀ τ : K →+* ℂ,
        ∃ (e : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ →* ℂˣ) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (∀ x, e x ^ m = 1) ∧
          (∀ u : (𝓞 K)ˣ, ((e (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom u) : ℂˣ) : ℂ) =
            τ ((u : 𝓞 K) : K)) ∧
          ∀ (x : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ) (n : ℕ) (h : n.Coprime N),
            (x : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = (n : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) → e x = χ (ZMod.unitOfCoprime n h) := by
  intro K _ _ _ h2 l hl hl2 hd N hN χ hχ hχ1 τ
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : (N : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  haveI := ringChar.charP (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})
  let j : ZMod N →+* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)} := ZMod.castHom (ringChar.dvd hN0) _
  have hj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at ha
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n N).2 (int_dvd K N n ha)
  let t : (𝓞 K)ˣ →* ℂˣ := Units.map (τ.comp (algebraMap (𝓞 K) K)).toMonoidHom
  obtain ⟨F, hF⟩ := glue ((Units.map j.toMonoidHom).coprod
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom)) (χ.coprod t) (by
      rintro ⟨a, u⟩ h
      have h' : j a * Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u = 1 := congrArg Units.val h
      change χ a * t u = 1
      have h3 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u = j (a⁻¹ : (ZMod N)ˣ) := by
        have : j (a⁻¹ : (ZMod N)ˣ) * j a = 1 := by rw [← map_mul, Units.inv_mul, map_one]
        linear_combination j (a⁻¹ : (ZMod N)ˣ) * h' - Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u * this
      have h4 := h3
      rw [← ZMod.natCast_zmod_val ((a⁻¹ : (ZMod N)ˣ) : ZMod N), map_natCast,
        ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq, Ideal.mem_span_singleton] at h4
      rcases unit_eq K h2 hN u _ h4 with rfl | rfl
      · have : a = 1 := by
          apply Units.ext
          apply hj
          simpa using h'
        rw [this, map_one, map_one, one_mul]
      · have : a = -1 := by
          apply Units.ext
          apply hj
          simpa [neg_eq_iff_eq_neg] using h'
        have ht : t (-1) = -1 := Units.ext (by simp [t])
        rw [this, hχ1, ht]
        simp)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega))
  have hM : Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM l hl.ne_one
  have hw := not_dvd_torsionOrder K l hl hl2 hd
  have hw0 : Units.torsionOrder K ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have hcop : (l ^ s).Coprime (2 * Units.torsionOrder K) := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hl).2 hw))
    exact (Nat.coprime_primes hl Nat.prime_two).2 hl2
  have hk := Nat.ModEq.pow_totient hcop
  have hφ : (2 * Units.torsionOrder K).totient ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  obtain ⟨c, hc⟩ : l ^ s ∣ (l ^ s) ^ (2 * Units.torsionOrder K).totient := dvd_pow_self _ hφ
  have key : ∀ z : ℂˣ, z ^ (2 * Units.torsionOrder K) = 1 →
      z ^ ((l ^ s) ^ (2 * Units.torsionOrder K).totient) = z := fun z hz => by
    rw [pow_eq_pow_of_modEq hk hz, pow_one]
  refine ⟨F ^ ((l ^ s) ^ (2 * Units.torsionOrder K).totient), m, Nat.pos_of_ne_zero (fun h => hm (h ▸ dvd_zero _)),
    hm, fun x => ?_, fun u => ?_, fun x n h hx => ?_⟩
  · rw [MonoidHom.pow_apply, ← pow_mul, hc, mul_right_comm, ← hsm, pow_mul, ← map_pow, pow_card_eq_one', map_one,
      one_pow]
  · have h1 : F (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom u) = t u := by
      simpa using hF (1, u)
    have h3 : u ^ Units.torsionOrder K = 1 := by
      have := all_torsion K h2 u
      rw [← Units.rootsOfUnity_eq_torsion] at this
      exact this
    rw [MonoidHom.pow_apply, h1, key _ (by rw [mul_comm, pow_mul, ← map_pow, h3, map_one, one_pow])]
    rfl
  · have h1 : x = Units.map j.toMonoidHom (ZMod.unitOfCoprime n h) := by
      apply Units.ext
      rw [hx]
      exact (map_natCast j n).symm
    have h3 : F x = χ (ZMod.unitOfCoprime n h) := by
      rw [h1]
      simpa using hF (ZMod.unitOfCoprime n h, 1)
    have h4 : χ (ZMod.unitOfCoprime n h) ^ 2 = 1 := DFunLike.congr_fun hχ _
    rw [MonoidHom.pow_apply, h3, key _ (by rw [pow_mul, h4, one_pow])]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.RedUnique
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

namespace UpperTheory.V.Sd.Tw

variable {K : Type} [Field K] [NumberField K]

private theorem red_field (v : HeightOneSpectrum (𝓞 K)) (a : K) :
    Valued.v (algebraMap K (v.adicCompletion K) a) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem red_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    Valued.v (algebraMap K (v.adicCompletion K) (a : K)) = v.intValuation a := by
  rw [red_field]
  exact v.valuation_of_algebraMap a

private theorem red_nat (v : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    Valued.v (N : v.adicCompletion K) = v.intValuation (N : 𝓞 K) := by
  rw [← red_int]
  congr 1
  have : (((N : 𝓞 K)) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [this, map_natCast]

private theorem red_approx (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    {y : v.adicCompletion K} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 K, Valued.v (y - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n := by
  have h0 : v.intValuation n ≠ 0 := v.intValuation_ne_zero n hn
  have ho : IsOpen {y : v.adicCompletion K | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion K) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have h1 : IsOpen {z : v.adicCompletion K |
      Valued.v ((y - z) * (algebraMap K (v.adicCompletion K) (n : K))⁻¹) < 1} :=
    ho.preimage ((continuous_const.sub continuous_id).mul continuous_const)
  obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open h1
    ⟨y, by simp⟩
  have ht : Valued.v ((y - algebraMap K (v.adicCompletion K) t) *
    (algebraMap K (v.adicCompletion K) (n : K))⁻¹) < 1 := ht
  rw [map_mul, map_inv₀, red_int, mul_inv_lt_iff₀ (zero_lt_iff.2 h0), one_mul] at ht
  have ht1 : v.valuation K t ≤ 1 := by
    rw [← red_field, ← sub_sub_cancel y (algebraMap K (v.adicCompletion K) t)]
    exact Valuation.map_sub_le _ hy (ht.le.trans (v.intValuation_le_one n))
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer ht1 (Units.mk0 _ h0)
  refine ⟨a, ?_⟩
  have e : y - algebraMap K (v.adicCompletion K) (a : K) =
      (y - algebraMap K (v.adicCompletion K) t) -
        algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a - t) := by
    rw [map_sub]; ring
  rw [e]
  refine Valuation.map_sub_le _ ht.le ?_
  rw [red_field]
  exact ha.le

private theorem red_exists {n : 𝓞 K} (hn : n ≠ 0)
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    ∃ a : 𝓞 K, ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n := by
  classical
  have hS : {v : HeightOneSpectrum (𝓞 K) | n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (I := Ideal.span {n}) (by simpa using hn)
    simpa only [Ideal.dvd_span_singleton] using this
  choose f hf using fun v : HeightOneSpectrum (𝓞 K) => red_approx v hn (hy v)
  have he : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : ℕ, v.intValuation n = WithZero.exp (-(e : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hn⟩
  choose e he using he
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hS.toFinset)
    (fun v => v.asIdeal) e (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun v => f v.1)
  refine ⟨a, fun v hv => ?_⟩
  have h1 := ha v (hS.mem_toFinset.2 hv)
  rw [← v.intValuation_le_pow_iff_mem, ← he, ← red_int] at h1
  have e1 : y v - algebraMap K (v.adicCompletion K) (a : K) =
      (y v - algebraMap K (v.adicCompletion K) (f v : K)) -
        algebraMap K (v.adicCompletion K) ((a - f v : 𝓞 K) : K) := by
    have : ((a - f v : 𝓞 K) : K) = (a : K) - (f v : K) := map_sub (algebraMap (𝓞 K) K) _ _
    rw [this, map_sub]; ring
  rw [e1]
  exact Valuation.map_sub_le _ (hf v) h1

private theorem red_unique {n : 𝓞 K} (hn : n ≠ 0)
    (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) {a b : 𝓞 K}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (a : K)) ≤ v.intValuation n)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), n ∈ v.asIdeal →
      Valued.v (y v - algebraMap K (v.adicCompletion K) (b : K)) ≤ v.intValuation n) :
    Ideal.Quotient.mk (Ideal.span {n}) a = Ideal.Quotient.mk (Ideal.span {n}) b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hle : ∀ v : HeightOneSpectrum (𝓞 K), v.intValuation (a - b) ≤ v.intValuation n := by
    intro v
    by_cases hv : n ∈ v.asIdeal
    · have := Valuation.map_sub_le _ (hb v hv) (ha v hv)
      rw [sub_sub_sub_cancel_left, ← map_sub] at this
      have e : ((a - b : 𝓞 K) : K) = (a : K) - (b : K) := map_sub (algebraMap (𝓞 K) K) _ _
      rwa [← e, red_int] at this
    · rw [v.intValuation_eq_one_iff.2 hv]
      exact v.intValuation_le_one _
  have hn' : algebraMap (𝓞 K) K n ≠ 0 := by simpa using hn
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
    (algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K n) (fun v => by
      rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      exact div_le_one_of_le₀ (hle v) zero_le)
  refine ⟨c, IsFractionRing.injective (𝓞 K) K ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ hn']

end UpperTheory.V.Sd.Tw

theorem UpperTheory.V.Sd.Tw.red :
    ∀ (K : Type) [Field K] [NumberField K] (N : ℕ), N ≠ 0 →
        ∃ red : ↥(GlobalTheory.Mem.Chr.unitIdl K) →* (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ,
          ∀ (a : ↥(GlobalTheory.Mem.Chr.unitIdl K)) (r : 𝓞 K),
            (∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal →
              Valued.v (((a : Ideles K) : AdeleRing (𝓞 K) K).2 v - algebraMap K (v.adicCompletion K) (r : K)) ≤
                Valued.v (N : v.adicCompletion K)) →
            ((red a : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ) : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = Ideal.Quotient.mk _ r := by
  intro K _ _ N hN
  have hn : (N : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hN
  choose f hf using fun a : GlobalTheory.Mem.Chr.unitIdl K =>
    red_exists hn (fun v => ((a : Ideles K) : AdeleRing (𝓞 K) K).2 v) (fun v => (a.2 v).le)
  let φ : GlobalTheory.Mem.Chr.unitIdl K →* (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) :=
    { toFun := fun a => Ideal.Quotient.mk _ (f a)
      map_one' := by
        rw [← map_one (Ideal.Quotient.mk _)]
        refine red_unique hn _ (hf 1) fun v _ => ?_
        show Valued.v ((1 : v.adicCompletion K) - _) ≤ _
        simp
      map_mul' := fun a b => by
        rw [← map_mul]
        refine red_unique hn _ (hf (a * b)) fun v hv => ?_
        show Valued.v (((a : Ideles K) : AdeleRing (𝓞 K) K).2 v *
          ((b : Ideles K) : AdeleRing (𝓞 K) K).2 v - _) ≤ _
        have e0 : ((f a * f b : 𝓞 K) : K) = (f a : K) * (f b : K) := map_mul (algebraMap (𝓞 K) K) _ _
        have e1 : ∀ x y p q : v.adicCompletion K, x * y - p * q = x * (y - q) + q * (x - p) :=
          fun x y p q => by ring
        rw [e0, map_mul, e1]
        refine Valuation.map_add_le _ ?_ ?_
        · rw [map_mul, a.2 v, one_mul]
          exact hf b v hv
        · rw [map_mul, red_int]
          exact (mul_le_of_le_one_left' (v.intValuation_le_one _)).trans (hf a v hv) }
  refine ⟨φ.toHomUnits, fun a r h => ?_⟩
  show Ideal.Quotient.mk _ (f a) = _
  exact red_unique hn _ (hf a) fun v hv => by rw [← red_nat]; exact h v hv
end

