module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AutomorphicArithmetic.WeightCongruences.ExistsUnitEqRootOfUnityMulConjPhaseOne
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.MuZero

theorem exists_residue_char {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = ω (-1) ∧ ∀ (a : ℕ) (ha : a.Coprime p),
      ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ, (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧
        θ b = ω (ZMod.unitOfCoprime a ha) := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), ?_, fun a ha => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp
  · refine ⟨Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) (ZMod.unitOfCoprime a ha), ?_, ?_⟩
    · simp
    · rw [MonoidHom.comp_apply]
      congr 1
      ext
      simp

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem eq_of_overP {k k' : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (h : Formalism.L2.Host.OverP H (H.g k) w)
    (h' : Formalism.L2.Host.OverP H (H.g k') w) : k = k' := by
  by_contra hne
  have hg : H.g k ≠ H.g k' := by
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hne
    · exact H.g_ne
    · exact H.g_ne.symm
    · exact absurd rfl hne
  have hc : IsCoprime ((H.g k : ℕ) : 𝓞 H.E) ((H.g k' : ℕ) : 𝓞 H.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (H.g_prime k) (H.g_prime k')).2 hg)
  obtain ⟨s, t, hst⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ h')


open Classical in
theorem exists_unitary_mu_zero_characters_of_split_type_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : Formalism.L2.Host.PiBar H) (W : Formalism.L2.Host.Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (Formalism.L2.Host.embPsi H) e → Formalism.L2.Host.Mu0Exists P W e j := by
  intro R H P W e j hs hint hev
  choose z hz using hint
  have hmu : UpperTheory.MU (Formalism.L2.Host.embPsi H) z := hev.mu hz
  haveI := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := fun k => _root_.GlobalTheory.Mem.Chr.splitsC_main R H (H.g k) (H.g_prime k) (hs k)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = 1 ∧
      ∀ k, P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)),
        ∃ b : (𝓞 H.E ⧸ w.asIdeal)ˣ, (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) ∧
          θ b = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
    intro w
    by_cases h : ∃ k, P.Div k w
    · obtain ⟨k, hk⟩ := h
      obtain ⟨θ, h1, h2⟩ := exists_residue_char w (H.g_prime k) (hsp k w (P.overP hk)).1
        ((W.om k ^ (2 * (j + 1)))⁻¹)
      refine ⟨θ, ?_, fun k' hk' => ?_⟩
      · rw [h1, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_mul, ← map_pow, neg_one_sq, map_one, one_pow, inv_one]
      · obtain rfl := eq_of_overP (P.overP hk) (P.overP hk')
        exact h2
    · exact ⟨1, rfl, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := Finset.univ.biUnion fun k => Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k)
  have hS : ∀ w, w ∈ S ↔ ∃ k, P.Div k w := fun w => by
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hmem : ∀ k w, w ∈ Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k) ↔ P.Div k w := fun k w => by
    simp only [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hres : ∀ (k : Fin 2) (ζ : (𝓞 H.E)ˣ), (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 H.E) : H.E) ^ m = 1) →
      ∏ w ∈ Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k), θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 :=
    fun k ζ hζ => UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E (H.g k) (H.g_prime k) (P.pb k) _ (fun w => hmem k w)
      (fun w hw => ⟨(hsp k w (P.overP ((hmem k w).1 hw))).1, (hsp k w (P.overP ((hmem k w).1 hw))).2.1⟩)
      ((W.om k ^ (2 * (j + 1)))⁻¹) θ (fun w hw a ha => hθ2 w k ((hmem k w).1 hw) a ha) ζ (H.der.norm_mu _ hζ)
  have hdisj : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)).PairwiseDisjoint
      (fun k => Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k)) := by
    intro k _ k' _ hkk'
    refine Finset.disjoint_left.2 fun w hw hw' => hkk' ?_
    exact eq_of_overP (P.overP ((hmem k w).1 hw)) (P.overP ((hmem k' w).1 hw'))
  obtain ⟨χ, hu, ht, hi, htame, hunr, hloc, -⟩ := GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm z S θ
    (by
      intro w hw w' hcj hw'
      obtain ⟨k, hk⟩ := (hS w).1 hw
      obtain ⟨k', hk'⟩ := (hS w').1 hw'
      rw [hce] at hcj
      obtain ⟨ho, hiff⟩ := (hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) w' hcj
      obtain rfl := eq_of_overP ho (P.overP hk')
      exact hiff.1 hk hk')
    (by
      intro ζ hζ
      have hinf : ∏ i, Formalism.L2.Host.embPsi H i ((ζ : 𝓞 H.E) : H.E) ^ (-z i) = 1 := hmu.neg _ hζ
      have hfin : ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
        rw [Finset.prod_biUnion hdisj]
        exact Finset.prod_eq_one fun k _ => hres k ζ hζ
      rw [hinf, one_mul, ← Units.coe_prod]
      exact (congrArg Units.val hfin).trans Units.val_one)
  refine ⟨χ, hu, ht, ⟨_, fun τ => ?_, hi⟩, fun v hv => hunr v ?_ ?_, htame, fun k w hw a ha x hx => ?_⟩
  · show _ = 2 * -e τ
    rw [hz τ]
    push_cast
    ring
  · intro h
    obtain ⟨k, hk⟩ := (hS v).1 h
    exact hv k (P.overP hk)
  · intro w hw hcj
    obtain ⟨k, hk⟩ := (hS w).1 hw
    rw [hce] at hcj
    exact hv k ((hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) v hcj).1
  · obtain ⟨b, hb, hb'⟩ := hθ2 w k hw a ha
    rw [← hb']
    exact hloc w ((hS w).2 ⟨k, hw⟩) x (a : 𝓞 H.E) b (by rw [hx]; simp) hb

end GlobalTheory.Mem.MuZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.DeltaZero

theorem exists_char_of_dvd {G : Type} [Group G] [IsCyclic G] {m : ℕ} (hm : m ≠ 0) (h : m ∣ Nat.card G) :
    ∃ θ : G →* ℂˣ, ∀ n : ℕ, θ ^ n = 1 ↔ m ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hζ' := hζ.isUnit_unit hm
  set ζ : ℂˣ := (hζ.isUnit hm).unit
  have ho : orderOf ζ ∣ orderOf g := by
    rw [← hζ'.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun n => ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator hg, MonoidHom.pow_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.one_apply]
  exact hζ'.pow_eq_one_iff_dvd n

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ Q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using hu
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

private theorem exists_residue_read {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, (∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 L ⧸ w.asIdeal)ˣ),
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      ∀ n : ℕ, θ ^ n = 1 ↔ ω ^ n = 1 := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), fun a ha b hb => ?_, fun n => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp [hb]
  · constructor
    · intro h
      ext u
      have := congrArg (fun f => f (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u)) h
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      have e : Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p) (Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) u) = u := by
        ext; simp
      rw [e] at this
      simp [MonoidHom.pow_apply, this]
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h, MonoidHom.one_apply,
        MonoidHom.one_apply]


open Classical in
theorem delta_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → Formalism.L2.Host.DeltaExists (H := H) p := by
  intro R H p hp h15 hs
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs
  obtain ⟨Q, hQ⟩ := exists_place_over H.K hp
  have : Fact p.Prime := ⟨hp⟩
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨ω, hω⟩ := exists_char_of_dvd (G := (ZMod p)ˣ) (m := 15) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ,
      (Formalism.L2.Host.OverP H p w → ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ b = ω (ZMod.unitOfCoprime a ha)) ∧
      (Formalism.L2.Host.OverP H p w → ∀ n : ℕ, θ ^ n = 1 ↔ 15 ∣ n) := by
    intro w
    by_cases h : Formalism.L2.Host.OverP H p w
    · obtain ⟨θ, h1, h2⟩ := exists_residue_read w hp (hsp w h).1 ω
      exact ⟨θ, fun _ => h1, fun _ n => (h2 n).trans (hω n)⟩
    · exact ⟨1, fun h' => absurd h' h, fun h' => absurd h' h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := Formalism.L2.Host.aboveF (L := H.E) H.K Q
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 H.K) = Q := fun w => by
    simp only [S, Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]
    rfl
  have hov : ∀ w ∈ S, Formalism.L2.Host.OverP H p w := fun w hw => by
    have h1 := hQ
    rw [← (hS w).1 hw] at h1
    have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((p : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
    rwa [map_natCast] at h2
  have hres := UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q S hS (fun w hw => ⟨(hsp w (hov w hw)).1, (hsp w (hov w hw)).2.1⟩) ω θ
    (by
      intro w hw a ha
      have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
        obtain ⟨s, t, hst⟩ : IsCoprime ((a : ℕ) : 𝓞 H.E) ((p : ℕ) : 𝓞 H.E) := Nat.Coprime.cast ha
        have h0 : Ideal.Quotient.mk w.asIdeal ((p : ℕ) : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hov w hw)
        have h1 := congrArg (Ideal.Quotient.mk w.asIdeal) hst
        rw [map_add (f := _), map_mul, map_mul, h0, mul_zero, add_zero, map_one] at h1
        exact IsUnit.of_mul_eq_one_right _ h1
      exact ⟨hu.unit, hu.unit_spec, hθ1 w (hov w hw) a ha _ hu.unit_spec⟩)
  obtain ⟨χ, -, ht, hi, htame, hunr, -, hord⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm (fun _ => 0) S θ
    (by
      intro w hw w' hcj hw'
      rw [hce] at hcj
      exact ((hsp w (hov w hw)).2.2.2 Q hQ w' hcj).2.1 ((hS w).1 hw) ((hS w').1 hw'))
    (by
      intro ζ hζ
      have h1 := hres ζ (H.der.norm_mu _ hζ)
      have h2 : ∏ w ∈ S, ((θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
        rw [← Units.coe_prod]
        exact congrArg Units.val h1 |>.trans Units.val_one
      rw [h2]
      simp)
  refine ⟨χ, GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity H.E χ fun k => ?_, ht, htame, fun v hv => hunr v (fun h => hv (hov v h)) ?_,
    fun v hv n => ?_⟩
  · apply Units.ext
    rw [hi k]
    simp
  · intro w hw hcj
    rw [hce] at hcj
    exact hv ((hsp w (hov w hw)).2.2.2 Q hQ v hcj).1
  · by_cases h : v ∈ S
    · exact (hord v h n).1.trans (hθ2 v hv n)
    · obtain ⟨w, hw, -⟩ := existsUnique_conjPl c.toRingEquiv.symm v
      have hcj : ConjPl c.toRingEquiv w v := fun x => by
        have := hw (c.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have hwo : Formalism.L2.Host.OverP H p w := by
        refine ((conjPl_iff_mem _ w v).1 hcj _ _ ?_).2 hv
        simp
      have hwS : w ∈ S := (hS w).2
        (((hsp w hwo).2.2.2 Q hQ v (hce ▸ hcj)).2.2 fun e => h ((hS v).2 e))
      exact ((hord w hwS n).2 v hcj).trans (hθ2 w hwo n)

end GlobalTheory.Mem.DeltaZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.EtaT

theorem card_above {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Formalism.L2.Host.aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [Formalism.L2.Host.aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

private theorem card_above_of_prime {R : Ranks} (H : Formalism.BasicNotions.Host R) (l : ℕ) (hp : l.Prime) (hl : l ∣ H.condN)
    (P : HeightOneSpectrum (𝓞 H.E)) (hP : ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal) :
    (Formalism.L2.Host.aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 2 := by
  have : Fact l.Prime := ⟨hp⟩
  have hPp := P.isPrime
  have hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP
  have he := H.der.eta.2.2 l hl P.asIdeal
  change (if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [card_above]
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

private theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (N : ℕ) (hN : N ≠ 0)
    (h : (N : A) ∈ P) : ∃ l : ℕ, l.Prime ∧ l ∣ N ∧ (l : A) ∈ P := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl hN
  | one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨l, h1, h2, h3⟩ := ih (fun h0 => hN (by rw [h0, mul_zero])) h
      exact ⟨l, h1, h2.mul_left _, h3⟩


open Classical in
theorem etaT_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), Formalism.L2.Host.EtaTExists H := by
  intro R H
  obtain ⟨c, hc, hcm, hunr, -, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H)
    (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by
      obtain ⟨δ, hδ, hval, hprod⟩ := UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ
      refine ⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩
      · have hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun hm => by
          obtain ⟨l, hl, hlN, hlP⟩ := exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm
          rw [card_above_of_prime H l hl hlN P hlP] at hP
          exact absurd hP (by decide)
        have h0 : Formalism.L2.Host.ordF P δ = 0 := by simp [Formalism.L2.Host.ordF, hval P hn]
        rw [h0]
        exact Even.zero
      · simp only [zpow_one]
        exact hprod)
  exact ⟨χ, h1, h2, h3, h4⟩

end GlobalTheory.Mem.EtaT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory

theorem kroneckerTwo_neg_eq_jacobiSym_two (q : ℕ) (hq : q % 4 = 3) :
    GlobalTheoryTheory.kron2 (-(q : ℤ)) = jacobiSym 2 q := by
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  unfold GlobalTheoryTheory.kron2
  split_ifs <;> omega

theorem kronSym_neg_eq_jacobiSym_and_two :
    (∀ q n : ℕ, q % 4 = 3 → 0 < n → GlobalTheoryTheory.kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
      ∀ n : ℕ, Odd n → GlobalTheoryTheory.kronSym 2 n = ZMod.χ₈ (n : ZMod 8) := by
  refine ⟨fun q n hq hn => ?_, fun n hn => ?_⟩
  · unfold GlobalTheoryTheory.kronSym
    have hodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
      exact Nat.odd_iff.mpr (by omega)
    have hmul : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [jacobiSym_neg_eq_of_three_mod_four q _ hq hodd, kroneckerTwo_neg_eq_jacobiSym_two q hq,
      ← jacobiSym.pow_left, ← jacobiSym.mul_left]
    congr 1
    rw [mul_comm]
    exact_mod_cast hmul
  · unfold GlobalTheoryTheory.kronSym
    have h0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hn; omega)
    rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two hn]

end GlobalTheory
end

