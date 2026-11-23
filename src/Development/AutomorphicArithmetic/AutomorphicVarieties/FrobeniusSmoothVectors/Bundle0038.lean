module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Ufacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem km_mono {Ω C : Type} [Field Ω] [CharZero Ω] [Monoid C] {m n : ℕ} (h : m ∣ n) {χ : G ℚ Ω →* C}
    (hχ : Af.KillsMu m χ) : Af.KillsMu n χ := fun s hs => hχ s fun ζ hζ => hs ζ (by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hζ, one_pow])

private theorem split_of {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {N w : ℕ} (hw : w ≡ 1 [MOD N])
    {χ : G ℚ Ω →* (Qbar l)ˣ} (hχ : Af.KillsMu N χ) : Sd.SplitAt N w χ :=
  ⟨hχ, fun s hs => hχ s fun ζ hζ => by
    rw [hs ζ hζ, pow_eq_pow_mod w hζ, hw, ← pow_eq_pow_mod 1 hζ, pow_one]⟩

theorem UpperTheory.V.Fr.seed_cl :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ Q : ℕ, Q ≠ 0 ∧ ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (w : ℕ), IsAbelianGalois ℚ L → galOf ℚ L Ω = upl Ω L ⊓ η.ker → FrobeniusWitnessPrime l η Ψ M w → w ≡ 1 [MOD Q] → upl Ω L ≤ Hth Ω l w → (∃ s ∈ galOf ℚ L Ω, barChar c.O Ψ s ^ 2 ≠ 1) → SeedClause c η Ψ σ L := by
  intro Ω _ _ _ l _ c _ η Ψ σ B M Hb hG
  have hlp : l.Prime := Fact.out
  obtain ⟨a, hηa, hΨa⟩ := hG.cyc
  obtain ⟨j, hj⟩ := hG.Ψ_l
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := hG.quad
  obtain ⟨K, iK, nK, aK, hK2, hKc, hKη⟩ := sc_quad Ω η D δ hD hδ hηδ
  obtain ⟨T, hT, hTa⟩ := sc_teich Ω l c hG.fin
  have hM : M ^ a * l ≠ 0 := mul_ne_zero (pow_ne_zero _ hG.M_ne) hlp.ne_zero
  obtain ⟨r, N, hlN, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM l hlp.one_lt.ne'
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM (by rw [hN, mul_zero])
  let φ : G ℚ Ω →* (ResidueField c.O)ˣ := barChar c.O Ψ * (omO Ω l c.O ^ j)⁻¹
  let χ' : G ℚ Ω →* (Qbar l)ˣ := T.comp φ
  let η' : G ℚ Ω →* (Qbar l)ˣ := (Units.map (Int.castRingHom (Qbar l)).toMonoidHom).comp η
  have hφ : ∀ s, φ s = barChar c.O Ψ s * ((omO Ω l c.O) s ^ j)⁻¹ := fun s => rfl
  have hχ : ∀ s, χ' s = T (φ s) := fun s => rfl
  have hη'ker : η'.ker = η.ker := by
    ext s
    simp only [MonoidHom.mem_ker]
    exact map_eq_one_iff _ (Units.map_injective (f := (Int.castRingHom (Qbar l)).toMonoidHom) Int.cast_injective)
  have hφK : Af.KillsMu (M ^ a * l) φ := by
    intro s hs
    have h1 : barChar c.O Ψ s = 1 := km_mono (dvd_mul_right _ _) hΨa s hs
    have h2 : omO Ω l c.O s = 1 := km_mono (dvd_mul_left _ _) (sc_om Ω l c.O).1 s hs
    rw [hφ, h1, h2, one_pow, inv_one, mul_one]
  have hχK : Af.KillsMu (M ^ a * l) χ' := by
    intro s hs
    rw [hχ, hφK s hs, map_one]
  have hη'K : Af.KillsMu (M ^ a * l) η' := by
    intro s hs
    have h1 : η s = 1 := km_mono (dvd_mul_right _ _) hηa s hs
    show Units.map _ (η s) = 1
    rw [h1, map_one]
  have hχN : Af.KillsMu N χ' := by
    refine sc_strip Ω l _ χ' r N hN0 hlN (hN ▸ hχK) B hG.over_l ?_
    intro s hs
    rw [MonoidHom.mem_ker, hχ, hφ, hj B hG.over_l s hs, mul_inv_cancel, map_one]
  have hη'N : Af.KillsMu N η' := by
    refine sc_strip Ω l _ η' r N hN0 hlN (hN ▸ hη'K) B hG.over_l ?_
    rw [hη'ker]
    exact hG.η_l B hG.over_l
  have hT1 : T (-1) = -1 := by
    have hne : (-1 : (ResidueField c.O)ˣ) ≠ 1 := by
      intro h
      have h' : (-1 : ResidueField c.O) = 1 := by
        simpa using congrArg (fun u : (ResidueField c.O)ˣ => (u : ResidueField c.O)) h
      rw [neg_one_eq_one_iff, ringChar.eq (ResidueField c.O) l] at h'
      exact hG.odd h'
    have hsq : ((T (-1) : (Qbar l)ˣ) : Qbar l) * (T (-1) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (hT (by rw [map_one]; exact Units.ext h)) hne
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have happ : ∀ s, (GlobalTheory.GalOfCusp.cycBar ℚ Ω l ^ j * χ') s =
      (GlobalTheory.GalOfCusp.cycBar ℚ Ω l) s ^ j * T ((Units.map ↑(residue c.O)) (Ψ s) * ((omO Ω l c.O) s ^ j)⁻¹) :=
    fun s => rfl
  have hord : ¬ l ∣ orderOf χ' := by
    classical
    haveI := Fintype.ofFinite (ResidueField c.O)
    have hpow : χ' ^ Fintype.card (ResidueField c.O)ˣ = 1 := MonoidHom.ext fun s => by
      show (T (φ s)) ^ Fintype.card (ResidueField c.O)ˣ = 1
      rw [← map_pow, pow_card_eq_one, map_one]
    intro hd
    have hd2 := hd.trans (orderOf_dvd_of_pow_eq_one hpow)
    obtain ⟨n, -, hcard⟩ := FiniteField.card (ResidueField c.O) l
    rw [Fintype.card_units, hcard] at hd2
    have hl1 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hlp.pos
    have h3 : l ∣ (l ^ (n : ℕ) - 1) + 1 := by
      rw [Nat.sub_add_cancel hpos]
      exact hl1
    exact hlp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd2).1 h3))
  refine ⟨N, hN0, ?_⟩
  intro L _ _ _ _ w hLab hLgal hw hwQ hLth hs0
  obtain ⟨s0, hs0L, hs0⟩ := hs0
  obtain ⟨θ, hθker, hθ1, hθl, hθw⟩ := sc_theta Ω l w hw.prime hw.one
  have hwN : ¬ w ∣ N := by
    intro hd
    have hd' : w ∣ M ^ a * l := hN ▸ dvd_mul_of_dvd_right hd _
    rcases (Nat.Prime.dvd_mul hw.prime).1 hd' with h | h
    · exact hw.cop (hw.prime.dvd_of_dvd_pow h)
    · have hwl := (Nat.prime_dvd_prime_iff_eq hw.prime hlp).1 h
      have h1 : w % l = 1 % l := hw.one
      rw [hwl, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt] at h1
      exact zero_ne_one h1
  have hLK : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
    rw [hKη, hLgal]
    exact inf_le_right
  refine ⟨K, iK, nK, aK, N, w, χ', η', θ, j, ?_, ?_, hord, fun s => rfl, fun s => happ s ▸ hTa (Ψ s) j s, ?_⟩
  · refine ⟨hG.cc, ⟨hG.odd, Nat.pos_of_ne_zero hN0, hlN, hw.prime, hwN, hθ1, hθl, hθw⟩, hK2, hKc, hLab, hLK,
      by rw [hη'ker, hKη], split_of hwQ hη'N, split_of hwQ hχN, ?_, ?_, ?_⟩
    · rw [hθker, hLgal]
      exact inf_le_left.trans hLth
    · rw [hχ, hφ, hG.even, (sc_om Ω l c.O).2 σ hG.cc, one_mul, ← inv_pow, inv_neg_one, map_pow, hT1]
    · refine ⟨s0, hs0L, fun hc => hs0 ?_⟩
      exact sc_cong l c (Ψ s0) _ (happ s0 ▸ hTa (Ψ s0) j s0) hc
  · intro heq
    apply hG.g4
    intro s hs
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hs
    have h1 : χ' s = 1 := by
      rw [hχ, hφ, hs.1, hs.2, one_pow, inv_one, mul_one, map_one]
    rw [heq] at h1
    rw [← hη'ker]
    exact h1
  · exact sc_disc Ω l K hK2 (fun B' hB' => hKη ▸ hG.η_l B' hB')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Strict
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem st_char : GC.Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (κ : G ℚ Ω →* kˣ), IsOpen (κ.ker : Set (G ℚ Ω)) → (∃ σ : G ℚ Ω, IsCC σ ∧ κ σ ≠ 1) → (∃ s, κ s ≠ GC.cycF ℚ Ω l k s) → ∀ N w : ℕ, N ≠ 0 → w.Prime → w ≠ l → (∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker) → (∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1) →
    ∃ y : G ℚ Ω → k, IsLocallyConstant y ∧ (∀ s t, y (s * t) = y s + κ s * y t) ∧ (¬ ∃ b, ∀ s, y s = κ s * b - b) ∧ (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (w : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A, κ s = 1 → y s = 0 := by
  intro hP Ω _ _ _ l _ hl2 k _ _ _ κ hκo hcc hcyc N w hN hw hwl hram hdecw hdecl
  have hlp : l.Prime := Fact.out
  obtain ⟨hIt, hex, hne, hdict⟩ := Kum.placeDict ℚ Ω
  obtain ⟨S, v₀, hv₀, hS⟩ := st_set Ω l w N hlp hw hN _ κ hram
  have hmem : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ), IsPlaceOver A v →
      (A.valuation (n : Ω) < 1 ↔ (n : 𝓞 ℚ) ∈ v.asIdeal) :=
    fun A v n h => hdict A v n h
  have hw0 : (w : 𝓞 ℚ) ∈ v₀.asIdeal := (hv₀ v₀).2 rfl
  have hl_notin : (l : 𝓞 ℚ) ∉ v₀.asIdeal := by
    intro hl
    have hcop : IsCoprime (l : ℤ) (w : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hlp hw).2 (Ne.symm hwl))
    have hcop' : IsCoprime (l : 𝓞 ℚ) (w : 𝓞 ℚ) := by
      simpa using hcop.map (Int.castRingHom (𝓞 ℚ))
    obtain ⟨u, u', hu⟩ := hcop'
    apply v₀.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hu]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hw0)
  have hv₀S : v₀ ∈ S := (hS v₀ (placeOf Ω v₀) (isPlaceOver_placeOf Ω v₀)).2 (Or.inr (Or.inl rfl))
  have hCA : ContainsAbove S l := fun v hv => (hS v (placeOf Ω v) (isPlaceOver_placeOf Ω v)).2 (Or.inl hv)
  have hout : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker := by
    intro v hv A hA
    by_contra h
    exact hv ((hS v A hA).2 (Or.inr (Or.inr h)))
  have hdec0 : ∀ A : ValuationSubring Ω, IsPlaceOver A v₀ → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker :=
    fun A hA => hdecw A ((hmem A v₀ w hA).2 hw0)
  have hother : ∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1 := by
    intro v hv hne' A hA
    rcases (hS v A hA).1 hv with h | h | h
    · exact hdecl A ((hmem A v l hA).2 h)
    · exact absurd h hne'
    · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 h
      exact ⟨s, Ine_le_Dec A hs, by rwa [MonoidHom.mem_ker] at hs'⟩
  obtain ⟨y, hyc, hyco, hynot, hyout, hyS⟩ :=
    st_sel hP Ω l hl2 k κ hκo hcc hcyc S hCA hout v₀ hv₀S hl_notin hdec0 hother
  have hcob : ∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = (κ s : k) * b - b := by
    intro v hv hne' A hA
    obtain ⟨A0, hA0, hb⟩ := hyS v hv hne'
    exact st_conj Ω k κ y hyco v A0 A hA0 hA hb
  refine ⟨y, hyc, hyco, hynot, ?_, ?_⟩
  · intro A hA
    obtain ⟨v, hv⟩ := hex A (hne A l hlp.ne_zero hA)
    have hlv := (hmem A v l hv).1 hA
    refine hcob v (hCA v hlv) ?_ A hv
    rintro rfl
    exact hl_notin hlv
  · intro A hA s hs hκs
    by_cases htop : A = ⊤
    · subst htop
      rw [hIt] at hs
      rw [Subgroup.mem_bot.1 hs]
      have h := hyco 1 1
      rw [mul_one, map_one, Units.val_one, one_mul] at h
      simpa using h
    obtain ⟨v, hv⟩ := hex A htop
    by_cases hvS : v ∈ S
    · have hvne : v ≠ v₀ := by
        intro h
        exact hA ((hmem A v w hv).2 (h ▸ hw0))
      obtain ⟨b, hb⟩ := hcob v hvS hvne A hv
      rw [hb s (Ine_le_Dec A hs), hκs, Units.val_one, one_mul, sub_self]
    · exact hyout v hvS A hv s hs

theorem UpperTheory.V.Fr.strict :
    GC.Hypotheses₂ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ (m : ℕ) (a : ℕ), a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (Upl l Hb H₀ w m) := by
  intro hP Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hw m a ha
  have hlp : l.Prime := Fact.out
  haveI : Finite (ResidueField O) := hG.fin
  have hF := ufacts l η Ψ σ B M Hb hG H₀ w h0 hw m
  set U := Upl l Hb H₀ w m with hU
  set κ : G ℚ Ω →* (ResidueField O)ˣ := (barChar O Ψ)⁻¹ ^ a * etaO O η with hκdef
  have hκ : ∀ s, κ s = ((barChar O Ψ s)⁻¹) ^ a * etaO O η s := fun s => rfl
  have hκη : ∀ s, η s = 1 → κ s = ((barChar O Ψ s)⁻¹) ^ a := by
    intro s h1
    rw [hκ]
    show _ * Units.map _ (η s) = _
    rw [h1, map_one, mul_one]
  have hκ1 : ∀ s, η s = 1 → barChar O Ψ s = 1 → κ s = 1 := by
    intro s h1 h2
    rw [hκη s h1, h2, inv_one, one_pow]
  obtain ⟨b, hηb, hΨb⟩ := hG.cyc
  have hκK : Af.KillsMu (M ^ b) κ := fun s hs => hκ1 s (hηb s hs) (hΨb s hs)
  obtain ⟨hKo, hram⟩ := st_mu Ω M b hG.M_ne _ κ hκK
  have hM_l : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → A.valuation (M : Ω) < 1 := by
    intro A hA
    obtain ⟨t, ht⟩ := hG.l_dvd
    rw [ht, Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A t)) hA
  have hdecl : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A ⊓ U, κ s ≠ 1 := by
    intro A hA
    obtain ⟨s, hs, hs2⟩ := hF.f3 A hA
    have hη : η s = 1 := hF.split A (hM_l A hA) hs
    refine ⟨s, hs, ?_⟩
    rw [hκη s hη]
    rcases ha with rfl | rfl
    · intro h
      apply hs2
      rw [pow_one, inv_eq_one] at h
      rw [h, one_pow]
    · intro h
      apply hs2
      rwa [inv_pow, inv_eq_one] at h
  have hne1 : (-1 : ResidueField O) ≠ 1 := by
    rw [Ne, neg_one_eq_one_iff, ringChar.eq (ResidueField O) l]
    exact hG.odd
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := hG.quad
  have hησ : η σ = -1 := st_eta Ω η D δ hD hδ hηδ σ hG.cc
  have hκσ : κ σ ≠ 1 := by
    rw [hκ, hG.even, inv_one, one_pow, one_mul]
    intro h
    apply hne1
    have h' := congrArg (fun u : (ResidueField O)ˣ => (u : ResidueField O)) h
    simpa [etaO, hησ] using h'
  have hcyc : ∃ s, κ s ≠ GC.cycF ℚ Ω l (ResidueField O) s := by
    have hex : ∃ s ∈ U ⊓ η.ker, (omO Ω l O) s * (barChar O Ψ) s ^ (a : ℤ) ≠ 1 := by
      rcases ha with rfl | rfl
      · exact hF.f2b 1 (Or.inl rfl)
      · exact hF.f2c 2 (Or.inl rfl)
    obtain ⟨s, hs, hne⟩ := hex
    have hη : η s = 1 := (Subgroup.mem_inf.1 hs).2
    refine ⟨s, fun h => hne ?_⟩
    have h' : omO Ω l O s = κ s := h.symm
    rw [h', hκη s hη, zpow_natCast, inv_pow, inv_mul_cancel]
  have hwl : w ≠ l := by
    intro h
    have h1 : w % l = 1 % l := hw.one
    rw [h, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt] at h1
    exact zero_ne_one h1
  have hdecw : ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 →
      Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l (ResidueField O)).ker := by
    intro A hA s hs
    obtain ⟨h12, h3⟩ := Subgroup.mem_inf.1 (hw.split A hA hs)
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h12
    exact Subgroup.mem_inf.2 ⟨hκ1 s h1 h2, h3⟩
  obtain ⟨y, hyc, hyco, hynot, hydec, hyw⟩ :=
    st_char hP Ω l hG.odd (ResidueField O) κ hKo ⟨σ, hG.cc, hκσ⟩ hcyc M w hG.M_ne hw.prime hwl hram hdecw
      (fun A hA => by
        obtain ⟨s, hs, h⟩ := hdecl A hA
        exact ⟨s, (Subgroup.mem_inf.1 hs).1, h⟩)
  refine ⟨y, hyc, hyco, ?_, hydec, ?_⟩
  · rintro ⟨b0, hb0⟩
    obtain ⟨s, hs, hκs⟩ := hdecl B hG.over_l
    exact hynot (st_res (G ℚ Ω) _ κ U hF.ab ⟨s, (Subgroup.mem_inf.1 hs).2, hκs⟩ y hyco ⟨b0, hb0⟩)
  · intro B' hB' s hs hη hΨ
    have hs' := Subgroup.mem_inf.1 hs
    by_cases hBw : B'.valuation (w : Ω) < 1
    · have hth' := hth Ω l w hw.prime hw.one
      have hsH : s ∈ Hth Ω l w := by
        have h2 := hs'.2
        simp only [hU, Upl, Subgroup.mem_inf] at h2
        exact h2.1.1.2
      refine st_tame Ω l (ResidueField O) B' hB' _ hth'.1 hth'.2.1 hth'.2.2.1 (hth'.2.2.2.2 B' hBw) y hyc ?_ s
        (Subgroup.mem_inf.2 ⟨hs'.1, hsH⟩)
      intro s1 hs1 t1 _
      have hk : κ s1 = 1 := (Subgroup.mem_inf.1 (hdecw B' hBw (Ine_le_Dec B' hs1))).1
      rw [hyco, hk, Units.val_one, one_mul]
    · exact hyw B' hBw s hs'.1 (hκ1 s hη hΨ)
end

