module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.MemIffDvd
section
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

private theorem intCast_mem_asIdeal_iff_dvd (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (q : ℕ) (hq : q.Prime) (hP : (q : 𝓞 E) ∈ P.asIdeal) (n : ℤ) :
    (n : 𝓞 E) ∈ P.asIdeal ↔ (q : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hc : IsCoprime (q : ℤ) n :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq).irreducible).mpr hnd
    obtain ⟨x, z, hxz⟩ := hc
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 := congrArg (Int.cast : ℤ → 𝓞 E) hxz
    push_cast at h1
    rw [← h1]
    exact add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hn)
  · rintro ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hP

theorem UpperTheory.Gal.G1.pKeyK :
    DiscInt → KeyK := by
  intro hD E _ _ _ A q hq hqD r u w hqu hqw hru hrw y hy
  obtain ⟨a, b, hab⟩ := hD E A y hy
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ P.asIdeal → A.ω - (r : 𝓞 E) ∈ P.asIdeal →
      (y ∈ P.asIdeal ↔ (q : ℤ) ∣ a + b * r) := by
    intro P hP hωP
    have hDP : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∉ P.asIdeal :=
      fun h => hqD ((intCast_mem_asIdeal_iff_dvd E P q hq hP _).mp h)
    have hdiff : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y - ((a + b * r : ℤ) : 𝓞 E) ∈ P.asIdeal := by
      rw [hab]
      have h4 : (a : 𝓞 E) + (b : 𝓞 E) * A.ω - ((a + b * r : ℤ) : 𝓞 E) = (b : 𝓞 E) * (A.ω - (r : 𝓞 E)) := by
        push_cast; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ hωP
    rw [← intCast_mem_asIdeal_iff_dvd E P q hq hP]
    constructor
    · intro hy'
      have h5 : ((a + b * r : ℤ) : 𝓞 E) = ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y -
          (((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y - ((a + b * r : ℤ) : 𝓞 E)) := by ring
      rw [h5]
      exact sub_mem (Ideal.mul_mem_left _ _ hy') hdiff
    · intro hc
      have hm : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y ∈ P.asIdeal := by
        have h6 := add_mem hdiff hc
        rwa [sub_add_cancel] at h6
      exact (P.isPrime.mem_or_mem hm).resolve_left hDP
  rw [key u hqu hru, key w hqw hrw]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBarAdj
section
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pBarAdj :
    DiscInt → BarAdj := by
  intro h E _ _ _ A y hy
  obtain ⟨a, b, hab⟩ := h E A y hy
  have hD : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) ≠ 0 := by
    exact_mod_cast ne_of_lt A.disc_neg
  have hb : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have h1 := congrArg A.bar hab
  simp only [map_mul, map_add (f := _), map_intCast] at h1
  rw [hb] at h1
  have h2 : (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) * ((A.bar y : 𝓞 E) : E)
      = (a : E) + (b : E) * ((A.tr : E) - (A.ω : E)) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) h1
    simpa only [map_mul, map_add (f := _), map_sub, map_intCast] using h3
  have e : ((A.bar y : 𝓞 E) : E)
      = ((a : E) + (b : E) * ((A.tr : E) - (A.ω : E))) / (((A.tr ^ 2 - 4 * A.nm : ℤ)) : E) := by
    rw [← h2, mul_div_cancel_left₀ _ hD]
  rw [e]
  exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _)
    (sub_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)))) (intCast_mem _ _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCjMem
section
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pCjMem :
    CjMem := by
  intro E _ _ _ A w y
  have hb : ((A.bar y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := A.bar_eq y
  have hv := GlobalTheory.BCT.SuppFin.valuation_conj E w (y : E)
  rw [← hb] at hv
  have h1 := HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (A.bar y)
  have h2 := HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (CertificateRingHomMap.cj w) y
  rw [← h1, ← h2]
  exact iff_of_eq (congrArg (· < 1) hv.symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSides
section
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

theorem UpperTheory.Gal.G1.pSides :
    CjMem → BarAdj → KeyK → RootAt → Pl.Sides := by
  intro hCj hBar hKey hRoot E _ _ _ A x hG q hq hs w hw
  have hadj : IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {(A.ω : E)} :=
    le_antisymm (IntermediateField.adjoin_simple_le_iff.2 hG.2) (IntermediateField.adjoin_simple_le_iff.2 hG.1)
  have hS : ∀ u u' : HeightOneSpectrum (𝓞 E), CertificateRingHomMap.SameK x u u' ↔
      ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ u'.asIdeal) := fun u u' => by
    unfold CertificateRingHomMap.SameK
    rw [hadj]
  have hnd := hs.1
  have hmemω : ∀ s : ℤ, ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := fun s => by
    have e : ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) = (A.ω : E) - (s : E) := by
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _ - _
      simp
    rw [e]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self ℚ _) (intCast_mem _ s)
  have hmemq : ((q : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := by
    have e : ((q : 𝓞 E) : E) = (q : E) := by
      change algebraMap (𝓞 E) E _ = _
      simp
    rw [e]
    exact natCast_mem _ q
  have hbarI : ∀ s : ℤ, A.bar (s : 𝓞 E) = (s : 𝓞 E) := fun s => map_intCast A.bar s
  have hbarN : A.bar (q : 𝓞 E) = (q : 𝓞 E) := map_natCast A.bar q
  have hbarω : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have hbarsub : ∀ s : ℤ, A.bar (A.ω - (s : 𝓞 E)) = (A.tr : 𝓞 E) - A.ω - (s : 𝓞 E) := fun s => by
    rw [map_sub, hbarω, hbarI]
  have hquad : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]; ring
  obtain ⟨r, hr, hrw⟩ := hRoot E A q hq hs w hw
  have hne1 : ¬ CertificateRingHomMap.SameK x (CertificateRingHomMap.cj w) w := by
    intro h
    have h1 : A.ω - (r : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := ((hS _ _).1 h _ (hmemω r)).2 hrw
    have h2 : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) ∈ w.asIdeal := by
      rw [← hbarsub]; exact (hCj E A w _).1 h1
    have h3 : ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem hrw h2
      have e : A.ω - (r : 𝓞 E) - ((A.tr : 𝓞 E) - A.ω - (r : 𝓞 E)) = (2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E) := by ring
      rwa [e] at this
    have h4 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.mul_mem_left ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) h3
      have e : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) = ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) * ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) - 4 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) * (-1) - 8 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) := by
        push_cast; ring
      rw [e, hquad]
      simpa using this
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 hnd
    have h5 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 E) = (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) := by
        exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hab).symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ h4)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h5)
  refine ⟨hne1, ?_, ?_, ?_, ?_, ⟨r, hr, hrw⟩, ?_⟩
  · refine ⟨CertificateRingHomMap.cj w, fun h => hne1 (by rw [h]; exact fun _ _ => Iff.rfl), ?_⟩
    exact GlobalTheory.DefU.ClassFin.under_conjSrc _ (fun y => (IsCMField.complexConj E).commutes y) w
  · intro u hu
    obtain ⟨k, hk⟩ := hr
    have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
    have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
      push_cast
      linear_combination hquad - hkE
    have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ u.asIdeal := by
      rw [hprod]; exact u.asIdeal.mul_mem_right _ hu
    rcases u.isPrime.mem_or_mem hmem with h | h
    · exact Or.inl ((hS _ _).2 (hKey E A q hq hnd r u w hu hw h hrw))
    · refine Or.inr ((hS _ _).2 (hKey E A q hq hnd r (CertificateRingHomMap.cj u) w ?_ hw ?_ hrw))
      · rw [hCj E A u, hbarN]; exact hu
      · rw [hCj E A u, hbarsub]
        have e : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) = -(A.ω - ((A.tr - r : ℤ) : 𝓞 E)) := by
          push_cast; ring
        rw [e]
        exact u.asIdeal.neg_mem h
  · intro u h
    exact ((hS _ _).1 h _ hmemq).2 hw
  · intro u u' h y hy
    rw [hadj] at hy
    rw [hCj E A u, hCj E A u']
    exact (hS _ _).1 h _ (hBar E A y hy)
  · intro s hsw u
    constructor
    · intro h
      exact ⟨((hS _ _).1 h _ hmemq).2 hw, ((hS _ _).1 h _ (hmemω s)).2 hsw⟩
    · rintro ⟨h1, h2⟩
      exact (hS _ _).2 (hKey E A q hq hnd s u w h1 hw h2 hsw)
end

