module

public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

@[expose] public section

-- bundled from ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep
section
namespace ReciprocityTheory.CA

open Polynomial


attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem height_le_one_of_comap_C_eq_bot {A : Type*} [CommRing A] [IsDomain A]
    (Q : Ideal A[X]) [Q.IsPrime] (hQ : Q.comap C = ⊥) : Q.height ≤ 1 := by

  have hd : Disjoint ((Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A) : Submonoid A[X]) :
      Set A[X]) (Q : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    have h0 : s ∈ Q.comap C := hsQ
    rw [hQ, Ideal.mem_bot] at h0
    exact nonZeroDivisors.ne_zero hs h0
  letI : Algebra A[X] (FractionRing A)[X] := Polynomial.algebra A (FractionRing A)
  haveI : IsLocalization (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A))
      (FractionRing A)[X] := Polynomial.isLocalization (nonZeroDivisors A) (FractionRing A)
  haveI hQ' : (Q.map (algebraMap A[X] (FractionRing A)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹Q.IsPrime› hd
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) (FractionRing A)[X] ‹Q.IsPrime› hd
  have hh : Q.height = (Q.map (algebraMap A[X] (FractionRing A)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_under (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hQ'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ← hh] at h1
  exact_mod_cast h1

theorem height_le_height_comap_C_add_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : P.height ≤ (P.comap C).height + 1 := by

  set p := P.comap (C : R →+* R[X]) with hp
  letI : Algebra R[X] (Localization.AtPrime p)[X] := Polynomial.algebra R (Localization.AtPrime p)
  haveI : IsLocalization (Submonoid.map (C : R →+* R[X]) p.primeCompl)
      (Localization.AtPrime p)[X] := Polynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  have hd : Disjoint ((Submonoid.map (C : R →+* R[X]) p.primeCompl : Submonoid R[X]) :
      Set R[X]) (P : Set R[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  haveI hP' : (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P ‹P.IsPrime› hd
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.map (C : R →+* R[X]) p.primeCompl) (Localization.AtPrime p)[X] ‹P.IsPrime› hd
  have hh : P.height = (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_under (Submonoid.map (C : R →+* R[X]) p.primeCompl) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hP'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), ← hh] at h1
  exact_mod_cast h1

private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    p.height = Order.height (⟨p, hp⟩ : PrimeSpectrum R) := by
  exact PrimeSpectrum.height_eq_orderHeight ⟨p, hp⟩

theorem height_add_one_le_height_comap_of_surjective {A S : Type*} [CommRing A] [IsDomain A]
    [CommRing S] (φ : A →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≠ ⊥)
    (q : Ideal S) [q.IsPrime] : q.height + 1 ≤ (q.comap φ).height := by
  let g : WithBot (PrimeSpectrum S) → PrimeSpectrum A := fun x =>
    Option.elim x ⟨⊥, Ideal.isPrime_bot⟩ (fun p => ⟨p.asIdeal.comap φ, inferInstance⟩)
  have hg : StrictMono g := by
    intro a b hab
    induction b using WithBot.recBotCoe with
    | bot => exact (not_lt_bot hab).elim
    | coe p' =>
      induction a using WithBot.recBotCoe with
      | bot =>
        change (⊥ : Ideal A) < p'.asIdeal.comap φ
        have hk : RingHom.ker φ ≤ p'.asIdeal.comap φ := fun y hy => by
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact p'.asIdeal.zero_mem
        exact bot_lt_iff_ne_bot.mpr fun h => hker (le_bot_iff.mp (hk.trans h.le))
      | coe p =>
        have hpp : p < p' := WithBot.coe_lt_coe.mp hab
        change p.asIdeal.comap φ < p'.asIdeal.comap φ
        refine lt_of_le_of_ne (Ideal.comap_mono (show p.asIdeal ≤ p'.asIdeal from hpp.le)) ?_
        intro h
        have h' : p'.asIdeal ≤ p.asIdeal :=
          (Ideal.comap_le_comap_iff_of_surjective φ hφ _ _).mp h.ge
        exact lt_irrefl _ (lt_of_lt_of_le ((PrimeSpectrum.asIdeal_lt_asIdeal p p').mpr hpp) h')
  have h1 := Order.height_le_height_apply_of_strictMono g hg
    ((⟨q, ‹_›⟩ : PrimeSpectrum S) : WithBot (PrimeSpectrum S))
  rw [Order.height_coe_withBot] at h1
  rw [height_eq_order_height_lemma q, height_eq_order_height_lemma (q.comap φ)]
  exact h1

theorem height_le_height_comap_of_eval₂_surjective {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) (x : S)
    (hgen : Function.Surjective (eval₂RingHom f x)) (halg : ∃ g : R[X], g ≠ 0 ∧ eval₂ f x g = 0)
    (q : Ideal S) [q.IsPrime] : q.height ≤ (q.comap f).height := by
  have hker : RingHom.ker (eval₂RingHom f x) ≠ ⊥ := by
    obtain ⟨g, hg0, hg⟩ := halg
    intro h
    apply hg0
    have hmem : g ∈ RingHom.ker (eval₂RingHom f x) := by
      rw [RingHom.mem_ker]
      simpa using hg
    rw [h, Ideal.mem_bot] at hmem
    exact hmem
  have h3 := height_add_one_le_height_comap_of_surjective (eval₂RingHom f x) hgen hker q
  have h2 := height_le_height_comap_C_add_one (q.comap (eval₂RingHom f x))
  have hc : (q.comap (eval₂RingHom f x)).comap (C : R →+* R[X]) = q.comap f := by
    rw [Ideal.comap_comap]
    congr 1
    ext r
    simp
  rw [hc] at h2
  exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h3.trans h2)

end ReciprocityTheory.CA
end

-- bundled from ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
section
namespace ReciprocityTheory.CA

private theorem exists_prime_over_lemma {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (p : Ideal A) [p.IsPrime] (I : Ideal B)
    (hI : I.comap (algebraMap A B) ≤ p) :
    ∃ Q : Ideal B, I ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap A B) = p := by
  first
  | exact Ideal.exists_ideal_over_prime_of_isIntegral p I hI
  | exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p I hI
  | (obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p I hI
     exact ⟨Q, h1, h2, h3⟩)

theorem exists_ltSeries_lift_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
      l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by
  suffices H : ∀ n, ∀ l : LTSeries (PrimeSpectrum A), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
        l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal by
    exact H _ l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    obtain ⟨Q, -, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal ⊥ (by
      first
      | (rw [Ideal.comap_bot_of_injective _ h]; exact bot_le)
      | (intro y hy
         rw [Ideal.mem_comap, Ideal.mem_bot] at hy
         rw [show y = 0 from h (by rw [hy, map_zero])]
         exact Ideal.zero_mem _))
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, ?_, ?_⟩
    · simp [hl]
    · simpa using hQc
  | succ n ih =>
    intro l hl
    have hne : l.length ≠ 0 := by omega
    obtain ⟨l', hlen, hlast⟩ := ih l.eraseLast (by simp [hl])
    have hlt : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
    obtain ⟨Q, hQle, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal l'.last.asIdeal (by
      rw [hlast]
      exact le_of_lt hlt)
    have hlt' : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle ?_
      intro heq
      have hc := congrArg (fun q : PrimeSpectrum B => q.asIdeal.comap (algebraMap A B)) heq
      simp only at hc
      rw [hlast, hQc] at hc
      exact (ne_of_lt hlt) (PrimeSpectrum.ext hc)
    refine ⟨l'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · first
      | (simp [hlen, hl]; done)
      | (simp [hlen, hl]; omega)
    · simpa using hQc

theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  have hmono : StrictMono (fun q : PrimeSpectrum B =>
      (⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩ : PrimeSpectrum A)) := by
    intro q q' hqq'
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hqq' ⊢
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hqq'
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff (le_of_lt hqq') ⟨hx, hx'⟩
      (Algebra.IsIntegral.isIntegral x)
  apply le_antisymm
  · first
    | exact Order.krullDim_le_of_strictMono _ hmono
    | (apply iSup_le
       intro l'
       exact le_iSup_of_le (l'.map _ hmono) le_rfl)
  · apply iSup_le
    intro l
    obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift_of_isIntegral hinj l
    rw [← hlen]
    exact le_iSup (fun p : LTSeries (PrimeSpectrum B) => (p.length : WithBot ℕ∞)) l'

theorem ringKrullDim_quotient_eq_quotient_comap_of_isIntegral {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal B) :
    ringKrullDim (B ⧸ I) = ringKrullDim (A ⧸ I.comap (algebraMap A B)) := by
  haveI : Algebra.IsIntegral (A ⧸ I.comap (algebraMap A B)) (B ⧸ I) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.quotient I
  exact ringKrullDim_eq_of_isIntegral_of_injective Ideal.algebraMap_quotient_injective

end ReciprocityTheory.CA
end

