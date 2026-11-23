module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AsmUnr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def UnrSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ f : ℕ, 0 < f → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ X : Fld E Ω, Tower S X ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → normV w' = normV w ^ f) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u →
        ∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ

private theorem over_under {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (maximalRealSubfield E))) := by
  intro x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hA]
  rfl

private theorem dec_res {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {g : G E Ω} (hg : g ∈ Dec (F := E) A) :
    AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ Dec (F := maximalRealSubfield E) A := by
  exact hg

private theorem ine_res {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {g : G E Ω} (hg : g ∈ Ine (F := E) A) :
    AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ Ine (F := maximalRealSubfield E) A := by
  exact ⟨dec_res hg.1, hg.2⟩

theorem unrSplit_of (h1 : GroupStep) (h2 : UnrCharPP) (h3 : FreshSplit) (h4 : ExFld) (h6 : LayerOf) (h7 : DegOf)
    (h8 : SplitIff) : UnrSplit := by
  unfold UnrSplit
  intro E Ω _ _ _ _ _ _ w hw f hf S hS
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  obtain ⟨r, hrG, hrR, hrv⟩ := unrCharAt_of h2 f hf E Ω v
  obtain ⟨m, hm, hrm⟩ : ∃ m, 0 < m ∧ r ^ m = 1 := by
    haveI : Finite (G (maximalRealSubfield E) Ω ⧸ r.ker) :=
      Subgroup.quotient_finite_of_isOpen _ hrG.isOpen
    refine ⟨r.ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_⟩
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, ← map_pow, MonoidHom.one_apply]
    exact MonoidHom.mem_ker.mp (r.ker.pow_index_mem g)
  let T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :=
    insert v ((fun s : HeightOneSpectrum (𝓞 E) => s.under (𝓞 (maximalRealSubfield E))) '' S)
  have hTf : T.Finite := (hS.image _).insert v
  have mkPl : ∀ (ψ : G (maximalRealSubfield E) Ω →* ℂˣ) (n : ℕ), 2 ≤ n → RamSplit E ψ.ker →
      ∀ u, u ∉ T → (∀ A : ValuationSubring Ω, IsPlaceOver A u →
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n) →
      (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) ∧
        ∀ A : ValuationSubring Ω, IsPlaceOver A u →
          ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g := by
    intro ψ n hn hR u huT hu
    refine ⟨fun s hs h => huT (Set.mem_insert_of_mem _ ⟨s, hs, h⟩), fun A hA => ?_⟩
    have hR' := hR
    unfold RamSplit at hR'
    rcases hR' u A hA with h | h
    · obtain ⟨τ, hτ, ho⟩ := hu A hA
      have h1' : ψ τ = 1 := MonoidHom.mem_ker.mp (h hτ)
      rw [h1', orderOf_one] at ho
      omega
    · exact h
  obtain ⟨r', hr'Gd, hr'D, X, hXc, hXT⟩ := h1 (G (maximalRealSubfield E) Ω)
    (fun H => Good H ∧ RamSplit E H)
    (fun H => ∃ X : Fld E Ω, Cuts X H ∧ Tower S X)
    {g | ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ g ∈ Dec (F := maximalRealSubfield E) A}
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) //
      (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) ∧
        ∀ A : ValuationSubring Ω, IsPlaceOver A u →
          ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g}
    (fun u => {g | ∃ A : ValuationSubring Ω, IsPlaceOver A u.1 ∧ g ∈ Dec (F := maximalRealSubfield E) A})
    (fun u => {g | ∃ A : ValuationSubring Ω, IsPlaceOver A u.1 ∧ g ∈ Ine (F := maximalRealSubfield E) A})
    (by
      rintro u g ⟨A, hA, hg⟩
      exact ⟨A, hA, Ine_le_Dec A hg⟩)
    (by
      rintro H H' ⟨hG, hR⟩ ⟨hG', hR'⟩
      exact ⟨hG.inf hG', hR.inf hR'⟩)
    (by
      rintro H H' hle ⟨hG, hR⟩
      exact ⟨hG.mono hle, hR.mono hle⟩)
    (by
      rintro U ⟨hUG, -⟩ n hn
      obtain ⟨ψ, hψG, hψR, -, hψT, u, huT, hu⟩ :=
        h3 E Ω U hUG.isOpen T hTf (max n 2) (by omega)
      have hPl := mkPl ψ (max n 2) (le_max_right _ _) hψR u huT (fun A hA => (hu A hA).2)
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
      rcases Nat.lt_or_ge n 2 with h | h
      · have hn1 : n = 1 := by omega
        subst hn1
        refine ⟨1, ?_, one_pow _, fun g _ => rfl, ⟨u, hPl⟩, ?_, 1, ⟨A, hA, Subgroup.one_mem _⟩, by simp⟩
        · rw [MonoidHom.ker_one]
          exact ⟨Good.top, RamSplit.mono le_top hψR⟩
        · rintro g ⟨B, hB, hg⟩
          exact (hu B hB).1 hg
      · obtain ⟨ψ', hψ'G, hψ'R, hψ'n, hψ'T, u', hu'T, hu'⟩ :=
          h3 E Ω U hUG.isOpen T hTf n hn
        have hPl' := mkPl ψ' n h hψ'R u' hu'T (fun B hB => (hu' B hB).2)
        obtain ⟨A', hA'⟩ := exists_isPlaceOver Ω u'
        obtain ⟨τ, hτ, ho⟩ := (hu' A' hA').2
        refine ⟨ψ', ⟨hψ'G, hψ'R⟩, hψ'n, ?_, ⟨u', hPl'⟩, ?_, τ, ⟨A', hA', hτ⟩, ho⟩
        · rintro g ⟨B, hB, hg⟩
          exact hψ'T v (Set.mem_insert _ _) B hB g hg
        · rintro g ⟨B, hB, hg⟩
          exact (hu' B hB).1 hg)
    (by
      rintro H H' u ⟨-, -⟩ ⟨hG', -⟩ ⟨X, hX, hXT⟩ hle hp hDc ⟨τ, ⟨A0, hA0, hτ⟩, hτ'⟩
      obtain ⟨Y, hY⟩ := h4 E Ω H' hG'
      have hL := h6 E Ω S H H' hG' hle hp X Y hX hY u.1 u.2.1
        (fun A hA g hg => ⟨u.2.2 A hA g hg, by exact hDc ⟨A, hA, hg⟩⟩) ⟨A0, hA0, τ, hτ, hτ'⟩
      exact ⟨Y, hY, hXT.step hL.1⟩)
    ⊤ r ⟨Good.top, RamSplit.mono le_top hrR⟩ ⟨Fld.base E Ω, cuts_base, Tower.base S⟩
    ⟨hrG, hrR⟩ m hm hrm
  obtain ⟨-, hr'R⟩ := hr'Gd
  have hc : ∀ g : G E Ω, Fixes X.K g ↔
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ ⊤ ⊓ r'.ker := by
    unfold Cuts at hXc
    exact hXc
  have key : ∀ g : G E Ω, Fixes X.K g ↔
      r' (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g) = 1 := fun g =>
    ⟨fun h => MonoidHom.mem_ker.mp ((hc g).1 h).2,
      fun h => (hc g).2 ⟨Subgroup.mem_top _, MonoidHom.mem_ker.mpr h⟩⟩
  have hIne : ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ := by
    intro A hA τ hτ
    have hA' : IsPlaceOver A v := over_under hA
    rw [key, hr'D _ ⟨A, hA', Ine_le_Dec A (ine_res hτ)⟩]
    exact MonoidHom.mem_ker.mp ((hrv A hA').1 (ine_res hτ))
  refine ⟨X, hXT, fun A hA => ⟨hIne A hA, fun w' hw' => ?_⟩, ?_⟩
  · haveI := X.tower
    have hA' : IsPlaceOver A v := over_under hA
    have hsplit := (h8 E Ω A w hA).1 hw
    obtain ⟨φ₀, hφ₀⟩ := exists_isFrob hA'
    have hvw : normV w = normV v ^ 1 :=
      h7 (maximalRealSubfield E) E Ω A v w hA' hA
        (fun τ hτ => hsplit τ (Ine_le_Dec A hτ)) φ₀ 1 one_pos hφ₀
        (fun k => ⟨fun _ => one_dvd k, fun _ => hsplit _ (Subgroup.pow_mem _ hφ₀.1 k)⟩)
    rw [pow_one] at hvw
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφD : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) φ ∈
        Dec (F := maximalRealSubfield E) A := dec_res hφ.1
    have hφF : IsFrob A (normV v) (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) φ) := by
      refine ⟨hφD, fun x hx => ?_⟩
      have := hφ.2 x hx
      rw [hvw] at this
      exact this
    have hord := (hrv A hA').2 _ hφF
    refine h7 E X.K Ω A w w' hA hw' (hIne A hA) φ f hf hφ (fun k => ?_)
    rw [key, map_pow, map_pow, hr'D _ ⟨A, hA', hφD⟩, ← orderOf_dvd_iff_pow_eq_one, hord]
  · intro u hu A hA τ hτ
    have hA' := over_under hA
    rw [key]
    have hR := hr'R
    unfold RamSplit at hR
    rcases hR _ A hA' with h | h
    · exact MonoidHom.mem_ker.mp (h (ine_res hτ))
    · exact absurd ((h8 E Ω A u hA).2 h) hu

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ExistsPlaceOfPrime
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_prime_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∀ n : ℕ, n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ A.valuation (r : Ω) < 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hv
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hv
    have hp := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    by_cases h : A.valuation ((n.minFac : ℕ) : Ω) < 1
    · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
    · have h1 : A.valuation ((n.minFac : ℕ) : Ω) = 1 :=
        le_antisymm (ReciprocityTheory.Gal.valuation_natCast_le_one A _) (not_lt.1 h)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hp.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        nlinarith [hm]
      have hvm : A.valuation (m : Ω) < 1 := by
        have e : A.valuation ((n : ℕ) : Ω) = A.valuation ((n.minFac : ℕ) : Ω) * A.valuation (m : Ω) := by
          rw [← map_mul, ← Nat.cast_mul, ← hm]
        rwa [e, h1, one_mul] at hv
      obtain ⟨r, hr, hrm, hrv⟩ := ih m hlt hm0 hvm
      exact ⟨r, hr, hrm.trans ⟨n.minFac, by rw [mul_comm]; exact hm⟩, hrv⟩

private theorem normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  haveI : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
  exact Nat.card_pos

private theorem normV_mem {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  simpa [normV, nsmul_eq_mul] using card_nsmul_eq_zero' (G := 𝓞 F ⧸ t.asIdeal) (x := 1)

private theorem exists_place_of_prime {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal := by
  have hne : Ideal.span {((q : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at h2
    exact (Nat.prime_iff_prime_int.1 hq).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hq0 : ((q : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hmem := hle (Ideal.mem_span_singleton_self ((q : ℕ) : 𝓞 K))
  exact ⟨⟨M, hM.isPrime, fun h => hq0 (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

private theorem exists_moves {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {q : ℕ} (hq : q.Prime) (h2 : 2 < q) (hB : ∀ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2)
    {x : Ω} (hx : x ^ 2 = ((q : ℕ) : Ω)) :
    ∃ (u : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal ∧ IsPlaceOver A u ∧
      ∃ σ ∈ Ine (F := K) A, σ x = -x := by
  obtain ⟨u, hu⟩ := exists_place_of_prime (K := K) hq
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨σ, hσ, h⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj K Ω A u hA q hu (hB u) 2 two_pos
    (fun hd => by have := Nat.le_of_dvd two_pos hd; omega) x (-1) hx (by norm_num)
  exact ⟨u, A, hu, hA, σ, hσ, by rw [h]; ring⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.quad0Ex :
    SqrtFix → MkQ → UnrLarge → Quad0Ex := by
  intro hS hM hU E Ω _ _ _ _ _ _ T hT
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  obtain ⟨E', hfin, hE'⟩ : ∃ E' : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧
      ∀ (j : E →+* Ω) (y : E), j y ∈ E' :=
    ⟨IntermediateField.normalClosure ℚ E Ω, inferInstance,
      fun j y => AlgHom.fieldRange_le_normalClosure j.toRatAlgHom ⟨y, rfl⟩⟩
  haveI : NumberField E' := { }
  haveI : IsAlgClosure E' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  obtain ⟨B1, hB1⟩ := hU E
  obtain ⟨B2, hB2⟩ := hU E'
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ∏ t ∈ hT.toFinset, normV t := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Finset.prod_pos fun t _ => normV_pos' t
  have hcd : ∀ t ∈ T, normV t ∣ c := fun t ht => hc ▸ Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)
  obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 8 * c) (max (max B1 B2) (max c 2)) (by omega)
  simp only [max_lt_iff] at hgt
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hgt
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : Ω) two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((q : ℕ) : Ω) = 0 := by rw [← hx]; simp
    exact hq.ne_zero (Nat.cast_eq_zero.1 this)
  have hneg : -x ≠ x := fun h => hx0 (by
    have : (2 : Ω) * x = 0 := by linear_combination -h
    simpa using this)
  obtain ⟨u', A', _, _, σ', hσ', hσ'x⟩ := exists_moves (K := E') hq h4 (hB2 q hq h2) hx
  obtain ⟨u, A, huq, hA, τ, hτ, hτx⟩ := exists_moves (K := E) hq h4 (hB1 q hq h1) hx
  have hxZ : x ^ 2 = (((q : ℕ) : ℤ) : Ω) := by rw [hx]; simp
  obtain ⟨Q, hxQ, hspan, hfix⟩ := hM E Ω x (q : ℤ) hxZ ⟨τ, by rw [hτx]; exact hneg⟩
  have hfixT : ∀ (F : Type) [Field F] [NumberField F] [Algebra F Ω], ∀ t ∈ T, ∀ A : ValuationSubring Ω,
      IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, g x = x := by
    intro F _ _ _ t ht A hA g hg
    have hv : A.valuation ((normV t : ℕ) : Ω) < 1 := by
      have := (hA _).2 (normV_mem t)
      simpa using this
    obtain ⟨r, hr, hrd, hrv⟩ := exists_prime_val A _ (normV_pos' t).ne' hv
    refine (hS F Ω A x q hxZ).1 r hr hrv ?_ g hg
    have h8 : 8 * r ∣ 8 * c := Nat.mul_dvd_mul_left 8 (hrd.trans (hcd t ht))
    exact (Int.natCast_dvd_natCast.2 h8).trans (Nat.modEq_iff_dvd.1 hmod.symm)
  have hs1 : ∀ (j : E →+* Ω) (y : E), σ'.toRingEquiv (j y) = j y := fun j y => by
    simpa using σ'.commutes (⟨j y, hE' j y⟩ : E')
  have huT : u ∉ T := by
    intro ht
    have hle : normV u ≤ c := Nat.le_of_dvd hc0 (hcd u ht)
    have hcop : Nat.Coprime q (normV u) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => by
        have := Nat.le_of_dvd (normV_pos' u) hd
        omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((normV u : ℕ) : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hmem : (1 : 𝓞 E) ∈ u.asIdeal := by
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ huq) (Ideal.mul_mem_left _ _ (normV_mem u))
    exact (Ideal.ne_top_iff_one _).1 u.isPrime.ne_top hmem
  refine ⟨Q, ⟨⟨x, hxQ⟩, ⟨⟨q, hq.pos, ?_⟩, hspan, σ'.toRingEquiv, hs1, hσ'x⟩, ?_⟩, ?_, u, huT, A, hA, τ, hτ, ?_⟩
  · apply Subtype.ext
    simpa using hx
  · intro t ht A hA g hg
    exact hfixT _ t ht A hA g hg
  · intro t ht A hA g hg
    exact hfix E g (fun y => g.commutes y) (hfixT E t ht A hA g hg)
  · intro hf
    have := hf ⟨x, hxQ⟩
    exact hneg (hτx.symm.trans this)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshSplit
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem under_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {t : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A t) :
    IsPlaceOver A (t.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ F Ω]
  exact hA (algebraMap _ _ x)

private theorem res_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ g ∈ Dec (F := F) A :=
  GlobalTheory.AboveL.mem_dec_congr A _ g fun _ => rfl

private theorem res_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Ine (F := ℚ) A ↔ g ∈ Ine (F := F) A := by
  rw [mem_Ine, mem_Ine]
  exact Iff.rfl

private theorem eq_of_natCast_mem {p : ℕ} (hp : p.Prime) {a b : HeightOneSpectrum (𝓞 ℚ)}
    (ha : ((p : ℕ) : 𝓞 ℚ) ∈ a.asIdeal) (hb : ((p : ℕ) : 𝓞 ℚ) ∈ b.asIdeal) : a = b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal := by
    have h := Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv.symm (p := Ideal.span {(p : ℤ)})
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
  have key : ∀ c : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ c.asIdeal →
      c.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := fun c hc =>
    (hmax.eq_of_le c.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hc)).symm
  exact HeightOneSpectrum.ext ((key a ha).trans (key b hb).symm)

private theorem natCast_normV_mem (u : HeightOneSpectrum (𝓞 ℚ)) (h : (normV u).Prime) :
    ((normV u : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
  have hne : Nat.card (𝓞 ℚ ⧸ u.asIdeal) ≠ 0 := by
    have h0 := h.ne_zero
    unfold normV at h0
    exact h0
  haveI : Finite (𝓞 ℚ ⧸ u.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 ℚ ⧸ u.asIdeal)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold normV
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

private theorem core {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (hFC : FreshChar) (V : Subgroup (G F Ω)) (hV : IsOpen (V : Set (G F Ω)))
    (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (n : ℕ) (hn : 0 < n) :
    ∃ ψ : G F Ω →* ℂˣ, Good ψ.ker ∧
      (∀ (t : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A t →
        Ine (F := F) A ≤ ψ.ker ∨ Dec (F := F) A ≤ V) ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ V ∧
        ∃ τ ∈ Ine (F := F) A, orderOf (ψ τ) = n := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let res : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ
  have hres_inj : Function.Injective res := fun g h hgh => AlgEquiv.ext fun x => by
    have e := congrArg (fun σ : G ℚ Ω => σ x) hgh
    exact e
  have hVo : IsOpen ((V.map res : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) :=
    GlobalTheory.KLift.isOpen_map_restrictScalars V hV
  obtain ⟨ψ₀, hG₀, hpow₀, hT₀, u₀, hu₀T, hp, hu₀, hram⟩ := hFC ℚ Ω (V.map res) hVo
    ((fun t : HeightOneSpectrum (𝓞 F) => t.under (𝓞 ℚ)) '' T) (hT.image _) n hn
  have decV : ∀ A : ValuationSubring Ω, IsPlaceOver A u₀ → Dec (F := F) A ≤ V := by
    intro A hA g hg
    obtain ⟨h, hhV, hh⟩ := (hu₀ A hA).1 ((res_dec A g).2 hg)
    rwa [hres_inj hh] at hhV
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω u₀
  obtain ⟨u, hu⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := ℚ) (K := F) hA₀
  have eu : u.under (𝓞 ℚ) = u₀ := eq_of_isPlaceOver (under_place hu) hA₀
  have hunder : ∀ A : ValuationSubring Ω, IsPlaceOver A u → IsPlaceOver A u₀ := by
    intro A hA
    rw [← eu]
    exact under_place hA
  refine ⟨ψ₀.comp res, ?_, ?_, ?_, ?_, u, ?_, ?_⟩
  · refine ⟨hG₀.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω),
      Abelianization.commutator_subset_ker _, fun j c hc => ?_⟩
    exact hG₀.real j (res c) hc
  · intro t A hA
    by_cases hpt : ((normV u₀ : ℕ) : 𝓞 ℚ) ∈ (t.under (𝓞 ℚ)).asIdeal
    · right
      have e : t.under (𝓞 ℚ) = u₀ := eq_of_natCast_mem hp hpt (natCast_normV_mem u₀ hp)
      apply decV
      rw [← e]
      exact under_place hA
    · left
      intro g hg
      exact hram _ A (under_place hA) hpt _ ((res_ine A g).2 hg)
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hpow₀,
      MonoidHom.one_apply, MonoidHom.one_apply]
  · intro t ht A hA g hg
    exact hT₀ _ ⟨t, ht, rfl⟩ A (under_place hA) _ ((res_dec A g).2 hg)
  · intro huT
    exact hu₀T ⟨u, huT, eu⟩
  · intro A hA
    refine ⟨decV A (hunder A hA), ?_⟩
    obtain ⟨τ₀, hτ₀, ho⟩ := (hu₀ A (hunder A hA)).2
    obtain ⟨h, -, hh⟩ := (hu₀ A (hunder A hA)).1 (Ine_le_Dec A hτ₀)
    refine ⟨h, (res_ine A h).1 (by rw [show res h = τ₀ from hh]; exact hτ₀), ?_⟩
    show orderOf (ψ₀ (res h)) = n
    rw [show res h = τ₀ from hh]
    exact ho

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshSplit :
    FreshChar → FreshSplit := by
  intro hFC E Ω _ _ _ _ _ _ U hU T hT n hn
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ψ, h1, h2, h3, h4, u, hu, h5⟩ := core hFC (U ⊓ fixGrp (maximalRealSubfield E) Ω E)
    (hU.inter (isOpen_fixGrp _ Ω E)) T hT n hn
  exact ⟨ψ, h1, fun t A hA => (h2 t A hA).imp_right fun h g hg => (h hg).2, h3, h4, u, hu,
    fun A hA => ⟨fun g hg => ((h5 A hA).1 hg).1, (h5 A hA).2⟩⟩
end

