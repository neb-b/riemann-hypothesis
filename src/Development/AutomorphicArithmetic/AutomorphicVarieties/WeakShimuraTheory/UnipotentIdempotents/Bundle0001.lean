module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BarFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem open_bar {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing O] [IsLocalRing O]
    (γ : Γ →* Oˣ) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (h : ∀ g ∈ H, residue O (γ g : O) = 1) :
    IsOpen {g : Γ | residue O (γ g : O) = 1} := by
  have h2 : H ≤ ((Units.map (residue O).toMonoidHom).comp γ).ker := fun g hg => Units.ext (h g hg)
  have h3 := Subgroup.isOpen_mono h2 hH
  convert h3 using 1
  ext g
  exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

theorem UpperTheory.V.Ws.Lk.barFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → (∀ i, IsOpen {g : G ℚ Ω | Raw.bar (D.ps i) g = 1}) ∧ IsOpen {g : G ℚ Ω | Raw.bar D.om g = 1} ∧ ∀ A, Raw.Away D.S A → ∀ g ∈ Ine (F := ℚ) A, (∀ i, D.ps i g = 1) ∧ D.rbar g = 1 := by
  intro Ω _ _ _ l _ c D h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr, ho, hu⟩ := facts D h
  refine ⟨fun i => open_bar _ _ hr fun g hg => ?_, open_bar _ _ ho fun g hg => ?_, fun A hA g hg => ?_⟩
  · have h1 : D.rbar g = 1 := hg
    simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrFun (congrFun h1 i) i
  · rw [MonoidHom.mem_ker.1 hg, Units.val_one, map_one]
  · have h2 : ∀ i, D.ps i g = 1 := fun i => hu i A hA hg
    refine ⟨h2, ?_⟩
    ext i j
    by_cases e : i = j
    · subst e
      simp [Raw.rbar, Raw.r0, diagRep, mapRep, h2]
    · simp [Raw.rbar, Raw.r0, diagRep, mapRep, e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BetaCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open scoped Pointwise

namespace UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.1 hl.out
  have h2 := (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).2 h
  simpa using h2

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  show _ ↔ (n : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  rw [Ideal.mem_span_singleton]
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hdvd : ((l : ℕ) : 𝓞 ℚ) ∣ (n : 𝓞 ℚ) ↔ (l : ℤ) ∣ n := by
    rw [show ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) by simp,
      show (n : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n by simp, map_dvd_iff]
  rw [hdvd]
  constructor
  · intro hv
    by_contra hnd
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    have h1 : A.valuation ((a * l + b * n : ℤ) : Ω) < 1 := by
      push_cast
      apply lt_of_le_of_lt (A.valuation.map_add _ _)
      apply max_lt
      · rw [map_mul]
        calc A.valuation (a : Ω) * A.valuation ((l : ℕ) : Ω) ≤ 1 * A.valuation ((l : ℕ) : Ω) :=
              mul_le_mul' (hle a) le_rfl
          _ < 1 := by rw [one_mul]; exact hA
      · rw [map_mul]
        calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' (hle b) le_rfl
          _ < 1 := by rw [one_mul]; exact hv
    rw [hab] at h1
    simp at h1
  · rintro ⟨y, rfl⟩
    push_cast
    rw [map_mul]
    calc A.valuation ((l : ℕ) : Ω) * A.valuation (y : Ω) ≤ A.valuation ((l : ℕ) : Ω) * 1 :=
          mul_le_mul' le_rfl (hle y)
      _ < 1 := by rw [mul_one]; exact hA

end UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

open UpperTheory.V.Ws.Lk.BetaCyclotomicPlace in
theorem UpperTheory.V.Ws.Lk.betaCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ Ω) [NumberField K], Module.finrank ℚ K = 2 → ∀ A₀ : ValuationSubring Ω, A₀.valuation (l : Ω) < 1 → ∀ β : G K Ω →* (PadicAlgCl l)ˣ, (∀ σ ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = σ * resQ K s * σ⁻¹ → β s * β s' = 1) → ∀ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) → (∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A₀) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l])) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := K) A, (β s ^ 2 * cycBar K Ω l s ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ K _ hK A₀ hA₀ β hconj U hU hcyc A hA
  have hn : U.index ≠ 0 := by
    haveI : Finite (G K Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  have hpow : ∀ s : G K Ω, s ^ U.index.factorial ∈ U := fun s =>
    Subgroup.pow_mem_of_index_ne_zero_of_dvd hn s (fun m h1 h2 => Nat.dvd_factorial h1 h2)
  have hkpos : 0 < U.index.factorial := Nat.factorial_pos _
  have hval : ∀ t : G K Ω, ((cycBar K Ω l t : (Qbar l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l t : ℤ_[l]) := fun t => rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A₀ hA₀) (isPlaceOver_vQ A hA)
  by_cases hσK : σ ∈ K.fixingSubgroup
  · refine ⟨1, U.index.factorial, hkpos, odd_one, ?_⟩
    have hB : ∀ x ∈ K, x ∈ A ↔ x ∈ A₀ := by
      intro x hx
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ • x = x := (K.fixingSubgroup.inv_mem hσK) ⟨x, hx⟩
      rw [hfix]
    intro s hs
    have ht : s ^ U.index.factorial ∈ U ⊓ Ine (F := K) A := ⟨hpow s, pow_mem hs _⟩
    have h1 : β (s ^ U.index.factorial) ^ 2 = cycBar K Ω l (s ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A hB _ ht, hval])
    have e1 : (β s ^ 2 * cycBar K Ω l s ^ (-1 : ℤ)) ^ U.index.factorial =
        β (s ^ U.index.factorial) ^ 2 * (cycBar K Ω l (s ^ U.index.factorial))⁻¹ := by
      rw [map_pow, map_pow, zpow_neg, zpow_one]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e1, h1, mul_inv_cancel]
  · refine ⟨-1, U.index.factorial, hkpos, ⟨-1, by norm_num⟩, ?_⟩
    haveI hN : K.fixingSubgroup.Normal := by
      refine (InfiniteGalois.normal_iff_isGalois K).2 ?_
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      exact isGalois_iff.2 ⟨Algebra.IsSeparable.of_integral _ _, Algebra.IsQuadraticExtension.normal ℚ K⟩
    intro s hs
    have hg : resQ K s ∈ Ine (F := ℚ) A := (resQ_Ine K A s).1 hs
    have hlift : IsLift (RingEquiv.refl ℚ) (σ : Ω ≃+* Ω) := fun y => by simp
    have hg' : conjGal hlift (resQ K s) ∈ Ine (F := ℚ) A₀ := by
      refine conjGal_mem_Ine hlift (fun x => ?_) hg
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      show σ⁻¹ • σ • x ∈ A₀ ↔ x ∈ A₀
      rw [inv_smul_smul]
    have heq : conjGal hlift (resQ K s) = σ⁻¹ * resQ K s * σ := by
      ext x
      rfl
    have hmem : σ⁻¹ * resQ K s * σ ∈ K.fixingSubgroup := by
      have h' := hN.conj_mem _ (resQ_mem K s) σ⁻¹
      rwa [inv_inv] at h'
    obtain ⟨s', hs'⟩ := exists_resQ hmem
    have hs'I : s' ∈ Ine (F := K) A₀ := (resQ_Ine K A₀ s').2 (by rw [hs', ← heq]; exact hg')
    have hσ' : σ⁻¹ ∉ K.fixingSubgroup := fun h' => hσK (by simpa using K.fixingSubgroup.inv_mem h')
    have hbb : β s * β s' = 1 := hconj σ⁻¹ hσ' s s' (by rw [hs', inv_inv])
    have hcy : cycBar K Ω l s' = cycBar K Ω l s := by
      show Units.map _ (cycZ K Ω l s') = Units.map _ (cycZ K Ω l s)
      have hz : cycZ ℚ Ω l (σ⁻¹ * resQ K s * σ) = cycZ ℚ Ω l (resQ K s) := by
        rw [map_mul, map_mul, map_inv, mul_comm (cycZ ℚ Ω l σ)⁻¹, inv_mul_cancel_right]
      rw [← resQ_cyc, ← resQ_cyc, hs', hz]
    have ht' : s' ^ U.index.factorial ∈ U ⊓ Ine (F := K) A₀ := ⟨hpow s', pow_mem hs'I _⟩
    have h1 : β (s' ^ U.index.factorial) ^ 2 = cycBar K Ω l (s' ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A₀ (fun _ _ => Iff.rfl) _ ht', hval])
    have hbs : β s = (β s')⁻¹ := eq_inv_of_mul_eq_one_left hbb
    have e2 : (β s ^ 2 * cycBar K Ω l s ^ (-(-1) : ℤ)) ^ U.index.factorial =
        (β (s' ^ U.index.factorial) ^ 2)⁻¹ * cycBar K Ω l (s' ^ U.index.factorial) := by
      rw [neg_neg, zpow_one, hbs, ← hcy, map_pow, map_pow]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e2, h1, inv_mul_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CcOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.ccOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ → resQ T.L g' = σ * resQ T.L g * σ⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  refine ⟨(s.c : Ω ≃ₐ[W.Lp T.L] Ω).restrictScalars ℚ, ?_, ?_⟩
  · intro hfix
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hfix
    have hreal : NumberField.ComplexEmbedding.IsReal (j.comp (T.K.val : T.K →+* Ω)) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hx := hfix (x : Ω) x.2
      change s.c (x : Ω) = (x : Ω) at hx
      simp only [RingHom.comp_apply]
      rw [← hj]
      change j (s.c (x : Ω)) = j (x : Ω)
      rw [hx]
    exact NumberField.IsTotallyComplex.complexEmbedding_not_isReal _ hreal
  · intro g g' h
    ext x
    have hx := congrArg (fun f : G (W.Lp T.L) Ω => f x) h
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem exists_conj (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] :
    ∃ c : G (W.Lp L) Ω, ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  let j : Ω →ₐ[L] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := (j : Ω →+* ℂ).toAlgebra
  haveI : IsScalarTower (W.Lp L) Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes (x : L)).symm
  let s : ℂ →ₐ[W.Lp L] ℂ :=
    { starRingEnd ℂ with commutes' := fun x => (mem_maximalRealSubfield_iff (x : L)).1 x.2 φ }
  exact ⟨s.restrictNormal' Ω, j, fun x => s.restrictNormal_commutes Ω x⟩

private theorem ne_top {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) : A ≠ ⊤ := by
  rintro rfl
  refine v.ne_bot (eq_bot_iff.2 fun x hx => ?_)
  have h1 := (h x).2 hx
  rw [valuation_lt_one_iff'] at h1
  have h2 := h1.2.resolve_right fun h' => h' (ValuationSubring.mem_top _)
  simpa using h2

private theorem val_nat {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) (q : ℕ) : A.valuation (q : Ω) < 1 ↔ (q : 𝓞 k) ∈ v.asIdeal := by
  simpa using h (q : 𝓞 k)

private theorem fin_nat {k : Type} [Field k] [NumberField k] {q : ℕ} (hq : q ≠ 0) :
    {v : W.Plc k | (q : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {(q : 𝓞 k)}) (by simpa using hq)
  simpa [Ideal.dvd_span_singleton] using h

private theorem eq_of_mem {k : Type} [Field k] [NumberField k] {v : W.Plc k} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : 𝓞 k) ∈ v.asIdeal) (h2 : (q : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := 𝓞 k) ((Nat.coprime_primes hp hq).2 hne)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)))

theorem UpperTheory.V.Ws.Lk.mkSet :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], l ≠ 2 → (∀ A : ValuationSubring Ω, Ine (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → l ∈ S → (∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ A₀ : W.Vl l L → ValuationSubring Ω, (∀ v, IsPlaceOver (A₀ v) v.1) → ∀ (v₀ : W.Plc (W.Lp L)) (B : ValuationSubring Ω) (p : ℕ), p.Prime → p ≠ 2 → p ∉ S → ¬ (p : ℤ) ∣ discr L → ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v₀.asIdeal → normV v₀ = p → IsPlaceOver B v₀ → Dec (F := W.Lp L) B ≤ (W.resP L Ω).range → ∃ s : W.HidaSetting l L Ω, (∀ v : W.Vl l L, s.A v = A₀ v) ∧ s.A s.v0 = B ∧ s.S.Finite ∧ (∀ q ∈ S, ¬ B.valuation (q : Ω) < 1) ∧ ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ s.S → ∀ q ∈ S, ¬ A.valuation (q : Ω) < 1 := by
  classical
  intro l hl L Ω _ _ _ _ _ _ hodd hunr S hS hlS hsp A₀ hA₀ v₀ B p hp hp2 hpS hpd hpv hnv hB hBs
  have hq0 : ∀ q ∈ S, (q : 𝓞 (W.Lp L)) ∉ v₀.asIdeal := fun q hq h =>
    hpS (eq_of_mem hp (hS q hq) hpv h ▸ hq)
  obtain ⟨c, hc⟩ := exists_conj L Ω
  have hex : ∀ v : W.Plc (W.Lp L), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧
      (∀ h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal, A = A₀ ⟨v, h⟩) ∧ (v = v₀ → A = B) := by
    intro v
    by_cases h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact ⟨A₀ ⟨v, h⟩, hA₀ ⟨v, h⟩, fun _ => rfl, fun e => absurd (e ▸ h) (hq0 l hlS)⟩
    · by_cases e : v = v₀
      · exact ⟨B, e ▸ hB, fun h' => absurd h' h, fun _ => rfl⟩
      · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
        exact ⟨A, hA, fun h' => absurd h' h, fun e' => absurd e' e⟩
  choose A hA hAl hA0 using hex
  choose w hw using fun v => (places L Ω l (A v)).1 (ne_top (hA v))
  have hfin : {v : W.Plc (W.Lp L) | (∃ q ∈ S, (q : 𝓞 (W.Lp L)) ∈ v.asIdeal) ∧ (l : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite :=
    (S.finite_toSet.biUnion fun q hq => fin_nat (k := W.Lp L) (hS q hq).ne_zero).subset fun v hv => by
      obtain ⟨⟨q, hq, h⟩, -⟩ := hv
      exact Set.mem_biUnion hq h
  refine ⟨{ odd := hodd, unr := fun B _ _ => hunr B, c := c, hc := hc, w := w, A := A, hw := hw, hA := hA,
            St := hfin.toFinset, St_l := fun u hu => (hfin.mem_toFinset.1 hu).2, v0 := v₀, v0_St := ?_, p := p,
            p_prime := hp, p_odd := hp2, p_ne := fun e => hpS (e ▸ hlS), p_unr := hpd, norm_v0_eq_one := hnv,
            split := ?_ }, fun v => hAl v.1 v.2, hA0 v₀ rfl, ?_, fun q hq h => hq0 q hq ((val_nat hB q).1 h), ?_⟩
  · intro h
    obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
    exact hq0 q hq h
  · rintro v (h | h | rfl)
    · exact hsp l hlS _ ((val_nat (hA v) l).2 h)
    · obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
      exact hsp q hq _ ((val_nat (hA v) q).2 h)
    · rw [hA0 v rfl]; exact hBs
  · exact (fin_nat hl.out.ne_zero).union ((Finset.finite_toSet _).union (Set.finite_singleton v₀))
  · intro A' v hv hvS q hq h
    refine hvS ?_
    by_cases h' : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl h'
    · exact Or.inr (Or.inl (hfin.mem_toFinset.2 ⟨⟨q, hq, (val_nat hv q).1 h⟩, h'⟩))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.ExistsCharacterOfDirichletData
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {n M : ℕ} [NeZero n] (h : n ∣ M) {s : G ℚ Ω}
    (hs : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω n s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have h1 : s ζ = ζ := hs ζ (by obtain ⟨k, rfl⟩ := h; rw [pow_mul, hζ.pow_eq_one, one_pow])
  have h2 := Chr.cls_spec (k := ℚ) n s ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 : ζ ^ ((Chr.cls ℚ Ω n s : ZMod n)).val = ζ ^ (1 : ℕ) := by rw [pow_one]; exact h2.symm
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, NeZero.pos n, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h3
  ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω n s : ZMod n)), (ZMod.natCast_eq_natCast_iff _ _ _).2 h3,
    Nat.cast_one]

private theorem exp_ex {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) :
    ∃ k m : ℕ, l.Coprime m ∧ n ∣ k * m ∧ ∀ m' : ℕ, l.Coprime m' → k ≡ 1 [MOD Nat.gcd n m'] := by
  obtain ⟨a, m, hlm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.one_lt.ne'
  have hcop : l.Coprime m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  have hcop2 : (l ^ a).Coprime m := Nat.Coprime.pow_left a hcop
  let k := Nat.chineseRemainder hcop2 0 1
  have hk0 : k ≡ 0 [MOD l ^ a] := k.2.1
  have hk1 : k ≡ 1 [MOD m] := k.2.2
  refine ⟨k, m, hcop, ?_, ?_⟩
  · exact Nat.mul_dvd_mul (Nat.modEq_zero_iff_dvd.1 hk0) dvd_rfl
  · intro m' hm'
    refine Nat.ModEq.of_dvd ?_ hk1
    have hg : (Nat.gcd (l ^ a * m) m').Coprime (l ^ a) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.pow_right a hm'.symm)
    exact hg.dvd_of_dvd_mul_left (Nat.gcd_dvd_left _ _)

private theorem cyclotomicClass_eq_of_isComplexConj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] {σ τ : G ℚ Ω}
    (hσ : IsCC σ) (hτ : IsCC τ) : Chr.cls ℚ Ω N σ = Chr.cls ℚ Ω N τ := by
  have key : ∀ {ρ : G ℚ Ω}, IsCC ρ → ∀ ζ : Ω, ζ ^ N = 1 → ρ ζ = ζ⁻¹ := by
    rintro ρ ⟨j, hj⟩ ζ hζ
    apply j.injective
    rw [hj, map_inv₀, Complex.inv_eq_conj]
    exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne N)
  have h1 : Chr.cls ℚ Ω N (τ⁻¹ * σ) = 1 := cls_one (dvd_refl N) (fun ζ hζ => by
    rw [AlgEquiv.mul_apply, key hσ ζ hζ, ← key hτ ζ hζ]
    exact AlgEquiv.aut_inv τ ▸ τ.symm_apply_apply ζ)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

private theorem exists_character_of_dirichlet_data {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (hD : D.Good) {e N : ℕ} [NeZero N] {ψ : DirichletCharacter c.O N} {n' p₁ m₀ : ℕ}
    (hO : Aut.OfChar D e ψ n' p₁ m₀) :
    ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧ (∀ σ, IsCC σ → χ σ = 1) ∧
      (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
  obtain ⟨-, hpsi, -, hp1, ξ', ξ₀, -, -, -, hxi⟩ := hO
  haveI := hp1
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  have hl2 : l ≠ 2 := hD.l_odd
  have hn0 : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
  obtain ⟨k, m, hlm, hnkm, hk⟩ := exp_ex hlp hn0
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.1 (hD.om_bar σ)⟩
  obtain ⟨hker1, hker2, -, -, hcc, hunr, -, -⟩ := (omT Ω l c).2 D.om hom
  obtain ⟨mξ, hlξ, hξm⟩ := hD.xi_ord
  have hψn : ∀ g, D.ψ g ^ Fintype.card (ZMod N)ˣ = 1 := by
    intro g
    rw [hpsi]
    show (MulChar.toUnitHom ψ) (Chr.cls ℚ Ω N g) ^ Fintype.card (ZMod N)ˣ = 1
    rw [← map_pow, pow_card_eq_one, map_one]
  have hψk : ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → D.ψ g ^ k = D.ψ g := by
    rintro g ⟨m', hm', hg⟩
    have hd : orderOf (D.ψ g) ∣ Nat.gcd (Fintype.card (ZMod N)ˣ) m' :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hψn g)) (orderOf_dvd_of_pow_eq_one hg)
    conv_rhs => rw [← pow_one (D.ψ g)]
    exact pow_eq_pow_iff_modEq.2 ((hk m' hm').of_dvd hd)
  have hψ1 : D.ψ ^ Fintype.card (ZMod N)ˣ = 1 := MonoidHom.ext fun g => by rw [MonoidHom.pow_apply, hψn g, MonoidHom.one_apply]
  refine ⟨D.om ^ (D.e + 3) * D.ξ * D.ψ ^ k, l * N * p₁ * 2 ^ n', (l - 1) * mξ * m, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hlp.ne_zero (NeZero.ne N)) (NeZero.ne p₁)) (pow_ne_zero _ two_ne_zero))
  · intro s hs
    have hl' : Chr.cls ℚ Ω l s = 1 := cls_one ⟨N * p₁ * 2 ^ n', by ring⟩ hs
    have hN' : Chr.cls ℚ Ω N s = 1 := cls_one ⟨l * p₁ * 2 ^ n', by ring⟩ hs
    have hp' : Chr.cls ℚ Ω p₁ s = 1 := cls_one ⟨l * N * 2 ^ n', by ring⟩ hs
    have hq' : Chr.cls ℚ Ω (2 ^ n') s = 1 := cls_one ⟨l * N * p₁, by ring⟩ hs
    have h1 : D.om s = 1 := by
      have : s ∈ (Chr.cls ℚ Ω l).ker := hl'
      rw [← hker2] at this
      exact this
    have h2 : D.ξ s = 1 := by
      rw [hxi, MonoidHom.mul_apply]
      simp only [Chr.dirG, MonoidHom.comp_apply, hp', hq', map_one, mul_one]
    have h3 : D.ψ s = 1 := by
      rw [hpsi]
      simp only [Chr.dirG, MonoidHom.comp_apply, hN', map_one]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, h1, h2, h3, one_pow, mul_one]
  · have h : l.Coprime (l - 1) := (Nat.Prime.coprime_iff_not_dvd hlp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos))
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right h hlξ) hlm
  · obtain ⟨t, ht⟩ := hnkm
    have a1 : (D.om ^ (D.e + 3)) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show (D.e + 3) * ((l - 1) * mξ * m) = (l - 1) * ((D.e + 3) * mξ * m) by ring, pow_mul,
        hD.om_pow, one_pow]
    have a2 : D.ξ ^ ((l - 1) * mξ * m) = 1 := by
      rw [show (l - 1) * mξ * m = mξ * ((l - 1) * m) by ring, pow_mul, hξm, one_pow]
    have a3 : (D.ψ ^ k) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show k * ((l - 1) * mξ * m) = Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) by
        rw [show Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) = (Fintype.card (ZMod N)ˣ * t) * ((l - 1) * mξ) by ring,
          ← ht]
        ring, pow_mul, hψ1, one_pow]
    rw [mul_pow, mul_pow, a1, a2, a3, mul_one, mul_one]
  · intro σ hσ
    have ho : D.om σ = -1 := hcc σ hσ hl2
    have hx : D.ξ σ = -1 := by
      rw [← hD.xi_odd, hxi]
      simp only [MonoidHom.mul_apply, Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
    have hchi : chiO ℚ Ω l c.O D.cc = -1 := by
      have h := IsConjOm.cyc (E := ℚ) (l := l) (σ := MulSemiringAction.toRingAut (G ℚ Ω) Ω D.cc) hD.isCC
      show Units.map _ (cycZ ℚ Ω l D.cc) = -1
      rw [show cycZ ℚ Ω l D.cc = -1 from h]
      ext
      simp
    have hP := hD.Psi_even
    simp only [Raw.Psi, Chr.Psi, MonoidHom.mul_apply] at hP
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) D.cc = (chiO ℚ Ω l c.O D.cc) ^ (D.e : ℤ) from rfl, hchi, zpow_natCast] at hP
    have hψσ : D.ψ σ = (-1) ^ D.e := by
      rw [hpsi] at hP ⊢
      have : Chr.dirG ℚ Ω ψ σ = Chr.dirG ℚ Ω ψ D.cc := by
        simp only [Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
      rw [this]
      rw [← mul_right_inj ((-1 : c.Oˣ) ^ D.e), hP, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hsq : D.ψ σ ^ k = D.ψ σ := hψk σ ⟨2, (Nat.coprime_primes hlp Nat.prime_two).2 hl2,
      by rw [hψσ, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]⟩
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [ho, hx, hsq, hψσ, ← pow_succ, ← pow_add]
    exact Even.neg_one_pow ⟨D.e + 2, by ring⟩
  · intro A hA
    have h1 : Ine A ≤ D.om.ker := hunr A (hA l hD.l_mem)
    have h2 := hD.xi_unr A hA
    have h3 := hD.psi_unr A hA
    intro x hx
    have a1 : D.om x = 1 := h1 hx
    have a2 : D.ξ x = 1 := h2 hx
    have a3 : D.ψ x = 1 := h3 hx
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, a1, a2, a3, one_pow, mul_one]
  · intro g hg
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [hψk g hg]

theorem UpperTheory.V.Ws.Lk.etaEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, (Ctx2 D ∨ Ctx3 D) → ∃ (η : G ℚ Ω →* (PadicAlgCl l)ˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N η ∧ l.Coprime m ∧ η ^ m = 1 ∧ (∀ σ, IsCC σ → η σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ η.ker) ∧ ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → η g * toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g = 1 := by
  intro Ω _ _ _ l _ c D hC
  have key : ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧
      (∀ σ, IsCC σ → χ σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
    rcases hC with ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩ | ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩
    · exact exists_character_of_dirichlet_data hD hO
    · exact exists_character_of_dirichlet_data hD hO
  obtain ⟨χ, N, m, hN, hK, hm, hχm, hcc, hA, hg⟩ := key
  have hval : ∀ g, (toQ χ)⁻¹ g = (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (χ g))⁻¹ :=
    fun g => rfl
  refine ⟨(toQ χ)⁻¹, N, m, hN, ?_, hm, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hval, hK s hs, map_one, inv_one]
  · ext g
    rw [MonoidHom.pow_apply, hval, inv_pow, ← map_pow, ← MonoidHom.pow_apply, hχm]
    simp
  · intro σ hσ
    rw [hval, hcc σ hσ, map_one, inv_one]
  · intro A hAw x hx
    have h1 : χ x = 1 := hA A hAw hx
    rw [MonoidHom.mem_ker, hval, h1, map_one, inv_one]
  · intro g hg'
    rw [hval, show toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g =
      Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) ((D.om ^ (D.e + 3) * D.ξ * D.ψ) g) from rfl,
      ← hg g hg', inv_mul_cancel]
end

