module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ReductionToDirichletCharAnyLevelOfLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem not_valuation_lt_one_of_ne_of_valuation_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hB
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hp hq).2 hpq
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) = 1 := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this
  have ha : A.valuation (a : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A a)
  have hb : A.valuation (b : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A b)
  have hx : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hA
  have hy : A.valuation ((b : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (q : Ω) ≤ 1 * A.valuation (q : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hB
  have hs := Valuation.map_add_lt A.valuation hx hy
  rw [h1, map_one] at hs
  exact lt_irrefl _ hs

theorem UpperTheory.V.HV.gdOfHost :
    ∀ (h : Host) (t : ℕ), h.Big t → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra (Kstar (pK h.chi)) Ω] (l : ℕ) [Fact l.Prime] (e : ℕ), l ≠ 2 → 0 < e → e < t → h.CaseI l e →
      ∀ (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → PsiEven e ψ → GD Ω (Kstar (pK h.chi)) l e ψ := by
  intro h t hBig Ω _ _ _ _ l _ e hl2 he0 het hI O _ _ ψ hψ hpar
  have hB := UpperTheory.V.HV.bchiFacts h t hBig
  have hpB : pK h.chi ∈ Bchi h.chi := hB.2.1
  have hpPrime : Nat.Prime (pK h.chi) := (prime_of_mem_Bchi hpB).1
  have hp4 : pK h.chi % 4 = 3 := by
    have hne : {p : ℕ | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime h.chi.N}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      have h0 : pK h.chi = 0 := by
        unfold pK
        rw [hc, Nat.sInf_empty]
      exact hpPrime.ne_zero h0
    exact (Nat.sInf_mem hne).2.1
  have hK := UpperTheory.V.HV.kstar (pK h.chi) hpPrime hp4
  have hlB : l ∉ Bchi h.chi := hI.1
  have hl := hB.2.2.2.2 l (Fact.out) hl2 hlB
  have hC := (UpperTheory.V.HV.cases h t hBig O ψ hψ l e (Fact.out) hl2 he0 het).1 hlB
  have hlp : l ≠ pK h.chi := hl.2.2.2.1
  have hpN : ¬ pK h.chi ∣ h.N := hB.2.2.1
  refine ⟨hl2, he0, ?_, hC.1, hC.2.1, hpar, hK.2.2.1, hK.2.1, ?_, ?_, ?_, hI.2⟩
  · rw [even_iff_two_dvd]
    exact (dvd_pow_self 2 (by omega : h.ex + 2 ≠ 0)).trans h.two_pow_dvd
  · rw [hK.1]
    have habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi := by simp
    rw [habs]
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime l)).1 hdvd with h1 | h1
    · exact hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpPrime).1 h1)
    · exact hl.2.2.2.2.1 h1
  · rw [hK.1]
    have habs : (-(pK h.chi : ℤ)).natAbs = pK h.chi := by simp
    rw [habs]
    exact (Nat.Prime.coprime_iff_not_dvd hpPrime).2 hpN
  · intro hle
    obtain ⟨A, hA⟩ := (UpperTheory.V.Chr.placesQ Ω).1 (pK h.chi) hpPrime
    apply UpperTheory.V.HV.kstarRam (pK h.chi) hpPrime hp4 Ω A hA
    intro x hx
    apply hle
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have hlA : ¬ A.valuation (l : Ω) < 1 := not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) l hpPrime Fact.out (Ne.symm hlp) hA
      have := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlA) hx
      rw [MonoidHom.mem_ker] at this ⊢
      simp [cycMod, this]
    · have hNA : ¬ A.valuation (h.N : Ω) < 1 := by
        rw [(UpperTheory.V.Chr.placesQ Ω).2.1 A h.N (NeZero.ne _)]
        rintro ⟨q, hqN, hq⟩
        have hqP : Nat.Prime q := Nat.prime_of_mem_primeFactors hqN
        have hne : pK h.chi ≠ q := by
          rintro rfl
          exact hpN (Nat.dvd_of_mem_primeFactors hqN)
        exact not_valuation_lt_one_of_ne_of_valuation_lt_one A (pK h.chi) q hpPrime hqP hne hA hq
      have := ((UpperTheory.V.Chr.clsFacts ℚ Ω h.N).2.2.2.2 A hNA) hx
      rw [MonoidHom.mem_ker] at this ⊢
      simp [UpperTheory.V.Chr.dirG, this]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.RedAll
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.redAll :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, (Vlen Ω c e ψ + (lossAll l N H.index e : ℕ∞) * eO l c.O) := by
  intro E _ _ _ N _ H hH l _ hl2 c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI : NeZero (Nat.totient N) := ⟨(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩
  haveI : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    refine HasEnoughRootsOfUnity.of_dvd c.O (n := Nat.totient N) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => ?_)
    induction g using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, ZMod.pow_totient, QuotientGroup.mk_one]
  have hfr := (Chr.levGal E N H hH).2.1
  have key := (Chr.reduction_to_dirichletChar_any_level_of_le E c.O D Ω hH hl2 he T (N' := N) (NeZero.ne N)).1 hT
  rw [hfr] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SumOut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem exists_closure : ∃ (Q : Type) (_ : Field Q) (_ : CharZero Q), IsAlgClosure ℚ Q := by
  refine ⟨AlgebraicClosure ℚ, inferInstance, inferInstance,
    (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).2 ⟨inferInstance, ?_⟩⟩
  have h := AlgebraicClosure.isAlgebraic ℚ
  convert h using 1

private theorem card_small (S : Finset Nat.Primes) (n : ℕ) (h : ∀ l ∈ S, (l : ℕ) ≤ n) : S.card ≤ n := by
  have key : S.card ≤ (Finset.Icc 1 n).card := by
    apply Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
    · intro l hl
      have h1 := h l hl
      have h2 := l.2.one_lt
      simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_Icc, Finset.mem_coe]
      omega
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  simpa using key

private theorem final_le (M t : ℝ) (a b : ℕ) (hM : 2 ≤ M) (ht : t ≤ M) :
    t * (M ^ a + 2 * M * M ^ b) ≤ M ^ (a + b + 4) := by
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hpos : 0 ≤ M ^ a + 2 * M * M ^ b := by positivity
  have h1 : t * (M ^ a + 2 * M * M ^ b) ≤ M * (M ^ a + 2 * M * M ^ b) :=
    mul_le_mul_of_nonneg_right ht hpos
  have hA : M ^ (a + 1) ≤ M ^ (a + b + 3) := pow_le_pow_right₀ hM1 (by omega)
  have hB : M ^ (b + 2) ≤ M ^ (a + b + 2) := pow_le_pow_right₀ hM1 (by omega)
  have hY : 0 ≤ M ^ (a + b + 2) := by positivity
  have hX : 0 ≤ M ^ (a + b + 3) := by positivity
  have eX : M ^ (a + b + 3) = M * M ^ (a + b + 2) := by ring
  have e4 : M ^ (a + b + 4) = M * M ^ (a + b + 3) := by ring
  have eL : M * (M ^ a + 2 * M * M ^ b) = M ^ (a + 1) + 2 * M ^ (b + 2) := by ring
  have k1 : 0 ≤ (M - 2) * M ^ (a + b + 2) := mul_nonneg (by linarith) hY
  have k2 : 0 ≤ (M - 1) * M ^ (a + b + 3) := mul_nonneg (by linarith) hX
  rw [e4]
  nlinarith

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.HV.sumOut :
    CountI → CountZ → CountII → CountIII → SumOut := by
  classical
  intro hI hZ hII hIII χ
  obtain ⟨C1, r₁, r₂, hr₁, hr₂, hI⟩ := hI χ
  obtain ⟨CZ, hZ⟩ := hZ χ
  obtain ⟨C2, hII⟩ := hII χ
  obtain ⟨C3, hIII⟩ := hIII χ
  refine ⟨C1 + 3 * max CZ (max C2 C3) + 4, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ hq1 hd hq1' hd' t ht2 hbig E _ _ _ hE Ω _ _ _ ld S hS
  subst hχ
  obtain ⟨Ω0, iF, iC, iA⟩ := exists_closure
  set K := max CZ (max C2 C3) with hK
  have hN1 : (1:ℝ) ≤ (h.N : ℝ) := by exact_mod_cast h.N_pos
  have ht2' : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht2
  set M : ℝ := (h.N : ℝ) * t with hM
  have hM2 : 2 ≤ M := by nlinarith
  have htM : (t:ℝ) ≤ M := by nlinarith
  have hNM : (h.N:ℝ) ≤ M := by nlinarith
  haveI : NeZero h.N.totient := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  choose c hc using fun l : Nat.Primes => exists_coef (l : ℕ) h.N.totient
  have hfacts := fun (l : Nat.Primes) (hl : l ∈ S) =>
    (bchiFacts h t hbig).2.2.2.2 (l:ℕ) l.2 (hS l hl).1 (hS l hl).2
  have hother : ∀ l ∈ S, ∀ e, 0 < e → e < t → ¬ h.CaseI (l:ℕ) e →
      ∀ ψ ∈ h.X (c l) e, VLe Ω0 (c l) e ψ (M ^ (3 * K)) := by
    intro l hl e he1 he2 hn ψ hψ
    have hl2 := (hS l hl).1
    have hlB := (hS l hl).2
    have hchar := ((Host.mem_X h).1 hψ).1
    have hc4 := ((UpperTheory.V.HV.cases h t hbig (↥(c l).O) ψ hchar (l:ℕ) e l.2 hl2 he1 he2).1 hlB).2.2.2.2.2
    have hdv : (l:ℕ) - 1 ∣ 2 * e := by
      simp only [Host.CaseI, not_and, not_not] at hn
      exact hn hlB
    have hle := (hfacts l hl).2.2.2.2.2.2.2 e he1 he2 hdv
    have hl' : ((l:ℕ):ℝ) ≤ 2 * t := by exact_mod_cast hle.2.1
    have he' : (e:ℝ) ≤ t := by exact_mod_cast he2.le
    have hl1 : (1:ℝ) ≤ (l:ℕ) := by exact_mod_cast l.2.one_lt.le
    have he1' : (1:ℝ) ≤ e := by exact_mod_cast he1
    have hbase1 : (1:ℝ) ≤ ((l:ℕ):ℝ) * h.N * e := by
      have a1 := mul_le_mul hl1 hN1 zero_le_one (by positivity)
      have a2 := mul_le_mul a1 he1' zero_le_one (by positivity)
      simpa using a2
    have hbase : ((l:ℕ):ℝ) * h.N * e ≤ M ^ 3 := by
      have a1 : ((l:ℕ):ℝ) * h.N ≤ (2 * t) * h.N := mul_le_mul_of_nonneg_right hl' (by positivity)
      have a2 : ((l:ℕ):ℝ) * h.N * e ≤ (2 * t) * h.N * t :=
        mul_le_mul a1 he' (by positivity) (by positivity)
      have hM0 : 0 ≤ M := by linarith
      have a4 : 2 * M * t ≤ M * M * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM2 hM0) (by positivity)
      have a5 : M * M * t ≤ M * M * M := mul_le_mul_of_nonneg_left htM (by positivity)
      have a3 : (2 * (t:ℝ)) * h.N * t = 2 * M * t := by rw [hM]; ring
      calc _ ≤ _ := a2
        _ = 2 * M * t := a3
        _ ≤ M * M * M := a4.trans a5
        _ = M ^ 3 := by ring
    have key : ∀ C', C' ≤ K → VLe Ω0 (c l) e ψ ((((l:ℕ):ℝ) * h.N * e) ^ C') →
        VLe Ω0 (c l) e ψ (M ^ (3 * K)) := by
      intro C' hC' v
      apply VLe.mono Ω0 (c l) v
      calc _ ≤ (((l:ℕ):ℝ) * h.N * e) ^ K := pow_le_pow_right₀ hbase1 hC'
        _ ≤ (M ^ 3) ^ K := pow_le_pow_left₀ (by linarith) hbase K
        _ = M ^ (3 * K) := by rw [← pow_mul]
    rcases hc4 with h1 | h1 | h1 | h1
    · exact absurd h1 hn
    · exact key CZ (le_max_left _ _) (hZ h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
    · exact key C2 (le_trans (le_max_left _ _) (le_max_right _ _))
        (hII h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
    · exact key C3 (le_trans (le_max_right _ _) (le_max_right _ _))
        (hIII h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
  have hfin : ∀ l ∈ S, ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X (c l) e, Vlen Ω0 (c l) e ψ ≠ ⊤ := by
    intro l hl e he1 he2 ψ hψ
    by_cases hn : h.CaseI (l:ℕ) e
    · have hLs : ∀ l' ∈ ({l} : Finset Nat.Primes), (l':ℕ) ≠ 2 ∧ h.CaseI (l':ℕ) e := by
        intro l' hl'
        rw [Finset.mem_singleton] at hl'
        rw [hl']
        exact ⟨(hS _ hl).1, hn⟩
      exact (hI h rfl hq1 hd hq1' hd' t hbig e he1 he2 Ω0 c {l} hLs).1 l
        (Finset.mem_singleton_self l) ψ hψ
    · exact (hother l hl e he1 he2 hn ψ hψ).1
  have hper : ∀ l ∈ S, (∀ e, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
      ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤
        ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
    intro l hl
    haveI := (c l).dvr
    haveI := (c l).fin
    haveI := hc l
    have hidx := (hfacts l hl).2.2.2.2.2.2.1
    have hlev := hostLevel h E hE
    have hT : ∀ e, (↑(h.X (c l) e) : Set (DirichletCharacter (↥(c l).O) h.N)) =
        Chr.evenSet (↥(c l).O) h.H e := by
      intro e
      ext ψ
      simp [Host.mem_X, Chr.evenSet, Host.IsChar, PsiEven]
    have hred := fun e (he : e ≠ 0) =>
      redPrime E h.N h.H hlev (l:ℕ) (hS l hl).1 hidx (c l) Ω (ld l) Ω0 e he (h.X (c l) e) (hT e)
    have r := Chr.sumBack (l:ℕ) (↥(c l).O) (DirichletCharacter (↥(c l).O) h.N)
      (fun e => if e < t then h.X (c l) e else ∅)
      ((Finset.range t).biUnion (fun e => h.X (c l) e))
      (fun ψ e => Vlen Ω0 (c l) e ψ) (fun e => plusLen (ld l) e) (fun _ => 0) t
      (by
        intro e
        split_ifs with h'
        · intro ψ hψ
          exact Finset.mem_biUnion.2 ⟨e, Finset.mem_range.2 h', hψ⟩
        · exact Finset.empty_subset _)
      (by
        intro e he1 he2
        simp only [he2, if_true, Nat.cast_zero, zero_mul, add_zero]
        exact ⟨hfin l hl e he1 he2, hred e he1.ne'⟩)
    refine ⟨r.1, ?_⟩
    have r2 := r.2
    simp only [Nat.cast_zero, Finset.sum_const_zero, mul_zero, add_zero] at r2
    refine r2.trans (le_of_eq (Finset.sum_congr rfl fun e he => ?_))
    simp only [Finset.mem_Ico] at he
    simp only [if_pos he.2]
    rfl
  have hstep : ∀ e, 0 < e → e < t →
      ∑ l ∈ S, Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤
        M ^ C1 + 2 * M * M ^ (3 * K) := by
    intro e he1 he2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => h.CaseI (l:ℕ) e)]
    have hLs : ∀ l ∈ S.filter (fun l : Nat.Primes => h.CaseI (l:ℕ) e), (l:ℕ) ≠ 2 ∧ h.CaseI (l:ℕ) e := by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨(hS l hl.1).1, hl.2⟩
    have hA := (hI h rfl hq1 hd hq1' hd' t hbig e he1 he2 Ω0 c _ hLs).2
    have hB : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e),
        Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤ (h.N:ℝ) * M ^ (3 * K) := by
      intro l hl
      rw [Finset.mem_filter] at hl
      rw [Finset.mul_sum]
      calc ∑ ψ ∈ h.X (c l) e, Real.log ((l:ℕ):ℝ) * Vn Ω0 (c l) e ψ
          ≤ ∑ ψ ∈ h.X (c l) e, M ^ (3 * K) := by
            apply Finset.sum_le_sum
            intro ψ hψ
            rw [mul_comm]
            exact (hother l hl.1 e he1 he2 hl.2 ψ hψ).2
        _ = ((h.X (c l) e).card : ℝ) * M ^ (3 * K) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (h.N:ℝ) * M ^ (3 * K) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (xCard (↥(c l).O) h.N).1 _
    have hcard : ((S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)).card : ℝ) ≤ 2 * t := by
      have := card_small (S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)) (2 * t) (by
        intro l hl
        rw [Finset.mem_filter] at hl
        have hn := hl.2
        simp only [Host.CaseI, not_and, not_not] at hn
        exact ((hfacts l hl.1).2.2.2.2.2.2.2 e he1 he2 (hn (hS l hl.1).2)).2.1)
      exact_mod_cast this
    have hB' : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e),
        Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤ 2 * M * M ^ (3 * K) := by
      calc _ ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e), (h.N:ℝ) * M ^ (3 * K) :=
            Finset.sum_le_sum hB
        _ = ((S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)).card : ℝ) * ((h.N:ℝ) * M ^ (3 * K)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * t) * ((h.N:ℝ) * M ^ (3 * K)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * M * M ^ (3 * K) := by rw [hM]; ring
    exact add_le_add hA hB'
  refine ⟨fun l hl e he1 he2 => (hper l hl).1 e he1 he2, ?_⟩
  calc ∑ l ∈ S, Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
      ≤ ∑ l ∈ S, Real.log ((l:ℕ):ℝ) *
          ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
        apply Finset.sum_le_sum
        intro l hl
        apply mul_le_mul_of_nonneg_left (hper l hl).2
        exact Real.log_nonneg (by exact_mod_cast l.2.one_lt.le)
    _ = ∑ e ∈ Finset.Ico 1 t, ∑ l ∈ S, Real.log ((l:ℕ):ℝ) *
          ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ e ∈ Finset.Ico 1 t, (M ^ C1 + 2 * M * M ^ (3 * K)) := by
        apply Finset.sum_le_sum
        intro e he
        simp only [Finset.mem_Ico] at he
        exact hstep e (by omega) he.2
    _ ≤ (t:ℝ) * (M ^ C1 + 2 * M * M ^ (3 * K)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le t 1
    _ ≤ M ^ (C1 + 3 * K + 4) := final_le M t C1 (3 * K) hM2 htM
end

