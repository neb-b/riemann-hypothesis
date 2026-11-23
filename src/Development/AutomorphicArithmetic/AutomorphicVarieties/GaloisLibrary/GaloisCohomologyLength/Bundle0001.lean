module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.cardAbove :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), D.S.card ≤ Module.finrank ℚ F := by
  intro F Ω _ _ _ _ _ l hl D
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  refine le_trans (Finset.card_le_card_of_injOn
    (t := IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F))
    (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)
  · intro p hp
    rw [D.hS] at hp
    have hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal := hp
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassFix
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.classFix :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) → ((∀ x : F, g (algebraMap F Ω x) = algebraMap F Ω x) ↔ h ∈ KStar.TotallyRealRoots.fieldSubgroup N K φ.fieldRange) := by
  intro F Ω _ _ _ _ _ N _ K _ _ _ φ g h hg
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap F Ω).injective).mp inferInstance
  letI : Algebra F K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F K := inferInstance
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  let ι : K →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ∀ x : F, ι (φ x) = algebraMap F Ω x := fun x => ι.commutes x
  set σ : Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm h with hσ
  have hσζ : ∀ y : K, y ^ N = 1 → σ y = y ^ (h : ZMod N).val := by
    intro y hy
    have := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hy
    rw [this, hσ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ y : K, g (ι y) = ι (σ y) := by
    have key : (g.toRingHom.toRatAlgHom).comp (ι.toRingHom.toRatAlgHom) =
        (ι.toRingHom.toRatAlgHom).comp σ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := {b : K | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1})
        (Algebra.eq_top_iff.mpr IsCyclotomicExtension.adjoin_roots) ?_
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      simp only [AlgHom.coe_comp, Function.comp_apply, RingHom.toRatAlgHom_apply,
        AlgEquiv.coe_algHom]
      rw [hσζ b hb, map_pow]
      apply hg
      rw [← map_pow, hb, map_one]
    intro y
    exact congrArg (fun f => f y) key
  unfold KStar.TotallyRealRoots.fieldSubgroup
  rw [Subgroup.mem_map_equiv, ← hσ, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro H y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    apply ι.toRingHom.injective
    change ι (σ (φ x)) = ι (φ x)
    rw [← hcomm, hι, H]
  · intro H x
    rw [← hι, hcomm, H _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassIff
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem ci_pow {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (a : (ZMod M)ˣ) (ζ : Ω) (hζ : ζ ^ m = 1) :
    ζ ^ (a : ZMod M).val = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  rw [ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ci_hen (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (i : ℕ) :
    HasEnoughRootsOfUnity Ω (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  infer_instance

private theorem ci_spec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (ζ : Ω) (hζ : ζ ^ l ^ n = 1) :
    g ζ = ζ ^ ((KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  have hen := ci_hen Ω l
  exact cyclotomicCharacter.spec l g ζ hζ

private theorem ci_red {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : Ω, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    w = KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) := by
  have hen := ci_hen Ω l n
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := ci_spec l n g ζ hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1

private theorem ci_eq {Ω : Type} [Field Ω] {x y : Ω} (hy : y ≠ 0) {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hab.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.LDataCardLeFinrank.classIff :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) ↔
      ((∀ ζ : Ω, ζ ^ ordCompl[l] N = 1 → g ζ = ζ ^ ((ZMod.unitsMap (Nat.ordCompl_dvd N l) h : (ZMod (ordCompl[l] N))ˣ) : ZMod (ordCompl[l] N)).val) ∧
        ZMod.unitsMap (Nat.ordProj_dvd N l) h = KStar.TotallyRealRoots.redPow l (N.factorization l) (cyclotomicCharacter Ω l g)) := by
  intro Ω _ _ _ l _ N _ g h
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l hN).ne'⟩
  have hmul : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  constructor
  · intro H
    refine ⟨fun ζ hζ => ?_, ci_red l _ g _ fun ζ hζ => ?_⟩
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, mul_comm, pow_mul, hζ, one_pow])
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, pow_mul, hζ, one_pow])
  · rintro ⟨H1, H2⟩ ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN] at hζ
      exact zero_ne_one hζ
    have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) :=
      (Nat.coprime_ordCompl hl hN).pow_left _
    have e1 : (ζ ^ ordProj[l] N) ^ ordCompl[l] N = 1 := by rw [← pow_mul, hmul, hζ]
    have e2 : (ζ ^ ordCompl[l] N) ^ ordProj[l] N = 1 := by rw [← pow_mul, mul_comm, hmul, hζ]
    refine ci_eq (pow_ne_zero _ hζ0) hcop ?_ ?_
    · rw [← map_pow, H1 _ e1, ← ci_pow _ h _ e1, ← pow_mul, ← pow_mul, mul_comm]
    · rw [← map_pow, ci_spec l _ g _ e2, ← H2, ← ci_pow _ h _ e2, ← pow_mul, ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.H0ScalRepInvPowEqTwistInv
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem units_zpow_neg_smul_eq_self_iff (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[l] A]
    (v : ℤ_[l]ˣ) (e : ℤ) (x : A) :
    ((v ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ e.natAbs) • x = x := by
  have key : ∀ n : ℕ, ((v ^ (-(n:ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ n) • x = x := by
    intro n
    rw [← Units.val_pow_eq_pow_val, ← Units.smul_def, ← Units.smul_def, zpow_neg, zpow_natCast]
    constructor
    · intro h
      conv_lhs => rw [← h]
      simp
    · intro h
      conv_lhs => rw [← h]
      simp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · simpa using key n
  · simp [← Units.val_pow_eq_pow_val]

theorem UpperTheory.V.LDataCardLeFinrank.H0_scalRep_inv_pow_eq_twistInv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (e : ℤ), H0 (scalRep (QZ l) (ψ ^ (-e))) = KStar.TotallyRealRoots.twistInv l (QZ l) ψ.range e.natAbs := by
  intro l _ Γ _ ψ e
  ext x
  rw [KStar.TotallyRealRoots.mem_twistInv]
  change (∀ g : Γ, (scalRep (QZ l) (ψ ^ (-e))) g x = x) ↔ _
  simp only [scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
    MonoidHom.zpow_apply]
  constructor
  · rintro h u ⟨g, rfl⟩
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mp (h g)
  · intro h g
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mpr (h _ ⟨g, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.ineFixRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 →
      (∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ) ∧ ∀ g ∈ Ine (F := F) A, g ζ = ζ := by
  intro F Ω _ _ _ _ _ l _ A hl m hm ζ hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hm)
  have hv1 : ∀ x : Ω, x ^ m = 1 → A.valuation x = 1 := by
    intro x hx
    have h := congrArg A.valuation hx
    rw [map_pow, map_one] at h
    rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
    · exact absurd h (pow_lt_one₀ zero_le' h1 hm0).ne
    · exact h1
    · exact absurd h (one_lt_pow₀ h1 hm0).ne'
  have hint : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1 := fun a => by
    simpa using A.valuation_le_one (a : A)
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hg : ((Nat.gcd m l : ℕ) : ℤ) = m * Nat.gcdA m l + l * Nat.gcdB m l := Nat.gcd_eq_gcd_ab m l
    rw [Nat.Coprime.gcd_eq_one hm] at hg
    have hΩ := congrArg (Int.cast : ℤ → Ω) hg
    push_cast at hΩ
    have h1 : A.valuation (1 : Ω) < 1 := by
      rw [hΩ]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
    simp at h1
  have part1 : ∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ := by
    intro ξ hξ hlt
    by_contra hne
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp [zero_pow hm0] at hζ
    set η := ξ / ζ with hηdef
    have hη : η ^ m = 1 := by rw [hηdef, div_pow, hξ, hζ, div_one]
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq hζ0).mp h)
    have hvη : A.valuation (η - 1) < 1 := by
      have e : η - 1 = (ξ - ζ) / ζ := by rw [hηdef, sub_div, div_self hζ0]
      rw [e, map_div₀, hv1 ζ hζ, div_one]
      exact hlt
    have hpow1 : ∀ j, A.valuation (η ^ j) = 1 := fun j => by rw [map_pow, hv1 η hη, one_pow]
    have hterm : ∀ i, A.valuation (1 - η ^ i) < 1 := by
      intro i
      have e : 1 - η ^ i = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1)) := by
        rw [geom_sum_mul]
        ring
      rw [e, Valuation.map_neg, map_mul]
      have hs : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        A.valuation.map_sum_le (fun j _ => (hpow1 j).le)
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hvη
    have hsum0 : ∑ i ∈ Finset.range m, η ^ i = 0 := by
      rw [geom_sum_eq hη1, hη, sub_self, zero_div]
    have hmΩ : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum0, sub_zero]
      simp
    apply hmv
    rw [hmΩ]
    exact A.valuation.map_sum_lt one_ne_zero (fun i _ => hterm i)
  refine ⟨part1, ?_⟩
  intro g hg
  have hg2 := (mem_Ine.mp hg).2
  apply part1
  · rw [← map_pow, hζ, map_one]
  · exact hg2 ζ (hv1 ζ hζ).le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NuLeBound
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

section

open KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nlb_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nlb_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nlb_main {U : Subgroup ℤ_[l]ˣ} {s e : ℕ} (h : princ l s ≤ U) (he : e ≠ 0) :
    nu l U e ≤ ((max s (if l = 2 then 2 else 1) + e.factorization l : ℕ) : ℕ∞) := by
  have hp : l.Prime := Fact.out
  set a := max s (if l = 2 then 2 else 1) with ha
  have ha1 : 1 ≤ a := le_trans (by split_ifs <;> omega) (le_max_right _ _)
  obtain ⟨u, hu⟩ := nlb_exists_unit (l := l) ha1
  have hm : u ∈ U := h (by
    rw [mem_princ, hu]
    exact pow_dvd_pow _ (le_max_left _ _))
  have hem : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
    rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]
  have key : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ e - 1) =
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) + emultiplicity l e := by
    by_cases hl : l = 2
    · refine emultiplicity_pow_sub_one_sq ?_ e
      rw [hu]
      refine pow_dvd_pow _ ?_
      rw [ha, if_pos hl]
      exact le_max_right _ _
    · refine emultiplicity_pow_sub_one_odd hl ?_ e
      rw [hu]
      exact dvd_pow_self _ (by omega)
  have := nlb_nu_le hm e
  rw [key, hem, ← padicValNat_eq_emultiplicity he] at this
  rw [Nat.cast_add, Nat.factorization_def _ hp]
  exact this

end

theorem UpperTheory.V.LDataCardLeFinrank.nuLeBound :
    ∀ (l : ℕ) [Fact l.Prime] (N e : ℕ) (U : Subgroup ℤ_[l]ˣ), KStar.TotallyRealRoots.princ l (N.factorization l) ≤ U → e ≠ 0 → KStar.TotallyRealRoots.nu l U e ≤ (nuBound l N e : ℕ∞) := by
  intro l _ N e U h he
  unfold nuBound
  by_cases hc : l ∣ N ∨ l - 1 ∣ e
  · rw [if_pos hc]
    exact nlb_main h he
  · rw [if_neg hc]
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := KStar.TotallyRealRoots.levelGroup_eq_top (l := l) hc.1 ⊤
    rw [h1] at h2
    have hU : U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      apply h
      rw [KStar.TotallyRealRoots.mem_princ, Nat.factorization_eq_zero_of_not_dvd hc.1, pow_zero]
      exact one_dvd _
    subst hU
    have h3 := hc.2
    rw [← h2, ← KStar.TotallyRealRoots.nu_pos_iff] at h3
    simpa using not_lt.mp h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.PlaceTransport
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem pt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

theorem UpperTheory.V.LDataCardLeFinrank.placeTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' →
      ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (∀ l : ℕ, v ∈ Above (F := F) l ↔ v' ∈ Above (F := F') l) ∧ (∀ x, x ∈ A ↔ σ x ∈ A') ∧
        (∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A') ∧ ∀ g, φ g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A' := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ v' A' hv'
  have hne : v'.asIdeal.comap (RingOfIntegers.mapRingHom f) ≠ ⊥ := by
    intro hb
    have h1 : ((Ideal.absNorm v'.asIdeal : ℕ) : 𝓞 F) ∈ v'.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [hb, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
    exact v'.ne_bot h1
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨v'.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, hne⟩
  have hA : ∀ x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun x => Iff.rfl
  generalize A'.comap σ.toRingHom = A at hA
  have hD : ∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A' := by
    intro g
    constructor
    · intro hg
      rw [mem_Dec]
      ext y
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hφ, ← hA, ← hA, map_inv]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) _
    · intro hg
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, hA, hA, hφ]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _
  refine ⟨v, A, ?_, ?_, hA, hD, ?_⟩
  · intro x
    have e : x ∈ v.asIdeal ↔ RingOfIntegers.mapRingHom f x ∈ v'.asIdeal := Iff.rfl
    rw [e, ← hv', pt_val_lt_one hA, h]
    rfl
  · intro l
    show RingOfIntegers.mapRingHom f ((l : ℕ) : 𝓞 F) ∈ v'.asIdeal ↔ ((l : ℕ) : 𝓞 F') ∈ v'.asIdeal
    rw [map_natCast]
  · intro g
    constructor
    · intro hg
      refine ⟨(hD g).1 hg.1, fun y hy => ?_⟩
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [← hφ, ← map_sub, ← pt_val_lt_one hA]
      exact hg.2 _ ((A.valuation_le_one_iff _).2 ((hA x).2 ((A'.valuation_le_one_iff _).1 hy)))
    · intro hg
      refine ⟨(hD g).2 hg.1, fun x hx => ?_⟩
      rw [pt_val_lt_one hA, map_sub, hφ]
      exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaAbsRes
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.shaAbsRes :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) (φ : G F' Ω' →* G F Ω) (hφ : Continuous φ),
      (∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' → ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (v ∈ S ↔ v' ∈ S') ∧
        (∀ g ∈ Dec (F := F') A', φ g ∈ Dec (F := F) A) ∧ ∀ g ∈ Ine (F := F') A', φ g ∈ Ine (F := F) A) →
      ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M), (∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S') ∧
        (Function.Surjective φ → Module.length R (ShaAbs ρ S) ≤ Module.length R (ShaAbs (ρ.comp φ) S')) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ S S' φ hφ h R _ M _ _ _ _ _ ρ
  have h1 : ∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S' := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨ha, hb⟩ := (mk_mem_ShaAbs ρ S z).1 hx
    refine (mk_mem_ShaAbs (ρ.comp φ) S' (restrictCocycles1 ρ φ hφ z)).2 ⟨?_, ?_⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, hD, -⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := ha v (hS.2 hv') A hA
      exact ⟨m, fun g hg => hm (φ g) (hD g hg)⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, -, hI⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := hb v (fun hv => hv' (hS.1 hv)) A hA
      exact ⟨m, fun g hg => hm (φ g) (hI g hg)⟩
  refine ⟨h1, fun hs => ?_⟩
  have hinj : Function.Injective (resH1 ρ φ hφ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (restrictCocycles1 ρ φ hφ z) : H1 (ρ.comp φ)) = 0 := hx
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g', rfl⟩ := hs g
    exact hm g'
  refine Module.length_le_of_injective ((resH1 ρ φ hφ).restrict h1) ?_
  intro x y hxy
  exact Subtype.ext (hinj (congrArg Subtype.val hxy))
end

