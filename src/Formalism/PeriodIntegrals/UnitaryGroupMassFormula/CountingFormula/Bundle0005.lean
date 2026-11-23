module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GoodAt {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : Prop :=
  (M p).split = none ∧ (L.H p).IsSelfDual (lattice₂ L p (VS D).L0) ∧
    (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
    ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

def DensAtGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ (Z : MatZ D) (p : PlF D), GoodAt L δ (Tn u) (Tn u') Z p →
          ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
            densP L δ ϖ (Tn u) (Tn u') Z p =
              Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0

def ResCard : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), Nat.card 𝓀[(D.s.atP p).Fp] = p.asIdeal.absNorm

def ModeLCofinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, (M p).split = none

theorem resChar_finite (D : Formalism.BasicNotions.D7) (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
  have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
      {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hempty : {p : PlF D | Loc.resChar p = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    rw [hempty]
    exact Set.finite_empty
  · refine (Ideal.finite_factors ?_).subset hsub
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ

theorem local_models_split_cofinite : ModeLCofinite := by
  intro D δ M hA
  have hfin : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)}.Finite := by
    have he : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)} =
        {p | Loc.resChar p = D.host.g 0} ∪ {p | Loc.resChar p = D.host.g 1} := by
      ext p
      simp
    rw [he]
    exact (resChar_finite D _).union (resChar_finite D _)
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [← D.s_split p]
  have hAp := (hA p).2.2.2.2.2
  cases hM : (M p).split with
  | none => exact absurd hM hp
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hAp
      exact hAp.elim
    | some sg => rfl

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitFiniteOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitFinite_of (hA : UnipotentIntegralIsGroup) (hB : OrbitReps) : OrbitFinite := by
  intro D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨K, hKf, hK⟩ := hB D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨-, hsymm, htrans⟩ := hA D F0 Λ
  unfold cntE
  rw [Set.encard_ne_top_iff]
  refine (hKf.image (fun k : (Fin D.R.rS → (VS D).V) × (VS D).V =>
      {F'' : LFlag (VS D) D.R.rS (Tn u') | F'' ∈ EZ (Tn u') F0 Λ Z ∧
        ∃ n ∈ N0 F0 Λ, (∀ a, n (k.1 a) = F''.fl.e a) ∧ n k.2 = F''.fl.z})).subset ?_
  rintro O ⟨F', hF', rfl⟩
  obtain ⟨n₀, hn₀, hk⟩ := hK F' hF'
  refine ⟨_, hk, ?_⟩
  ext F''
  simp only [Set.mem_setOf_eq, NilradicalFlagMoved]
  constructor
  · rintro ⟨hE, m, hm, he, hz⟩
    refine ⟨hE, n₀.trans m, htrans _ hn₀ _ hm, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz
  · rintro ⟨hE, n, hn, he, hz⟩
    refine ⟨hE, n₀.symm.trans n, htrans _ (hsymm _ hn₀) _ hn, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResCharLeAbsNorm
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain

set_option linter.style.haveILetI false

section
variable {K : Type} [Field K] [NumberField K]

theorem quot_finite (p : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ p.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot

def resChar (p : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ p.asIdeal)

theorem resChar_prime (p : HeightOneSpectrum (𝓞 K)) : (resChar p).Prime := by
  haveI := quot_finite p
  haveI := p.isPrime
  exact CharP.char_is_prime (𝓞 K ⧸ p.asIdeal) (ringChar (𝓞 K ⧸ p.asIdeal))

theorem resChar_mem (p : HeightOneSpectrum (𝓞 K)) : ((resChar p : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem resChar_le_absNorm (p : HeightOneSpectrum (𝓞 K)) : resChar p ≤ Ideal.absNorm p.asIdeal := by
  haveI := quot_finite p
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hinj := ZMod.castHom_injective (𝓞 K ⧸ p.asIdeal)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem fiber_card_le (q : ℕ) (hq : q.Prime) (s : Finset (HeightOneSpectrum (𝓞 K))) :
    (s.filter (fun p => resChar p = q)).card ≤ Module.finrank ℚ K := by
  set T := s.filter (fun p => resChar p = q) with hT

  have hdiv : (∏ p ∈ T, p.asIdeal) ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p _ p' _ hne
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne p.isMaximal p'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro p hp
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      have : resChar p = q := (Finset.mem_filter.mp hp).2
      rw [← this]
      exact resChar_mem p
  have hnorm : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have h1 : Ideal.absNorm (∏ p ∈ T, p.asIdeal) ∣ q ^ Module.finrank ℚ K := by
    rw [← hnorm]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
  have h2 : q ^ T.card ≤ ∏ p ∈ T, Ideal.absNorm p.asIdeal := by
    apply Finset.pow_card_le_prod
    intro p hp
    have : resChar p = q := (Finset.mem_filter.mp hp).2
    rw [← this]
    exact resChar_le_absNorm p
  rw [← map_prod] at h2
  have h3 := le_trans h2 (Nat.le_of_dvd (pow_pos hq.pos _) h1)
  exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h3
end

theorem prime_zeta_two : PrimeZeta2 := by
  intro K _ _
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le
    (c := (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2)) (fun p => by positivity) ?_
  intro u

  have step1 : ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2) ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p _
    have hp : (0 : ℝ) < resChar p := by exact_mod_cast (resChar_prime p).pos
    have hle : (resChar p : ℝ) ≤ (p.asIdeal.absNorm : ℝ) := by exact_mod_cast resChar_le_absNorm p
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  calc ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2)
      ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := step1
    _ = ∑ q ∈ u.image resChar, ∑ p ∈ u with resChar p = q, 1 / ((resChar p : ℝ) ^ 2) :=
        by
          rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp)]
    _ ≤ ∑ q ∈ u.image resChar, (Module.finrank ℚ K : ℝ) * (1 / ((q : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro q _
        rw [Finset.sum_congr rfl (g := fun _ => 1 / ((q : ℝ) ^ 2))
          (fun p hp => by rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
        have hc : ((u.filter (fun p => resChar p = q)).card : ℝ) ≤ Module.finrank ℚ K := by
          by_cases hq : q.Prime
          · exact_mod_cast fiber_card_le q hq u
          · have : u.filter (fun p => resChar p = q) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro p _ h
              exact hq (h ▸ resChar_prime p)
            rw [this, Finset.card_empty, Nat.cast_zero]
            positivity
        gcongr
    _ = (Module.finrank ℚ K : ℝ) * ∑ q ∈ u.image resChar, 1 / ((q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) := by
        gcongr
        exact hs.sum_le_tsum _ (fun _ _ => by positivity)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TransMemUnipotentIntegral
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fix_X_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, n (F0.e a) = F0.e a) :
    ∀ x ∈ F0.X, n x = x := by
  have hle : F0.X ≤ LinearMap.eqLocus (n : (VS D).V →ₗ[D.host.E] (VS D).V) LinearMap.id := by
    show Submodule.span _ (Set.range F0.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simpa [LinearMap.mem_eqLocus] using he a
  intro x hx
  simpa [LinearMap.mem_eqLocus] using hle hx

theorem Xa_le_X {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (k : ℕ) : F0.Xa k ≤ F0.X := by
  show Submodule.span _ _ ≤ Submodule.span _ _
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem mem_orth_iff {D : Formalism.BasicNotions.D7} (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_map_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hi : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y)
    (he : ∀ a, n (F0.e a) = F0.e a) (y : (VS D).V) :
    y ∈ orth (VS D) F0.X ↔ n y ∈ orth (VS D) F0.X := by
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro H x hx
    rw [← fix_X_of F0 n he x hx, hi]
    exact H x hx
  · intro H x hx
    rw [← hi, fix_X_of F0 n he x hx]
    exact H x hx

theorem gmap_mem {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {y : (VS D).V} (hy : y ∈ Λ) :
    n y ∈ Λ := by
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem gmap_surj {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {x : (VS D).V} (hx : x ∈ Λ) :
    ∃ y ∈ Λ, n y = x := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem refl_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ := by
  refine ⟨⟨⟨fun x y => rfl, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩, fun a => rfl, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · simp
  · simp

theorem symm_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ) :
    n.symm ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hi, hΛ⟩, -, horth⟩, he, hz⟩ := hn
  have hi' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hi
  have hfix : ∀ x ∈ F0.X, n.symm x = x := fun x hx =>
    n.symm_apply_eq.2 (fix_X_of F0 n he x hx).symm
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · rw [← hi' (n.symm x) (n.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ n hΛ hy
      show n.symm (n w) ∈ Λ
      rw [LinearEquiv.symm_apply_apply]
      exact hw
    · intro hx
      exact ⟨n x, gmap_mem Λ n hΛ hx, n.symm_apply_apply x⟩
  · rw [hfix x (Xa_le_X F0 (j + 1) hx), sub_self]
    exact Submodule.zero_mem _
  · have hy : n.symm x ∈ orth (VS D) F0.X := by
      rw [orth_map_of F0 n hi' he, LinearEquiv.apply_symm_apply]
      exact hx
    have e := horth (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at e
    have e' : n.symm x - x = -(x - n.symm x) := by abel
    rw [e']
    exact Submodule.neg_mem _ e
  · exact n.symm_apply_eq.2 (he a).symm
  · exact n.symm_apply_eq.2 hz.symm

theorem trans_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ)
    (hm : m ∈ N0 F0 Λ) : n.trans m ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hin, hΛn⟩, -, horthn⟩, hen, hzn⟩ := hn
  obtain ⟨⟨⟨him, hΛm⟩, -, horthm⟩, hem, hzm⟩ := hm
  have hin' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hin
  have him' : ∀ x y, (VS D).hT (m x) (m y) = (VS D).hT x y := him
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · show (VS D).hT (m (n x)) (m (n y)) = (VS D).hT x y
    rw [him', hin']
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact gmap_mem Λ m hΛm (gmap_mem Λ n hΛn hy)
    · intro hx
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ m hΛm hx
      obtain ⟨v, hv, rfl⟩ := gmap_surj Λ n hΛn hw
      exact ⟨v, hv, rfl⟩
  · have hX := Xa_le_X F0 (j + 1) hx
    show m (n x) - x ∈ _
    rw [fix_X_of F0 n hen x hX, fix_X_of F0 m hem x hX, sub_self]
    exact Submodule.zero_mem _
  · have h1 := horthn x hx
    have h2 := horthm (n x) ((orth_map_of F0 n hin' hen x).1 hx)
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      show m (n x) - x = _
      abel
    rw [e]
    exact Submodule.add_mem _ h2 h1
  · show m (n (F0.e a)) = F0.e a
    rw [hen, hem]
  · show m (n F0.z) = F0.z
    rw [hzn, hzm]

theorem unipotent_integral_isGroup : UnipotentIntegralIsGroup := by
  intro D T F0 Λ
  exact ⟨refl_mem_unipotentIntegral F0 Λ, fun n hn => symm_mem_unipotentIntegral F0 Λ n hn,
    fun n hn m hm => trans_mem_unipotentIntegral F0 Λ n m hn hm⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

