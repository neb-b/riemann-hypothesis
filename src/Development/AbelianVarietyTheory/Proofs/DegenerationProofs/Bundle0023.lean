module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSubMemMaximalIdeal
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
section
namespace GlobalTheory.TameKummer

open IsLocalRing Polynomial

theorem exists_pow_eq_of_residue {R : Type*} [CommRing R] [HenselianLocalRing R] {n : ℕ}
    (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u) (c : ResidueField R)
    (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u ∧ residue R v = c := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, hva⟩ := HenselianLocalRing.is_henselian (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (by simpa [derivative_X_pow] using hn.mul (ha.pow _))
  refine ⟨v, ?_, ?_⟩
  · simpa [sub_eq_zero] using hv
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hva
    exact hva

theorem exists_isPrimitiveRoot {R : Type*} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] {n : ℕ} (hn : IsUnit (n : R)) :
    ∃ v : R, IsPrimitiveRoot v n := by
  have : NeZero (n : ResidueField R) := ⟨by simpa using (hn.map (residue R)).ne_zero⟩
  obtain ⟨c, hc⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField R) n
  obtain ⟨v, hv, hvc⟩ := exists_pow_eq_of_residue hn isUnit_one c (by simpa using hc.pow_eq_one)
  refine ⟨v, hv, fun d hd => hc.dvd_of_pow_eq_one d ?_⟩
  rw [← hvc, ← map_pow, hd, map_one]

theorem irreducible_X_pow_sub_C {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) :
    Irreducible (X ^ n - C (algebraMap R K π) : K[X]) := by
  have hm := monic_X_pow_sub_C π hn
  have h : Irreducible (X ^ n - C π : R[X]) := by
    refine irreducible_of_eisenstein_criterion (P := Ideal.span {π})
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime) ?_ ?_ ?_ ?_ hm.isPrimitive
    · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    · intro i hi
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn), Nat.cast_lt] at hi
      rw [coeff_sub, coeff_X_pow, if_neg hi.ne, coeff_C, Ideal.mem_span_singleton]
      split_ifs <;> simp
    · rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.pos_of_ne_zero hn
    · rw [coeff_sub, coeff_X_pow, if_neg hn.symm, coeff_C, if_pos rfl, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, zero_sub, dvd_neg]
      intro h
      have : π * π ∣ π * 1 := by simpa [sq] using h
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hπ.ne_zero).1 this))
  simpa using (hm.irreducible_iff_irreducible_map_fraction_map (K := K)).1 h

theorem minpoly_eq {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) {L : Type*} [Field L] [Algebra K L] {ρ : L}
    (hρ : ρ ^ n = algebraMap K L (algebraMap R K π)) :
    minpoly K ρ = X ^ n - C (algebraMap R K π) :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C K hπ hn) (by simp [hρ])
    (monic_X_pow_sub_C _ hn)).symm

theorem isLocalRing_of_finite (R S : Type*) [CommRing R] [HenselianLocalRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  have e : S ≃+* Localization.AtPrime q := RingEquiv.ofBijective (algebraMap _ _)
    ⟨IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors,
      surjective_algebraMap_localization_of_henselian R q⟩
  exact e.symm.isLocalRing

theorem exists_root {R : Type} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  first
  | exact @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | (apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq ..)

theorem mem_range_of_pow_eq_one {R : Type*} (K : Type*) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (hn : IsUnit (n : R)) {Ω : Type*} [Field Ω] [Algebra K Ω] {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ Set.range (algebraMap K Ω) := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hn⟩
  obtain ⟨v, hv⟩ := exists_isPrimitiveRoot hn
  have h := (hv.map_of_injective (f := algebraMap R K) (IsFractionRing.injective R K)).map_of_injective
    (f := algebraMap K Ω) (algebraMap K Ω).injective
  obtain ⟨i, -, rfl⟩ := h.eq_pow_of_pow_eq_one hζ
  exact ⟨_, map_pow _ _ _⟩

theorem isClosed_eval {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

theorem exists_generator {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {l : ℕ} (hl : IsUnit (l : R)) (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) →
      ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsGalois K Ω := {}
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hlm : ∀ m, IsUnit ((l ^ m : ℕ) : R) := fun m => by simpa using hl.pow m
  have hπ0 : algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    simpa using hπ.ne_zero
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun m => {σ | ∀ ρ : Ω,
    ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ}
  have hcl : ∀ m, IsClosed (G m) := fun m => by
    have : G m = ⋂ ρ : Ω, {σ : Ω ≃ₐ[K] Ω | σ ρ ∈ {y | ρ ^ l ^ m =
        algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ y = ζ * ρ}} := by
      ext σ
      simp [G]
    rw [this]
    exact isClosed_iInter fun ρ => isClosed_eval ρ _
  have hdec : ∀ m, G (m + 1) ⊆ G m := fun m σ hσ ρ hρ => by
    obtain ⟨ρ', rfl⟩ := IsAlgClosed.exists_pow_nat_eq ρ (Nat.pos_of_ne_zero hl0)
    obtain ⟨ζ, hζ, h⟩ := hσ ρ' (by rw [← hρ, ← pow_mul, pow_succ'])
    refine ⟨ζ ^ l, hζ.pow (Nat.pos_of_ne_zero (pow_ne_zero _ hl0)) (pow_succ' _ _), ?_⟩
    rw [map_pow, h, mul_pow]
  have hne : ∀ m, (G m).Nonempty := fun m => by
    have hn : l ^ m ≠ 0 := pow_ne_zero _ hl0
    obtain ⟨ρ₀, hρ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (algebraMap R K π))
      (Nat.pos_of_ne_zero hn)
    have h0 : ρ₀ ≠ 0 := by
      rintro rfl
      exact hπ0 (by rw [← hρ₀, zero_pow hn])
    obtain ⟨v, hv⟩ := exists_isPrimitiveRoot (hlm m)
    have hζ := (hv.map_of_injective (f := algebraMap R K)
      (IsFractionRing.injective R K)).map_of_injective
      (f := algebraMap K Ω) (algebraMap K Ω).injective
    set ζ := algebraMap K Ω (algebraMap R K v)
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (x := ζ * ρ₀) (y := ρ₀) (K := K)
      (Algebra.IsAlgebraic.isAlgebraic _)
      (by rw [minpoly_eq K hπ hn hρ₀]; simp [mul_pow, hζ.pow_eq_one, hρ₀])
    refine ⟨σ, fun ρ hρ => ⟨ζ, hζ, ?_⟩⟩
    obtain ⟨η, hη⟩ := mem_range_of_pow_eq_one K (hlm m) (ζ := ρ / ρ₀)
      (by rw [div_pow, hρ, hρ₀, div_self hπ0])
    have : ρ = algebraMap K Ω η * ρ₀ := by rw [hη, div_mul_cancel₀ _ h0]
    rw [this, map_mul, AlgEquiv.commutes, hσ]
    ring
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  exact ⟨σ, fun m => Set.mem_iInter.1 hσ m⟩

theorem le_adjoin_root {R : Type} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : Ω, ρ ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) ∧
      L ≤ IntermediateField.adjoin K {ρ} := by
  obtain ⟨ρ, hρ⟩ := exists_root K hH hπ L hn
  have hn0 : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hρ' : (ρ : Ω) ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) := by
    have := congrArg (algebraMap L Ω) hρ
    rwa [map_pow, ← IsScalarTower.algebraMap_apply] at this
  refine ⟨ρ, hρ', ge_of_eq (IntermediateField.eq_of_le_of_finrank_eq ?_ ?_)⟩
  · simp
  · have hi : IsIntegral K (ρ : Ω) := (Algebra.IsIntegral.isIntegral (R := K) ρ).map L.val
    rw [IntermediateField.adjoin.finrank hi, minpoly_eq K hπ hn0 hρ', natDegree_X_pow_sub_C _]

end GlobalTheory.TameKummer

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.TameKummer.galois_of_prime_power_degree : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [CharZero K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (l : ℕ), l.Prime → IsUnit (l : R) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∃ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) ∧ L ≤ IntermediateField.adjoin K {ρ}) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Set.range (algebraMap K Ω)) ∧ ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  rintro R K _ _ _ _ _ _ ⟨h1, h2, h3, h4⟩ π hπ l hl hu Ω _ _ _
  obtain rfl : ‹IsLocalRing R› = h2.toIsLocalRing := rfl
  refine ⟨fun L hL hN hp => ?_, fun m ζ hζ => ?_, GlobalTheory.TameKummer.exists_generator K h2 hπ hu Ω⟩
  · have : IsGalois K L := {}
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
    rw [IsGalois.card_aut_eq_finrank] at hm
    obtain ⟨ρ, h⟩ := GlobalTheory.TameKummer.le_adjoin_root K h2 hπ L (by rw [hm]; simpa using hu.pow m)
    exact ⟨m, ρ, hm ▸ h⟩
  · exact GlobalTheory.TameKummer.mem_range_of_pow_eq_one (R := R) K (by simpa using hu.pow m) hζ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericIsomorphismProductModels
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.GenProj

theorem ext_of_dense {W X T Z : Scheme.{0}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)

theorem eq_of_generic {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by
  have key : pullback.fst p p ≫ q = pullback.snd p p ≫ q := by
    let w := pullback.fst p p ≫ p ≫ s
    have : Flat w := by dsimp only [w]; infer_instance
    refine ext_of_dense (pullback.fst w i) s' ?_ ?_
    · obtain ⟨c₁, h₁, h₁'⟩ := H _ (pullback.fst w i ≫ pullback.fst p p) (pullback.snd w i)
        (by rw [← pullback.condition]; simp [w])
      obtain ⟨c₂, h₂, h₂'⟩ := H _ (pullback.fst w i ≫ pullback.snd p p) (pullback.snd w i)
        (by rw [← pullback.condition, Category.assoc, ← pullback.condition_assoc])
      have e : c₁ = c₂ := by
        rw [← cancel_mono j, h₁, h₂, Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, ← h₁', ← h₂', e]
    · rw [Category.assoc, Category.assoc, ← hs, pullback.condition_assoc]
  have := congrArg (fun x => pullback.lift a b hab ≫ x) key
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem exists_image {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hr : Set.range p ⊆ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact subset_rfl
  have e : IsOpenImmersion.lift V.ι p hr ≫ V.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (IsOpenImmersion.lift V.ι p hr) (𝟙 U) V.ι p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [e, Category.id_comp]⟩
  refine ⟨V, IsOpenImmersion.lift V.ι p hr, e, ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip ‹_›
  · rintro ⟨_, u, rfl⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, e]; rfl

theorem exists_openImmersion {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by
  obtain ⟨V, p', hp, _, _, _⟩ := exists_image p
  obtain ⟨V', q', hq, _, _, _⟩ := exists_image q
  have H' : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p' = b ≫ p' ↔ a ≫ q' = b ≫ q' := by
    intro Z a b
    rw [← cancel_mono V.ι, ← cancel_mono V'.ι]
    simpa [hp, hq] using H Z a b
  let u := EffectiveEpi.desc p' q' (fun a b h => (H' _ a b).1 h)
  let v := EffectiveEpi.desc q' p' (fun a b h => (H' _ a b).2 h)
  have hu : p' ≫ u = q' := EffectiveEpi.fac _ _ _
  have hv : q' ≫ v = p' := EffectiveEpi.fac _ _ _
  have : IsIso u := ⟨v, by rw [← cancel_epi p', ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hv, hu, Category.comp_id]⟩
  exact ⟨V, p', u ≫ V'.ι, hp, ‹_›, ‹_›, by rw [← Category.assoc, hu, hq], inferInstance⟩

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => (M.prod N).e.inv.left ≫ q) h4).symm.trans h2)

theorem exists_lift_j (M : Model R A) {Z : Scheme.{0}} (a : Z ⟶ M.Y.left) (t : Z ⟶ Sp K)
    (h : a ≫ M.Y.hom = t ≫ spMap (algebraMap R K)) : ∃ d : Z ⟶ A.left, d ≫ M.j = a := by
  refine ⟨pullback.lift a t h ≫ M.e.hom.left, ?_⟩
  have e : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  unfold Model.j
  rw [Category.assoc, ← Category.assoc M.e.hom.left, e]
  exact (congrArg _ (Category.id_comp _)).trans (pullback.lift_fst _ _ _)

theorem mono_j [IsFractionRing R K] (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : Mono (pullback.fst M.Y.hom (spMap (algebraMap R K))) := inferInstance
  exact mono_comp' inferInstance this

theorem genIso_of_prod : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  intro R K _ _ _ _ _ hSH A A' B B' _ _ M M' N N' f Θ _ _ _ _ hΘ ⟨z, hz, U, g, hzU, ⟨hg₁, hg₂⟩, hgo⟩
  have := hSH.2.2.2
  have := M.smooth; have := M'.smooth; have := N.smooth; have := N'.smooth
  have := M.sep; have := M'.sep
  have := mono_j M; have := mono_j M'
  have : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  let π : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let π' : (M'.prod N').Y.left ⟶ M'.Y.left := (fst M'.Y N'.Y).left
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst M.Y.hom N.Y.hom))
  have : Smooth π' := inferInstanceAs (Smooth (pullback.fst M'.Y.hom N'.Y.hom))
  have hπ : π ≫ M.Y.hom = (M.prod N).Y.hom := Over.w (fst M.Y N.Y)
  have hπ' : π' ≫ M'.Y.hom = (M'.prod N').Y.hom := Over.w (fst M'.Y N'.Y)
  have hj : (M.prod N).j ≫ π = (fst A B).left ≫ M.j := prod_j_fst M N
  have hj' : (M'.prod N').j ≫ π' = (fst A' B').left ≫ M'.j := prod_j_fst M' N'
  have hs : (U.ι ≫ π) ≫ M.Y.hom = (g ≫ π') ≫ M'.Y.hom := by
    rw [Category.assoc, Category.assoc, hπ, hπ', hg₁]
  have H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U.toScheme) (t : Z ⟶ Sp K),
      a ≫ (U.ι ≫ π) ≫ M.Y.hom = t ≫ spMap (algebraMap R K) →
      ∃ c : Z ⟶ A.left, c ≫ M.j = a ≫ U.ι ≫ π ∧ c ≫ f.hom.left ≫ M'.j = a ≫ g ≫ π' := by
    intro Z a t h
    obtain ⟨d, hd⟩ := exists_lift_j (M.prod N) (a ≫ U.ι) t (by rw [← h, ← hπ]; simp only [Category.assoc])
    obtain ⟨d', h₁, h₂⟩ := (isPullback_morphismRestrict (M.prod N).j U).exists_lift a d hd.symm
    refine ⟨d ≫ (fst A B).left, ?_, ?_⟩
    · rw [Category.assoc, ← hj, ← Category.assoc, hd, Category.assoc]
    · have e : Θ.left ≫ (fst A' B').left = (fst A B).left ≫ f.hom.left := by
        rw [← Over.comp_left, hΘ, Over.comp_left]
      rw [← h₁, ← h₂]
      simp only [Category.assoc]
      rw [reassoc_of% hg₂, hj', reassoc_of% e]
  obtain ⟨V, p', h, hp, _, _, hq, hh⟩ := exists_openImmersion (U.ι ≫ π) (g ≫ π') (fun Z a b =>
    ⟨eq_of_generic (spMap (algebraMap R K)) M.Y.hom M'.Y.hom _ _ hs M.j (f.hom.left ≫ M'.j) H a b,
     eq_of_generic (spMap (algebraMap R K)) M'.Y.hom M.Y.hom _ _ hs.symm (f.hom.left ≫ M'.j) M.j
      (fun Z a t h => (H Z a t (by rw [hs, h])).imp fun _ h => h.symm) a b⟩)
  have : Epi p' := Flat.epi_of_flat_of_surjective _
  refine ⟨π z, ?_, V, h, ?_, ⟨?_, ?_⟩, hh⟩
  · show M.Y.hom (π z) = _
    rw [← Scheme.Hom.comp_apply, hπ]; exact hz
  · have : V.ι (p' ⟨z, hzU⟩) = π z := congrArg (fun q : U.toScheme ⟶ M.Y.left => q ⟨z, hzU⟩) hp
    rw [← this]; exact (p' ⟨z, hzU⟩).2
  · rw [← cancel_epi p', reassoc_of% hq, reassoc_of% hp]
    simpa only [Category.assoc] using hs.symm
  · have : Epi (pullback.snd p' (M.j ∣_ V)) := Flat.epi_of_flat_of_surjective _
    have e : pullback.fst p' (M.j ∣_ V) ≫ U.ι ≫ π = (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι) ≫ M.j := by
      rw [← hp, pullback.condition_assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨c, hc₁, hc₂⟩ := H _ (pullback.fst p' (M.j ∣_ V)) (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι ≫ A.hom)
      (by rw [← Category.assoc, e, Category.assoc, M.j_hom]; simp only [Category.assoc])
    rw [e, cancel_mono] at hc₁
    rw [← cancel_epi (pullback.snd p' (M.j ∣_ V)), ← pullback.condition_assoc, hq, ← hc₂, hc₁, Category.assoc]

end GlobalTheory.SS.GenProj
end
end

