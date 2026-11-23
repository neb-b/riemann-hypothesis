module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem cyc_mem_princ_iff (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (g : G F Ω) :
    cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ ∀ t : Ω, t ^ l ^ n = 1 → g t = t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ F Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  have hpow : ∀ t : Ω, t ^ l ^ n = 1 → t ^ (1 : ZMod (l ^ n)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  rw [h1]
  constructor
  · intro h t ht
    have := cyclotomicCharacter.spec l g.toRingEquiv t ht
    rw [h, hpow t ht] at this
    exact this
  · intro h
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ ht'

private theorem le_finrank (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ)
    (h : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) : c ≤ Module.finrank ℚ L := by
  have hl : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := h
  have h1 : (l ^ c).totient ≤ Module.finrank ℚ L := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ c) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hl.pos c)]
    exact minpoly.natDegree_le ζ
  rcases c with _ | c
  · exact Nat.zero_le _
  · rw [Nat.totient_prime_pow_succ hl] at h1
    have h2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
    have h4 : l ^ c * 1 ≤ l ^ c * (l - 1) := Nat.mul_le_mul_left _ h3
    omega

private theorem ex_iff (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L := by
  have hl : l.Prime := Fact.out
  have hb : BddAbove {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)} := ⟨_, fun c hc => le_finrank L l c hc⟩
  refine ⟨fun h => le_csSup hb h, fun h => ?_⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ cZero l L) :=
    Nat.sSup_mem (s := {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)}) ⟨0, 1, by simp⟩ hb
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  exact ⟨ζ ^ l ^ d, hζ.pow (pow_pos hl.pos _) (by rw [hd, pow_add, mul_comm])⟩

private theorem all_iff (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l c) ↔ ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : IsGalois L Ω := IsGalois.mk
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ c)
    obtain ⟨ζ, rfl⟩ : ξ ∈ Set.range (algebraMap L Ω) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed ξ).2 fun g =>
        (cyc_mem_princ_iff L Ω l c g).1 (h g) ξ hξ.pow_eq_one
    exact ⟨ζ, hξ.of_map_of_injective (algebraMap L Ω).injective⟩
  · rintro ⟨ζ, hζ⟩ g
    have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ c) := hζ.map_of_injective (algebraMap L Ω).injective
    refine (cyc_mem_princ_iff L Ω l c g).2 fun t ht => ?_
    obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one ht
    rw [map_pow, g.commutes]

theorem UpperTheory.V.Tower.muQ :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], (∀ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L) ∧ (∀ c : ℕ, Un L Ω l c = ⊤ ↔ c ≤ cZero l L) ∧
        (HasMuQ l L ↔ qExp l ≤ cZero l L) ∧ (HasMuQ l L → IsTotallyComplex L ∧ Procyc L Ω l) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L) := by
  intro L Ω _ _ _ _ _ l _
  have hl : l.Prime := Fact.out
  have hq : (if l = 2 then 4 else l) = l ^ qExp l := by
    unfold qExp
    split_ifs with h
    · subst h; rfl
    · rw [pow_one]
  have hP : Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L := by
    by_cases h : l = 2
    · have h2 : qExp l = 2 := if_pos h
      rw [Procyc, HasMuQ, hq, h2, ← all_iff L Ω l 2]
      rfl
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  refine ⟨ex_iff L l, fun c => ?_, ?_, fun h => ⟨?_, hP.2 (Or.inr h)⟩, hP⟩
  · rw [← ex_iff, ← all_iff L Ω, Subgroup.eq_top_iff']
    exact forall_congr' fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  · rw [HasMuQ, hq, ex_iff]
  · obtain ⟨ζ, hζ⟩ := h
    refine nrRealPlaces_eq_zero_iff.1 (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt ?_ hζ)
    have := hl.two_le
    split_ifs <;> omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTors
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dinfTors :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)), (IsClosed (U : Set (G k Ω)) → ∀ φ : Dinf l N U, ∃ r : ℕ, (l : ℤ_[l]) ^ r • φ = 0) ∧
        Dinf l N U ≤ Dinf l 1 U ∧ xRank l N U ≤ xRank l 1 U ∧
        ∀ [U.Normal] (e : ℤ), ∀ g ∈ cycU l U, dRep l N U g = 1 ∧ xRep l N U g = 1 ∧ dTw l N U e g = 1 ∧ xTw l N U e g = 1 := by
  intro k Ω _ _ _ _ _ l _ N U
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hconj : ∀ [U.Normal] (g : G k Ω), g ∈ cycU l U → ∀ φ : Dinf l N U, dRep l N U g φ = φ := by
    intro _ g hg φ
    have hadd := φ.2.2.1
    have h1 : (φ : cycU l U → QZ l) 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      simpa using this
    apply Subtype.ext
    funext u
    have e1 : conjHom (cycU l U) g u = (⟨g, hg⟩ : cycU l U)⁻¹ * u * ⟨g, hg⟩ := rfl
    change (φ : cycU l U → QZ l) (conjHom (cycU l U) g u) = _
    rw [e1, hadd, hadd]
    have h2 := hadd (⟨g, hg⟩ : cycU l U)⁻¹ ⟨g, hg⟩
    rw [inv_mul_cancel, h1] at h2
    rw [add_comm ((φ : cycU l U → QZ l) _) ((φ : cycU l U → QZ l) u), add_assoc, ← h2, add_zero]
  have hmono : Dinf l N U ≤ Dinf l 1 U := fun φ hφ =>
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun A hA => by simp at hA⟩
  refine ⟨fun hU φ => ?_, hmono, ?_, ?_⟩
  · classical
    have hC : IsClosed ((cycU l U : Subgroup (G k Ω)) : Set (G k Ω)) :=
      hU.inter (isClosed_singleton.preimage (continuous_cycZ k Ω l))
    haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  · refine Module.length_le_of_injective
      (LinearMap.restrict (Submodule.inclusion hmono)
        (p := Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]))
        (q := Submodule.torsionBy ℤ_[l] (Dinf l 1 U) (l : ℤ_[l])) fun x hx => ?_) ?_
    · rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← LinearMap.map_smul, hx, map_zero]
    · intro a b hab
      apply Subtype.ext
      apply Submodule.inclusion_injective hmono
      exact congrArg Subtype.val hab
  · intro _ e g hg
    have hc : cycZ k Ω l g = 1 := hg.2
    have hd : dRep l N U g = 1 := LinearMap.ext fun φ => hconj g hg φ
    have hx : xRep l N U g = 1 := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro φ
      change ((dRep l N U).linHom (Representation.trivial ℤ_[l] (G k Ω) (QZ l)) g f) φ = f φ
      rw [Representation.linHom_apply]
      simp [hconj g⁻¹ (inv_mem hg)]
    refine ⟨hd, hx, ?_, ?_⟩
    · show ((cycZ k Ω l ^ (-e)) g : ℤ_[l]) • dRep l N U g = 1
      simp [hc, hd]
    · show ((cycZ k Ω l ^ e) g : ℤ_[l]) • xRep l N U g = 1
      simp [hc, hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem dt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

private theorem dt_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Dec (F := F') A') :
    g ∈ Dec (F := F) A := by
  have h' : ∀ x, σ (g⁻¹ x) = g'⁻¹ (σ x) := fun x => by
    show σ (g.symm x) = g'.symm (σ x)
    rw [eq_comm, AlgEquiv.symm_apply_eq, ← h, AlgEquiv.apply_symm_apply]
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hA, hA, h']
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _

private theorem dt_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Ine (F := F') A') :
    g ∈ Ine (F := F) A := by
  refine ⟨dt_dec hA h hg.1, fun x hx => ?_⟩
  rw [dt_val_lt_one hA, map_sub, h]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))

private theorem dt_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] (σ : Ω ≃+* Ω') (N : ℕ)
    {V : Subgroup (G F Ω)} {V' : Subgroup (G F' Ω')} (e : V' →* V) (he : Continuous e)
    (h : ∀ (u : V') x, σ ((e u).1 x) = u.1 (σ x)) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {ψ : V → M} (hψ : ψ ∈ XDual N V R M) : ψ ∘ e ∈ XDual N V' R M := by
  have hA : ∀ (A' : ValuationSubring Ω') x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun _ _ => Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := hψ
  refine ⟨h1.comp_continuous he, fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
  · simp only [Function.comp_apply, map_mul, h2]
  · exact h3 (A.comap σ.toRingHom) _ (dt_ine (hA A) (h u) hu)
  · refine h4 (A.comap σ.toRingHom) ?_ _ (dt_dec (hA A) (h u) hu)
    rw [dt_val_lt_one (hA A), map_natCast]
    exact hN

theorem UpperTheory.V.Tower.dinfTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
        ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) (U' : Subgroup (G F' Ω')),
          (cycU l U').map φ = cycU l U → ∃ Ψ : Dinf l N U ≃ₗ[ℤ_[l]] Dinf l N U', ∀ (ψ : Dinf l N U) (u' : cycU l U') (u : cycU l U), u.1 = φ u'.1 → (Ψ ψ).1 u' = ψ.1 u := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ l _ N U U' hU
  obtain ⟨φ₀, hc, hφ₀, -, hi, -⟩ := galTransport F Ω F' Ω' f σ h
  obtain rfl : φ₀ = φ := MonoidHom.ext fun g => AlgEquiv.ext fun x => σ.injective (by rw [hφ, hφ₀])
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : IsGalois F' Ω' := IsAlgClosure.isGalois F' Ω'
  have hemb : Topology.IsInducing φ₀ := (hc.isClosedEmbedding hi).isInducing
  let e : cycU l U' ≃* cycU l U := ((cycU l U').equivMapOfInjective φ₀ hi).trans (MulEquiv.subgroupCongr hU)
  have he : ∀ u, (e u).1 = φ₀ u.1 := fun _ => rfl
  have he' : ∀ u, φ₀ (e.symm u).1 = u.1 := fun u => by rw [← he, MulEquiv.apply_symm_apply]
  have c1 : Continuous e.toMonoidHom := (hc.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e.symm.toMonoidHom := by
    refine continuous_induced_rng.2 (hemb.continuous_iff.2 ?_)
    exact continuous_subtype_val.congr fun u => (he' u).symm
  refine ⟨{ toFun := fun ψ => ⟨ψ.1 ∘ e.toMonoidHom, dt_mem σ N e.toMonoidHom c1 (fun u x => hφ u.1 x) ψ.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun ψ => ⟨ψ.1 ∘ e.symm.toMonoidHom, dt_mem σ.symm N e.symm.toMonoidHom c2 (fun u x => ?_) ψ.2⟩
            left_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.apply_symm_apply u))
            right_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.symm_apply_apply u)) }, ?_⟩
  · show σ.symm ((e.symm u).1 x) = u.1 (σ.symm x)
    rw [RingEquiv.symm_apply_eq, ← he' u, hφ, RingEquiv.apply_symm_apply]
  · intro ψ u' u hu
    exact congrArg ψ.1 (Subtype.ext hu.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dualKer :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (M' : Type) [AddCommGroup M'] [Module ℤ_[l] M'] (T : M →ₗ[ℤ_[l]] M'),
        LinearMap.range (LinearMap.lcomp ℤ_[l] (QZ l) T) = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker T).subtype) ∧
        ∀ p : Submodule ℤ_[l] M, Function.Surjective (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  intro l _ M _ _ M' _ _ T
  have hI := PropA.qzInj l
  refine ⟨?_, fun p g => ?_⟩
  · ext f
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext ⟨x, hx⟩
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.zero_apply]
      rw [LinearMap.mem_ker.mp hx, map_zero]
    · intro hf
      have hle : LinearMap.ker T ≤ LinearMap.ker f := by
        intro x hx
        have := LinearMap.congr_fun hf ⟨x, hx⟩
        simpa using this
      let g0 : LinearMap.range T →ₗ[ℤ_[l]] QZ l :=
        ((LinearMap.ker T).liftQ f hle).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap
      obtain ⟨h, hh⟩ := hI.out (LinearMap.range T).subtype Subtype.val_injective g0
      refine ⟨h, ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
      have := hh ⟨T x, LinearMap.mem_range_self T x⟩
      simp only [Submodule.subtype_apply] at this
      rw [this]
      simp [g0, LinearMap.quotKerEquivRange_symm_apply_image]
  · obtain ⟨h, hh⟩ := hI.out p.subtype Subtype.val_injective g
    refine ⟨h, ?_⟩
    ext x
    simpa using hh x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.existsGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∃ γ, IsGen l U γ := by
  intro k Ω _ _ _ _ _ l _ U hU hcond
  have hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hU.isCompact.image (continuous_cycZ k Ω l)).isClosed
  have hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2 := by
    by_cases hl : l = 2
    · rcases hcond with h | h
      · exact absurd hl h
      · right
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        have hx' := h hx
        simp only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'
        exact hx'.2
    · exact Or.inl hl
  obtain ⟨γ', hγ', hle⟩ := UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc
  obtain ⟨γ, hγU, rfl⟩ := Subgroup.mem_map.mp hγ'
  exact ⟨γ, hγU, hle⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem pg_emult {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) (h2 : l = 2 → 2 ≤ c) {u : ℤ_[l]}
    (hd : (l : ℤ_[l]) ^ c ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = emultiplicity (l : ℤ_[l]) (u - 1) + n := by
  have hp : Prime (l : ℕ) := (Fact.out : l.Prime).prime
  by_cases hl : l = 2
  · have hc : 2 ≤ c := h2 hl
    have hd2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 := (pow_dvd_pow _ hc).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq hd2, emultiplicity_pow_self_of_prime hp]
  · have hd1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ (by omega)).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_odd hl hd1, emultiplicity_pow_self_of_prime hp]

private theorem pg_index {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 0 < a) :
    (KStar.TotallyRealRoots.princ l a).index = l ^ (a - 1) * (l - 1) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hker : KStar.TotallyRealRoots.princ l a = (KStar.TotallyRealRoots.redPow l a).ker := rfl
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (KStar.TotallyRealRoots.redPow_surjective a),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl ha]

private theorem pg_exists {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) :
    ∃ v ∈ KStar.TotallyRealRoots.princ l c, v ∉ KStar.TotallyRealRoots.princ l (c + 1) := by
  have hirr : Irreducible (l : ℤ_[l]) := PadicInt.irreducible_p
  have hnu : ¬ IsUnit (-((l : ℤ_[l]) ^ c)) := by
    rw [IsUnit.neg_iff, isUnit_pow_iff (by omega)]
    exact hirr.not_isUnit
  have hu : IsUnit (1 + (l : ℤ_[l]) ^ c) := by
    have := (IsLocalRing.isUnit_or_isUnit_one_sub_self (-((l : ℤ_[l]) ^ c))).resolve_left hnu
    simpa [sub_eq_add_neg] using this
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp only [IsUnit.unit_spec, add_sub_cancel_left]
    rw [pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit]
    omega

theorem UpperTheory.V.Tower.princGen :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℕ), qExp l ≤ c →
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, (KStar.TotallyRealRoots.princ l c ≤ (Subgroup.zpowers u).topologicalClosure ↔ u ∉ KStar.TotallyRealRoots.princ l (c + 1))) ∧
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, u ∉ KStar.TotallyRealRoots.princ l (c + 1) → PropA.IsLevel l (u : ℤ_[l]) c ∧
          ∀ m : ℕ, u ^ l ^ m ∈ KStar.TotallyRealRoots.princ l (c + m) ∧ u ^ l ^ m ∉ KStar.TotallyRealRoots.princ l (c + m + 1)) ∧
        ∀ m : ℕ, (KStar.TotallyRealRoots.princ l (c + m)).relIndex (KStar.TotallyRealRoots.princ l c) = l ^ m := by
  intro l _ c hc
  have hl : l.Prime := Fact.out
  have h1 : 1 ≤ c := by
    unfold qExp at hc; split_ifs at hc <;> omega
  have h2 : l = 2 → 2 ≤ c := by
    intro h; unfold qExp at hc; simp [h] at hc; omega
  have hexact : ∀ u : ℤ_[l]ˣ, u ∈ KStar.TotallyRealRoots.princ l c → u ∉ KStar.TotallyRealRoots.princ l (c + 1) →
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = c := by
    intro u hu hu1
    rw [KStar.TotallyRealRoots.mem_princ] at hu hu1
    exact emultiplicity_eq_coe.mpr ⟨hu, hu1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    constructor
    · intro hle hu1
      have hcl : IsClosed ((KStar.TotallyRealRoots.princ l (c + 1) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
        Subgroup.isClosed_of_isOpen _ (KStar.TotallyRealRoots.isOpen_princ _)
      have hcle := Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hu1) hcl
      obtain ⟨v, hv, hv'⟩ := pg_exists (l := l) h1
      exact hv' (hcle (hle hv))
    · intro hu1
      exact KStar.TotallyRealRoots.princ_le_of_isClosed h1 h2 (Subgroup.isClosed_topologicalClosure _)
        (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)) (hexact u hu hu1)
  · intro u hu hu1
    have he := hexact u hu hu1
    refine ⟨⟨?_, h1, h2⟩, ?_⟩
    · have hpow : ∀ n : ℕ, IsDiscreteValuationRing.addVal ℤ_[l] ((l : ℤ_[l]) ^ n) = n := by
        intro n
        rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p]
        simp
      obtain ⟨hd, hnd⟩ := emultiplicity_eq_coe.mp he
      have a1 := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hd
      rw [hpow] at a1
      have a2 : ¬ (((c + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1)) := by
        intro h
        apply hnd
        apply (IsDiscreteValuationRing.addVal_le_iff_dvd).mp
        rw [hpow]
        exact h
      show IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1) = c
      apply le_antisymm _ a1
      push_neg at a2
      push_cast at a2
      exact ENat.lt_natCast_add_one_iff.mp a2
    · intro m
      have hm := pg_emult h1 h2 (KStar.TotallyRealRoots.mem_princ.mp hu) m
      rw [he] at hm
      have hm' : emultiplicity (l : ℤ_[l]) (((u ^ l ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1) = ((c + m : ℕ) : ℕ∞) := by
        push_cast
        exact hm
      obtain ⟨a, b⟩ := emultiplicity_eq_coe.mp hm'
      exact ⟨KStar.TotallyRealRoots.mem_princ.mpr a, fun h => b (KStar.TotallyRealRoots.mem_princ.mp h)⟩
  · intro m
    have hle := KStar.TotallyRealRoots.princ_anti (l := l) (Nat.le_add_right c m)
    have key := Subgroup.relIndex_mul_index hle
    rw [pg_index (by omega : 0 < c), pg_index (by omega : 0 < c + m)] at key
    have hcm : c + m - 1 = (c - 1) + m := by omega
    rw [hcm, pow_add] at key
    have hpos : 0 < l ^ (c - 1) * (l - 1) :=
      Nat.mul_pos (pow_pos hl.pos _) (by have := hl.two_le; omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [key]
    ring
end

