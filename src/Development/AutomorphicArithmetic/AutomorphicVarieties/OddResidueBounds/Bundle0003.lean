module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.actFacts :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → Function.Surjective ρ ∧ IsAbelianGalois ℚ E ∧ Nat.card (Gq ρ) = Module.finrank ℚ E ∧ ρ.ker.index = Module.finrank ℚ E ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), IsCycAct Ω M (ρ.comp (ZMod.unitsMap h)) := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  obtain ⟨_, hb⟩ := liftEx E Ω N
  have inj := (algebraMap E Ω).injective
  have hsurj : Function.Surjective ρ := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) τ.toRingEquiv
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨b, ?_⟩
    ext x
    apply inj
    have h1 := hρ b σ hbσ x
    have h2 := hσ x
    simpa using h1.symm.trans h2
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap inj
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ φ : E →ₐ[ℚ] Ω, ∃ σ : Ω ≃+* Ω, ∀ x : E, σ (algebraMap E Ω x) = φ x := by
    intro φ
    refine ⟨((Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ Ω).symm (φ.liftNormal Ω)).toRingEquiv,
      fun x => ?_⟩
    change φ.liftNormal Ω (algebraMap E Ω x) = φ x
    simpa only [Algebra.algebraMap_self_apply] using φ.liftNormal_commutes Ω x
  let f : Gal(E/ℚ) → (E →ₐ[ℚ] Ω) := fun g => (IsScalarTower.toAlgHom ℚ E Ω).comp g.toAlgHom
  have hf : Function.Surjective f := by
    intro φ
    obtain ⟨σ, hσ⟩ := key φ
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨ρ b, ?_⟩
    ext x
    have h1 := hρ b σ hbσ x
    rw [← hσ x, h1]
    rfl
  have hcard : Nat.card Gal(E/ℚ) = Module.finrank ℚ E := by
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    · calc Module.finrank ℚ E = Nat.card (E →ₐ[ℚ] Ω) := by
            rw [Nat.card_eq_fintype_card, AlgHom.card]
        _ ≤ Nat.card Gal(E/ℚ) := Nat.card_le_card_of_surjective f hf
  haveI : IsGalois ℚ E := IsGalois.of_card_aut_eq_finrank ℚ E hcard
  have hq : Nat.card (Gq ρ) = Module.finrank ℚ E := by
    rw [← hcard]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv
  refine ⟨hsurj, ?_, hq, hq, ?_⟩
  · exact
      { is_comm := ⟨fun x y => by
          obtain ⟨a, rfl⟩ := hsurj x
          obtain ⟨c, rfl⟩ := hsurj y
          rw [← map_mul, ← map_mul, mul_comm]⟩ }
  · intro M _ h b σ hσ
    apply hρ
    intro x hx
    have hxM : x ^ M = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, hx, one_pow]
    rw [hσ x hxM, ZMod.unitsMap_val]
    have e : (ZMod.cast (b : ZMod M) : ZMod N).val = (b : ZMod M).val % N := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (b : ZMod M)]
      rw [ZMod.cast_natCast h, ZMod.val_natCast]
    rw [e]
    conv_lhs => rw [← Nat.div_add_mod (b : ZMod M).val N]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.CobOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem coboundary_of_vanishing_on_finite_index {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) (hn : IsUnit (H.index : R)) (hn' : H.index ≠ 0) : ∃ m, ∀ g, f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index π H f hf h0 hn hn'

theorem UpperTheory.V.Odd.cobOne :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (z : Z1 (qzTw D e)), (∀ g ∈ galOf E (Fn E Ω l 1) Ω, z.1 (toGS Ω _ g) = 0) → (Submodule.Quotient.mk z : H1 (qzTw D e)) = 0 := by
  intro E Ω _ _ _ _ _ l hl D e z hz
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  have h0 := (fnCyc E Ω l 1).1
  rw [pow_one] at h0
  haveI : FiniteDimensional E (Fn E Ω l 1) := IsCyclotomicExtension.finiteDimensional {l} E _
  haveI : NumberField (Fn E Ω l 1) := NumberField.of_module_finite E _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure (Fn E Ω l 1) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  have hi : (galOf E (Fn E Ω l 1) Ω).index ∣ l - 1 := by
    rw [(galEmbTop E (Fn E Ω l 1) Ω).2.2]
    exact (fnOne E Ω l).1
  have h2 := hl.out.two_le
  have hle := Nat.le_of_dvd (by omega) hi
  have hne : (galOf E (Fn E Ω l 1) Ω).index ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hi
    omega
  have hu : IsUnit ((galOf E (Fn E Ω l 1) Ω).index : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, hl.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne) (by omega)
  obtain ⟨m, hm⟩ := coboundary_of_vanishing_on_finite_index ((qzTw D e).comp (toGS Ω _)) (galOf E (Fn E Ω l 1) Ω) (fun g => z.1 (toGS Ω _ g))
    (fun g h => by rw [map_mul]; exact z.2.2 _ _) hz hu hne
  rw [Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
  exact hm σ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

theorem UpperTheory.V.Odd.fixField :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∃ (K : IntermediateField E Ω) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K), galOf E K Ω = fixMu E Ω N ∧ ∀ (b : (ZMod N)ˣ) (σ : Ω ≃+* Ω), CycLift N b σ → IsLift (Stick.sg N K b).toRingEquiv σ := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : IsGalois ℚ Ω := {}
  haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {ζ}
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self ℚ ζ
  have hE : ∀ e : E, algebraMap E Ω e ∈ L := fun e => by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : σ ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ ζ hζL
    have hc : CycLift N 1 σ.toRingEquiv := fun x hx => by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
      have h2 : σ x = x := by rw [← hi, map_pow, h1]
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]
      exact h2
    have := hρ 1 _ hc e
    rw [map_one] at this
    exact this
  let K : IntermediateField E Ω := L.toSubfield.toIntermediateField hE
  haveI hL : IsCyclotomicExtension {N} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  let φ : L ≃+* K := RingEquiv.refl L
  have hK : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra :=
    @IsCyclotomicExtension.equiv {N} ℚ L _ _ _ K _ DivisionRing.toRatAlgebra hL
      (@AlgEquiv.ofRingEquiv ℚ L K _ _ _ _ DivisionRing.toRatAlgebra φ fun q => by simp)
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : NumberField K := IsCyclotomicExtension.numberField {N} ℚ K
  have hmu : ∀ x : Ω, x ^ N = 1 → x ∈ K := fun x hx => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact (pow_mem hζL i : ζ ^ i ∈ L)
  have hpow : ∀ x : K, x ^ N = 1 → algebraMap K Ω x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨K, inferInstance, hK, ?_, fun b σ hσ x => ?_⟩
  · ext g
    refine ⟨fun h x hx => h ⟨x, hmu x hx⟩, fun h x => ?_⟩
    exact DFunLike.congr_fun (cyc_hom_ext N (g.toRingEquiv.toRingHom.comp (algebraMap K Ω)) (algebraMap K Ω)
      fun y hy => h _ (hpow y hy)) x
  · refine DFunLike.congr_fun (cyc_hom_ext N (σ.toRingHom.comp (algebraMap K Ω))
      ((algebraMap K Ω).comp (Stick.sg N K b).toRingEquiv.toRingHom) fun y hy => ?_) x
    change σ (algebraMap K Ω y) = algebraMap K Ω (Stick.sg N K b y)
    rw [hσ _ (hpow y hy), Stick.sg_apply N K b hy, map_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogH
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logH :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 2 ≤ N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  intro E _ _ N hN hE
  obtain ⟨hd, hn⟩ := UpperTheory.V.Odd.logDisc E N (by omega) hE
  have hc := KStar.IdealCounting.log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.NearLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem near_level (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N]
    (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N) (ho : Odd a) (hl : l ∣ N) (r m : ℕ)
    (hm : r + ck l (e + 1) + 1 ≤ m) (M : ℕ) [NeZero M] (h : N ∣ M) (hM : M = N * l ^ m) (g : Γ) :
    InPow l r ((yEl (e + 1) a ha φ).coeff g - (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℚ)) := by
  have haN : a.Coprime l := Nat.Coprime.coprime_dvd_right hl ha
  have haM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right ha (Nat.Coprime.pow_right m haN)
  have hdiv : l ^ (r + ck l (e + 1) + 1) ∣ M := by
    rw [hM]
    exact Dvd.dvd.mul_left (pow_dvd_pow l hm) N
  have hI := yNear l Γ M (φ.comp (ZMod.unitsMap h)) e a r haM ho hdiv
  rw [yLevel l Γ N φ (e + 1) a ha (by omega) hl m M h haM hM] at hI
  have := (intAt_iff l r _).mp hI g
  simpa [coeff_coefMap] using this

theorem UpperTheory.V.Odd.congr :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Odd a → l ∣ N → ∃ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) ∧ ∀ r : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∃ w : MonoidAlgebra ℤ_[l] Γ, coefMap ℤ_[l] Γ (ytEl e a (φ.comp (ZMod.unitsMap h))) = z + (l : ℤ_[l]) ^ r • w := by
  intro l _ Γ _ _ N _ φ e a ha ho hl
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set y := yEl (e + 1) a ha φ with hy
  have hy0 : IntAt l 0 y := by
    rw [intAt_iff]
    intro g
    haveI : NeZero (N * l ^ (ck l (e + 1) + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)⟩
    have hn := near_level l Γ N φ e a ha ho hl 0 (ck l (e + 1) + 1) (by omega)
      (N * l ^ (ck l (e + 1) + 1)) (dvd_mul_right _ _) rfl g
    have h1 := hn.mem
    have h2 := add_mem h1 (intCast_mem (Zl l) ((ytEl e a (φ.comp (ZMod.unitsMap
      (dvd_mul_right N (l ^ (ck l (e + 1) + 1)))))).coeff g))
    rw [sub_add_cancel] at h2
    show y.coeff g / (l : ℚ) ^ 0 ∈ Zl l
    simpa using h2
  obtain ⟨Yp, hYp⟩ := exists_padicInt_lift_of_integralAt l y hy0
  have hYg : ∀ g, ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l]) := by
    intro g
    have := congrArg (fun x => x.coeff g) hYp
    simpa using this
  refine ⟨Yp, hYg, ?_⟩
  intro r
  refine ⟨r + ck l (e + 1) + 1, ?_⟩
  intro m hm M _ h hM
  have hc : ∀ g, ∃ c : ℤ_[l], (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℤ_[l]) =
      Yp.coeff g + (l : ℤ_[l]) ^ r * c := by
    intro g
    have hn := near_level l Γ N φ e a ha ho hl r m hm M h hM g
    set t : ℤ := (ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g
    set q : ℚ := (y.coeff g - (t : ℚ)) / (l : ℚ) ^ r with hqdef
    have hq : ‖(q : ℚ_[l])‖ ≤ 1 := Padic.norm_rat_le_one (mem_Zl.mp hn)
    have hqr : q * (l : ℚ) ^ r = y.coeff g - t := by
      rw [hqdef]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0))
    have hqr' : (q : ℚ_[l]) * (l : ℚ_[l]) ^ r = ((y.coeff g : ℚ) : ℚ_[l]) - (t : ℚ_[l]) := by
      have := congrArg (fun x : ℚ => (x : ℚ_[l])) hqr
      push_cast at this
      exact this
    let c : ℤ_[l] := ⟨(q : ℚ_[l]), hq⟩
    refine ⟨-c, ?_⟩
    apply Subtype.ext
    show (t : ℚ_[l]) = ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) + (l : ℚ_[l]) ^ r * -(q : ℚ_[l])
    rw [hYg g]
    linear_combination hqr'
  choose c hc using hc
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, coeff_coefMap, hc g]
  simp [smul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.TotKill
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_tot_mem (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : ℕ) [NeZero N] (g : G E Ω) : g ^ N.totient ∈ fixMu E Ω N := by
  obtain ⟨b, hb⟩ := (liftEx E Ω N).2 g.toRingEquiv
  intro x hx
  have h : ∀ k : ℕ, (g ^ k) x = x ^ ((b : ZMod N).val ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, pow_succ', pow_mul]
      congr 1
      exact hb x hx
  rw [h, pow_eq_pow_mod _ hx, (Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime b) : _ % N = 1 % N),
    ← pow_eq_pow_mod _ hx, pow_one]

theorem UpperTheory.V.Odd.totKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (N : ℕ) [NeZero N], e ≠ 0 → Procyc E Ω l → ∀ x : H1 (qzTw D e), (∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D e x u = 0) → N.totient • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ he hP x hx
  have hadd : ∀ a b : Uinf E Ω l, resInf D e x (a * b) = resInf D e x a + resInf D e x b := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hchi : ∀ g : G E Ω, D.chi (toGS Ω _ g) = cycZ E Ω l g := fun g => DFunLike.congr_fun D.hchi g
    have htriv : ∀ g : G E Ω, cycZ E Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
      rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
    have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
    intro a b
    rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  have hpow : ∀ (u : Uinf E Ω l) (k : ℕ), resInf D e x (u ^ k) = k • resInf D e x u := by
    intro u k
    induction k with
    | zero =>
      have := hadd 1 1
      rw [one_mul] at this
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 this
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  apply resInfInj E Ω l D e he hP
  rw [map_nsmul, map_zero]
  funext u
  rw [Pi.smul_apply, ← hpow]
  exact hx _ (by rw [Subgroup.coe_pow]; exact pow_tot_mem E Ω N u.1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrSel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.unrSel :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], (∃ ζ : E, IsPrimitiveRoot ζ l) → ∃ f : UnrHom E Ω l → SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l), Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ hζE
  obtain ⟨ζ₀, hζ₀⟩ := hζE
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
  have hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l := hζ₀.map_of_injective (algebraMap E Ω).injective
  have hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧
      ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β := by
    intro φ
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above E l) l := by
    intro φ
    show ∀ v ∉ Above E l, _
    intro v hv
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_
    intro g hg
    have hnot : ¬ A.valuation (l : Ω) < 1 := by
      intro h
      apply hv
      have hp := hA (l : 𝓞 E)
      have he : algebraMap E Ω (((l : 𝓞 E) : E)) = (l : Ω) := by simp
      exact hp.mp (he ▸ h)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := by
    intro φ h
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)
  have hcΩ : algebraMap E Ω (c : E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) =
      algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap E Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]
  have hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))
  have hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1 := by
    apply mul_right_cancel₀ hγ0
    rw [one_mul, ← hgγ', hgγ]
  have hpow := ((div_eq_one_iff_eq hζb).mp hq).symm
  exact ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
end

