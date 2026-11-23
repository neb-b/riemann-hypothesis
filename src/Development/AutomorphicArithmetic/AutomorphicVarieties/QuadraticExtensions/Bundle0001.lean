module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem ker_congr (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m n : ℕ) [NeZero m] [NeZero n]
    (h : m = n) : (galChar Ω m).ker = (galChar Ω n).ker := by
  subst h
  rfl

private theorem prim_lemma (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω)
    (Polynomial.degree_cyclotomic_pos m Ω (NeZero.pos m)).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

private theorem galChar_eq_of_apply_primitiveRoot_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m]
    (g : G ℚ Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) (k : ℕ) (hk : g ζ = ζ ^ k) :
    (galChar Ω m g : ZMod m) = k := by
  have h1 := galChar_spec m g ζ hζ.pow_eq_one
  rw [hk] at h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, NeZero.pos m, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.mp h1
  rw [← hζ.eq_orderOf] at h2
  rw [← ZMod.natCast_zmod_val (galChar Ω m g : ZMod m)]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h2).symm

private theorem galChar_val_cast_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    (((galChar Ω N g : ZMod N).val : ℕ) : ZMod m) = (galChar Ω m g : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω N
  obtain ⟨d, hd⟩ := h
  have hμ : IsPrimitiveRoot (ζ ^ d) m := hζ.pow (NeZero.pos N) (by rw [hd, mul_comm])
  refine (galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g (ζ ^ d) hμ _ ?_).symm
  rw [map_pow, galChar_spec N g ζ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    ZMod.unitsMap h (galChar Ω N g) = galChar Ω m g := by
  ext
  rw [← galChar_val_cast_eq_galChar_of_dvd Ω m N h g, ← ZMod.cast_eq_val]
  rfl

private theorem galChar_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    Function.Surjective (galChar Ω m) := by
  intro u
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  have hcop : Nat.Coprime (u : ZMod m).val m := ZMod.val_coe_unit_coprime u
  have hμ : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m := hζ.pow_of_coprime _ hcop
  have hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ := by
    have e1 := Polynomial.cyclotomic_eq_minpoly_rat hμ (NeZero.pos m)
    have e2 := Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)
    convert e1.symm.trans e2 <;> exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  have hg' : g ζ = ζ ^ (u : ZMod m).val := (AlgEquiv.smul_def g ζ).symm.trans hg
  refine ⟨g, ?_⟩
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ _ hg', ZMod.natCast_zmod_val]

private theorem isOpen_galChar_ker (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    IsOpen ((galChar Ω m).ker : Set (G ℚ Ω)) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro g hg
  have hfix : g ζ = ζ ^ 1 := by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
      (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))
  rw [MonoidHom.mem_ker]
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ 1 hfix]
  simp

theorem UpperTheory.V.Two.abBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], (∀ A B : AbF, abU Ω (A.sup B) = abU Ω A ⊓ abU Ω B) ∧ (∀ A : AbF, (abU Ω A).index = A.deg ∧ A.deg ≠ 0 ∧ IsOpen (abU Ω A : Set (G ℚ Ω)) ∧ (galChar Ω A.m).ker ≤ abU Ω A) ∧
      (∀ (A : AbF) (N : ℕ) [NeZero N], A.m ∣ N → ∀ g, g ∈ abU Ω A ↔ A.ker (galChar Ω N g : ZMod N).val) ∧ ∀ (m : ℕ) [NeZero m], abU Ω (AbF.cyc m) = (galChar Ω m).ker := by
  intro Ω _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    ext g
    rw [Subgroup.mem_inf]
    show ZMod.unitsMap (dvd_mul_right A.m B.m) (galChar Ω (A.m * B.m) g) ∈ A.H ∧
        ZMod.unitsMap (dvd_mul_left B.m A.m) (galChar Ω (A.m * B.m) g) ∈ B.H ↔
      galChar Ω A.m g ∈ A.H ∧ galChar Ω B.m g ∈ B.H
    rw [unitsMap_galChar_eq_galChar_of_dvd Ω A.m (A.m * B.m) (dvd_mul_right _ _) g,
      unitsMap_galChar_eq_galChar_of_dvd Ω B.m (A.m * B.m) (dvd_mul_left _ _) g]
  · intro A
    refine ⟨Subgroup.index_comap_of_surjective _ (galChar_surjective Ω A.m), Subgroup.index_ne_zero_of_finite, ?_, ?_⟩
    · refine Subgroup.isOpen_mono ?_ (isOpen_galChar_ker Ω A.m)
      intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
    · intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
  · intro A N _ hN g
    simp only [abU, Subgroup.mem_comap, AbF.ker]
    rw [galChar_val_cast_eq_galChar_of_dvd Ω A.m N hN g]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, hEq⟩
      rwa [← Units.ext hEq]
  · intro m _
    have hm : (AbF.cyc m).m = m := max_eq_left NeZero.one_le
    show Subgroup.comap _ ⊥ = _
    rw [MonoidHom.comap_bot]
    exact ker_congr Ω _ _ hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abExists :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L := by
  intro A
  obtain ⟨L, hF, hN, h, -⟩ := UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg A
  exact ⟨L, hF, hN, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbProps
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abProps :
    ∀ (A : AbF) (L : Type) [Field L] [NumberField L], IsAbField A L → IsAbelianGalois ℚ L ∧ Module.finrank ℚ L = A.deg ∧ Nonempty (L →ₐ[ℚ] CyclotomicField A.m ℚ) := by
  intro A L _ _ hA
  obtain ⟨N, hN, j, ζ, hmN, hζ, h⟩ := hA
  haveI := hN
  haveI hcN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI hab : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfix : ∀ τ : Gal(CyclotomicField N ℚ/ℚ),
      τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ y : L, τ (j y) = j y := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro H y
      exact H _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
    · intro H x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hx
      exact H y
  have hpow : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N).val) :=
    fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm
  have hker : ∀ v : (ZMod N)ˣ, A.ker ((v : ZMod N).val) ↔ ZMod.unitsMap hmN v ∈ A.H := by
    intro v
    have hc : ((ZMod.unitsMap hmN v : (ZMod A.m)ˣ) : ZMod A.m) = (((v : ZMod N).val : ℕ) : ZMod A.m) := by
      rw [ZMod.natCast_val]
      rfl
    constructor
    · rintro ⟨u, hu, hua⟩
      have : u = ZMod.unitsMap hmN v := Units.ext (hua.trans hc.symm)
      rwa [← this]
    · intro hv
      exact ⟨_, hv, hc⟩
  have hinj : Function.Injective (hζ.autToPow ℚ) := hζ.autToPow_injective ℚ
  have hcard : Nat.card Gal(CyclotomicField N ℚ/ℚ) = Nat.card (ZMod N)ˣ :=
    Nat.card_congr (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero N))).toEquiv
  have hsurj : Function.Surjective (hζ.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2
  refine ⟨IsAbelianGalois.of_algHom j, ?_, ?_⟩
  · rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    change Module.finrank ℚ j.fieldRange = _
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    have hS : j.fieldRange.fixingSubgroup = (A.H.comap (ZMod.unitsMap hmN)).comap (hζ.autToPow ℚ) := by
      ext τ
      rw [hfix, h τ _ (hpow τ)]
      exact hker _
    rw [hS, Subgroup.index_comap_of_surjective _ hsurj,
      Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hmN)]
    rfl
  · have hdvd : N / A.m ∣ N := Nat.div_dvd_of_dvd hmN
    have hp0 : N / A.m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hmN) A.pos).ne'
    have hζm : IsPrimitiveRoot (ζ ^ (N / A.m)) A.m := by
      have := hζ.pow_of_dvd hp0 hdvd
      rwa [Nat.div_div_self hmN (NeZero.ne N)] at this
    haveI : NeZero A.m := ⟨A.pos.ne'⟩
    haveI hcm : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
      CyclotomicField.isCyclotomicExtension A.m ℚ
    haveI : IsCyclotomicExtension {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) :=
      hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hMC : j.fieldRange ≤ IntermediateField.adjoin ℚ {ζ ^ (N / A.m)} := by
      rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}),
        IntermediateField.le_iff_le]
      intro τ hτ
      rw [hfix, h τ _ (hpow τ)]
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have h1 : τ (ζ ^ (N / A.m)) = ζ ^ (N / A.m) :=
        hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
      rw [map_pow, hpow τ, ← pow_mul, mul_comm, pow_mul] at h1
      generalize ((hζ.autToPow ℚ τ : ZMod N)).val = a at h1 ⊢
      have hfo : IsOfFinOrder (ζ ^ (N / A.m)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζm.pow_eq_one⟩
      have h2 : a ≡ 1 [MOD A.m] := by
        rw [hζm.eq_orderOf]
        exact hfo.pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1)
      refine ⟨1, one_mem _, ?_⟩
      rw [Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact h2.symm
    exact ⟨(IsCyclotomicExtension.algEquiv {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)})
      (CyclotomicField A.m ℚ)).toAlgHom.comp
        ((IntermediateField.inclusion hMC).comp (AlgEquiv.ofInjectiveField j).toAlgHom)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardClDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
    [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
  refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
  show Nat.card (Module.Dual (ZMod l) V) ≤ _
  rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

private theorem cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
    (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
    CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
  have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
    intro p c n
    induction n with
    | zero =>
      have h := hm p 1 1
      rw [mul_one] at h
      simpa using h
    | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
  have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
  have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
    intro v
    change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  let φ : P → A →* Multiplicative (ZMod l) := fun p =>
    { toFun := fun a => Multiplicative.ofAdd (θ p a)
      map_one' := by
        show Multiplicative.ofAdd (θ p 1) = 1
        rw [h1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (θ p (a * b)) = _
        rw [hm]
        rfl }
  let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
    QuotientGroup.lift _ (φ p) (by
      rintro _ ⟨c, rfl⟩
      show Multiplicative.ofAdd (θ p (c ^ l)) = 1
      rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl)
  let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
      show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
      rw [map_mul]
      rfl)
  have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
  have hinj : Function.Injective Φ := by
    intro p q h
    apply hθ
    funext a
    rw [← hΦ p a, ← hΦ q a, h]
  letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
  exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
    ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
      (M₁ := ZMod l)).comp hinj)

theorem UpperTheory.V.Two.cardClDual :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (N : ℕ), CardLe (ClDual K N (ZMod l) (ZMod l)) (Nat.card (ClassGroup (𝓞 K) ⧸ (powMonoidHom l : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)) := by
  intro K _ _ l _ N
  exact cardLe_hom (ClassGroup (𝓞 K)) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardUnion
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.cardUnion :
    ∀ (P : Type) (S : ℕ → Set P) (b : ℕ), Monotone S → (∀ x, ∃ n, x ∈ S n) → (∀ n, CardLe (S n) b) → CardLe P b := by
  intro P S b hmono hcov hcard
  choose m hm using hcov
  have key : ∀ T : Finset P, T.card ≤ b := by
    intro T
    classical
    obtain ⟨hfN, hbN⟩ := hcard (T.sup m)
    have hsub : (↑T : Set P) ⊆ S (T.sup m) := by
      intro x hx
      exact hmono (Finset.le_sup (f := m) hx) (hm x)
    have hfin : (S (T.sup m)).Finite := Set.toFinite _
    have h1 := Nat.card_mono hfin hsub
    have h2 : Nat.card (↑T : Set P) = T.card := by simp
    omega
  have hfin : Finite P := by
    by_contra hnot
    rw [not_finite_iff_infinite] at hnot
    obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq P (b + 1)
    have := key T
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite P
  classical
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact key _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DegBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.deg_sup_le (A B : AbF) : (A.sup B).deg ≤ A.deg * B.deg := by
  haveI : NeZero (A.m * B.m) := ⟨(Nat.mul_pos A.pos B.pos).ne'⟩
  have h1 := A.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right A.m B.m))
  have h2 := B.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_left B.m A.m))
  unfold AbF.deg
  rw [← h1, ← h2]
  exact Subgroup.index_inf_le

private theorem UpperTheory.V.Two.deg_cyc_four : (AbF.cyc 4).deg = 2 := by
  show (⊥ : Subgroup (ZMod 4)ˣ).index = 2
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

private theorem UpperTheory.V.Two.deg_quad_dvd (p : ℕ) (hp : p.Prime) : (AbF.quad p).deg ∣ 2 := by
  show ((powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range).index ∣ 2
  have hp' : (max p 1).Prime := by rwa [max_eq_left hp.pos]
  haveI := Fact.mk hp'
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_dvd_right _ _

theorem UpperTheory.V.Two.degBasic :
    (∀ A B : AbF, (A.sup B).deg ≤ A.deg * B.deg) ∧ (AbF.cyc 4).deg = 2 ∧ (∀ p : ℕ, p.Prime → (AbF.quad p).deg ∣ 2) ∧ ∀ (M : AbF) (q d : ℕ), q.Prime → d.Prime → (base2 M q d).deg ≤ 8 * M.deg := by
  refine ⟨deg_sup_le, deg_cyc_four, deg_quad_dvd, fun M q d hq hd => ?_⟩
  have h1 : (withI M).deg ≤ M.deg * 2 := deg_cyc_four ▸ deg_sup_le M (AbF.cyc 4)
  have hq2 := Nat.le_of_dvd two_pos (deg_quad_dvd q hq)
  have hd2 := Nat.le_of_dvd two_pos (deg_quad_dvd d hd)
  calc (base2 M q d).deg ≤ ((withI M).sup (AbF.quad q)).deg * (AbF.quad d).deg := deg_sup_le _ _
    _ ≤ ((withI M).deg * (AbF.quad q).deg) * 2 := Nat.mul_le_mul (deg_sup_le _ _) hd2
    _ ≤ (M.deg * 2 * 2) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 hq2)
    _ = 8 * M.deg := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ExtTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.extTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (h : U ≤ V) (σ : Γ) (hσ : σ ∈ V) (h2 : σ * σ ∈ U), IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      ∀ φ ∈ CharOff U S 2, (∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ u' = φ u) → φ ⟨σ * σ, h2⟩ = 0 →
      ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u.1, h u.2⟩ = φ u := by
  intro Γ _ _ _ U V S h σ hσ h2 hopen hidx hσU hS φ hφ hinv hσσ
  classical
  obtain ⟨hlc, hadd, hoff⟩ := hφ
  have key : ∀ a b : Γ, a ∈ V → b ∈ V → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := by
    intro a b ha hb
    have := Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf V) hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hσi : σ⁻¹ ∉ U := fun hh => hσU (by simpa using U.inv_mem hh)
  let Φ : Γ → ZMod 2 := fun g => if hg : g ∈ U then φ ⟨g, hg⟩ else 0
  have hΦ : ∀ g (hg : g ∈ U), Φ g = φ ⟨g, hg⟩ := fun g hg => dif_pos hg
  have hΦadd : ∀ a b, a ∈ U → b ∈ U → Φ (a * b) = Φ a + Φ b := by
    intro a b ha hb
    rw [hΦ a ha, hΦ b hb, hΦ _ (U.mul_mem ha hb), ← hadd]
    rfl
  have hR : ∀ a, a ∈ V → a ∉ U → a * σ ∈ U := fun a ha haU =>
    (key a σ ha hσ).2 (by simp [haU, hσU])
  have hL : ∀ a, a ∈ V → a ∉ U → σ⁻¹ * a ∈ U := fun a ha haU =>
    (key σ⁻¹ a (V.inv_mem hσ) ha).2 (by simp [haU, hσi])
  have hconj : ∀ a, a ∈ U → σ⁻¹ * a * σ ∈ U := by
    intro a ha
    refine hR _ (V.mul_mem (V.inv_mem hσ) (h ha)) ?_
    rw [key _ _ (V.inv_mem hσ) (h ha)]
    simp [ha, hσi]
  have hΦconj : ∀ a, a ∈ U → Φ (σ⁻¹ * a * σ) = Φ a := by
    intro a ha
    rw [hΦ a ha, hΦ _ (hconj a ha)]
    exact hinv _ _ rfl
  have hΦσ : Φ (σ * σ) = 0 := by rw [hΦ _ h2, hσσ]
  let ψ : V → ZMod 2 := fun v => if v.1 ∈ U then Φ v.1 else Φ (v.1 * σ)
  have hψU : ∀ v : V, v.1 ∈ U → ψ v = Φ v.1 := fun v hv => if_pos hv
  have hψN : ∀ v : V, v.1 ∉ U → ψ v = Φ (v.1 * σ) := fun v hv => if_neg hv
  have hψadd : ∀ a b : V, ψ (a * b) = ψ a + ψ b := by
    intro a b
    have hk := key a.1 b.1 a.2 b.2
    by_cases ha : a.1 ∈ U <;> by_cases hb : b.1 ∈ U
    · rw [hψU a ha, hψU b hb, hψU (a * b) (U.mul_mem ha hb)]
      exact hΦadd _ _ ha hb
    · have hab : (a * b).1 ∉ U := fun hh => hb ((hk.1 hh).1 ha)
      rw [hψU a ha, hψN b hb, hψN _ hab, ← hΦadd _ _ ha (hR _ b.2 hb), Subgroup.coe_mul, mul_assoc]
    · have hab : (a * b).1 ∉ U := fun hh => ha ((hk.1 hh).2 hb)
      rw [hψN a ha, hψU b hb, hψN _ hab, ← hΦconj _ hb, ← hΦadd _ _ (hR _ a.2 ha) (hconj _ hb), Subgroup.coe_mul]
      congr 1
      group
    · have hab : (a * b).1 ∈ U := hk.2 (by simp [ha, hb])
      have e1 : Φ (b.1 * σ) = Φ (σ⁻¹ * b.1) := by
        rw [← hΦconj _ (hR _ b.2 hb), show σ⁻¹ * (b.1 * σ) * σ = (σ⁻¹ * b.1) * (σ * σ) by group,
          hΦadd _ _ (hL _ b.2 hb) h2, hΦσ, add_zero]
      rw [hψN a ha, hψN b hb, hψU _ hab, e1, ← hΦadd _ _ (hR _ a.2 ha) (hL _ b.2 hb), Subgroup.coe_mul]
      congr 1
      group
  have hφ1 : φ 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact left_eq_add.1 this
  refine ⟨ψ, ⟨?_, hψadd, ?_⟩, ?_, ?_⟩
  · obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hlc {0})
    have hW : IsOpen ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O) :=
      hopen.inter (hO.preimage continuous_subtype_val)
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O),
      hW.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · have h1 : (1 : U) ∈ Subtype.val ⁻¹' O := by rw [hOe]; exact hφ1
      simp only [Set.mem_preimage, inv_mul_cancel]
      exact ⟨(U.subgroupOf V).one_mem, h1⟩
    · rintro y ⟨hy1, hy2⟩
      have hy1' : (x⁻¹ * y).1 ∈ U := hy1
      have h0 : (⟨_, hy1'⟩ : U) ∈ Subtype.val ⁻¹' O := hy2
      rw [hOe] at h0
      have h0' : ψ (x⁻¹ * y) = 0 := by
        rw [hψU _ hy1', hΦ _ hy1']
        exact h0
      have := hψadd x (x⁻¹ * y)
      rwa [mul_inv_cancel_left, h0', add_zero] at this
  · intro v hv
    have hvU := hS _ hv v.2
    rw [hψU v hvU, hΦ _ hvU]
    exact hoff _ hv
  · rw [hψN _ hσU]
    exact hΦσ
  · intro u
    rw [hψU _ u.2]
    exact hΦ _ u.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem mem_princ_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : G ℚ Ω) : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ g ∈ (galChar Ω (l ^ n)).ker := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ ℚ Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  rw [h1, cyclotomicCharacter.toZModPow, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem UpperTheory.V.Two.levChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (U : Subgroup (G ℚ Ω)), levU l U n = U ⊓ (galChar Ω (l ^ n)).ker ∧ (cycZ ℚ Ω l).ker ≤ (galChar Ω (l ^ n)).ker := by
  intro Ω _ _ _ l _ n U
  refine ⟨?_, fun g hg => ?_⟩
  · ext g
    rw [levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]
  · rw [← mem_princ_iff, MonoidHom.mem_ker.1 hg]
    exact one_mem _
end

