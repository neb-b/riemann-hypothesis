module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XNormDiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChiDvd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem chi_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (g : G ℚ Ω) (h : g ∈ fixMu ℚ Ω (l ^ n)) :
    (l : O) ^ n ∣ (chiO ℚ Ω l O g : O) - 1 := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h1 : (1 : ZMod (l ^ n)) = modularCyclotomicCharacter Ω
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) := by
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    exact h (t : Ω) (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val.toZModPow n = 1 := by
    rw [cyclotomicCharacter.toZModPow, ← h1]
  have h3 : (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val - 1 := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h2, map_one, sub_self]
  have h4 := map_dvd (algebraMap ℤ_[l] O) h3
  simpa [chiO, cycZ] using h4

theorem UpperTheory.V.ML.step :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F N q : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → F ∣ N → N ≠ 0 → q.Prime → q ≡ 1 [MOD F] →
    ∀ ν : G ℚ Ω → QO l O, IsNu (l ^ m) F (N * q) (dualChar l α) ν → ∀ (δ : G ℚ Ω) (a₀ a : O) (w₀ : QO l O), a₀ ∣ a → a ∣ (l : O) ^ m → (∀ y : O, y • w₀ = 0 ↔ a ∣ y) →
    (∀ u ∈ fixMu ℚ Ω F, a • ν u = 0) → ∀ c ∈ ShT (QO l O) α δ F a₀,
    (∀ A : ValuationSubring Ω, Over A N → ¬ Over A F → ¬ Over A q → ∀ g ∈ Dec (F := ℚ) A, c g = 0) →
    ∀ A : ValuationSubring Ω, Over A q → ∀ g ∈ Dec (F := ℚ) A, ∀ τ ∈ Ine (F := ℚ) A, ∀ y : O, ν τ = y • w₀ → y • c g = 0 := by
  intro hRec Ω _ _ _ l _ O _ _ _ _ _ N₀ m F N q α hD hFN hN hq hq1 ν hν δ a₀ a w₀ ha₀a hal hw₀ hνa c hc hyp A hA g hg τ hτ y hy
  obtain ⟨⟨hlc, hcoc⟩, -, hac0, hunrc, hlocc⟩ := hc
  have hl : l.Prime := Fact.out
  have hF : F ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.mp hFN)
  have hlmF : l ^ m ∣ F := Dvd.intro_left N₀ hD.lev.symm
  have hlF : l ∣ F := (dvd_pow_self l (by have := hD.pos; omega)).trans hlmF
  have hlN : l ∣ N := hlF.trans hFN
  have hql : q ≠ l := by
    intro hql
    have h := hq1.of_dvd hlF
    rw [hql] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt] at h
    exact absurd h (by norm_num)
  obtain ⟨-, hopen, -, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  obtain ⟨-, hfrobEx, hoverMul, hcopNot, hIne, -, hPows, -, hplace, -⟩ := placeBasic Ω
  have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
  have hAF : ¬Over A F := hcopNot A q F hcop hA
  have hIneA : Ine A ≤ fixMu ℚ Ω F := hIne A F hAF
  have hdivA : ∀ x ∈ fixMu ℚ Ω F, a ∣ (α x : O) - 1 := fun x hx => hal.trans (hD.triv x hx)
  have hl0 : (l : O) ≠ 0 := by
    obtain ⟨hinj, -⟩ := dvrFacts l O
    intro h0
    have h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by simpa using h0
    exact (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℤ_[l]) ≠ 0) (hinj h1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero m hl0 (zero_dvd_iff.mp hal)
  let S : Subgroup (G ℚ Ω) :=
    { carrier := {x | a ∣ (α x : O) - 1}
      mul_mem' := fun {x z} hx hz => by
        have e : (α (x * z) : O) - 1 = (α x : O) * ((α z : O) - 1) + ((α x : O) - 1) := by
          rw [map_mul, Units.val_mul]; ring
        show a ∣ (α (x * z) : O) - 1
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_right hz _) hx
      one_mem' := by
        show a ∣ (α 1 : O) - 1
        simp
      inv_mem' := fun {x} hx => by
        have hxx : (α x⁻¹ : O) * (α x : O) = 1 := by
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        have e : (α x⁻¹ : O) - 1 = -(α x⁻¹ : O) * ((α x : O) - 1) := by
          linear_combination hxx
        show a ∣ (α x⁻¹ : O) - 1
        rw [e]
        exact dvd_mul_of_dvd_right hx _ }
  have hSo : IsOpen {x : G ℚ Ω | a ∣ (α x : O) - 1} :=
    Subgroup.isOpen_mono (H₁ := fixMu ℚ Ω F) (H₂ := S) (fun x hx => hdivA x hx) hopen
  obtain ⟨φ, hφ⟩ := hfrobEx A q hq hA
  have hφF : φ ∈ fixMu ℚ Ω F := by
    intro z hz
    rw [hPows A q F φ hφ hAF z hz, pow_eq_pow_mod q hz, hq1, ← pow_eq_pow_mod 1 hz, pow_one]
  obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
  have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
  have hDecA : Dec A ≤ fixMu ℚ Ω F := Kum.decGen ℚ Ω A v φ (fixMu ℚ Ω F) hv hfr hopen hIneA hφF
  obtain ⟨δ', hδ'⟩ := hD.notCyc
  have hβ : IsUnit (((dualChar l α) δ' : O) - 1) := by
    have hu : (((α δ')⁻¹ : Oˣ) : O) * (α δ' : O) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((dualChar l α) δ' : O) - 1 =
        -(((α δ')⁻¹ : Oˣ) : O) * ((α δ' : O) - (chiO ℚ Ω l O δ' : O)) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      linear_combination hu
    rw [e]
    exact (Units.isUnit _).neg.mul hδ'
  obtain ⟨n, hncoc, hnν, hnform⟩ := ext Ω O (QO l O) (l ^ m) F (N * q) hF (dualChar l α) ν hν δ' hβ
  have han : ∀ x, a • n x = 0 := by
    intro x
    obtain ⟨u, hu, z, hz⟩ := hnform x
    rw [hz, smul_comm, hνa u hu, smul_zero]
  have hac : ∀ x, a • c x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := ha₀a
    rw [hk, mul_comm, mul_smul, hac0, smul_zero]
  have hnotF : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ¬Over B F := by
    intro B hB hBF
    obtain ⟨k, hk⟩ := hFN
    exact hB ((hoverMul B N q).mpr (Or.inl (by rw [hk]; exact (hoverMul B F k).mpr (Or.inl hBF))))
  have hunr : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ∀ x ∈ Ine B,
      a ∣ (α x : O) - 1 ∧ c x = 0 ∧ n x = 0 := by
    intro B hB x hx
    have hBF := hnotF B hB
    have hxF := hIne B F hBF hx
    exact ⟨hdivA x hxF, hunrc B hBF x hx, by rw [hnν x hxF]; exact hν.unr B hB x hx⟩
  have hloc : ∀ B : ValuationSubring Ω, Over B N → ¬Over B q →
      ∃ w, a • w = 0 ∧ ∀ x ∈ Dec B, c x = (α x : O) • w - w := by
    intro B hBN hBq
    by_cases hBF : Over B F
    · obtain ⟨w, hw, hw'⟩ := hlocc B hBF
      obtain ⟨k, hk⟩ := ha₀a
      exact ⟨w, by rw [hk, mul_comm, mul_smul, hw, smul_zero], hw'⟩
    · exact ⟨0, smul_zero _, fun x hx => by rw [hyp B hBN hBF hBq x hx, smul_zero, sub_zero]⟩
  have hdec : ∀ x ∈ Dec A, a ∣ (α x : O) - 1 ∧ a ∣ ((dualChar l α) x : O) - 1 := by
    intro x hx
    have hxF := hDecA hx
    refine ⟨hdivA x hxF, ?_⟩
    have hxl : x ∈ fixMu ℚ Ω (l ^ m) := fixMu_le ℚ Ω hlmF hxF
    have h1 := chi_dvd Ω l O m x hxl
    have h2 := hdivA x⁻¹ (inv_mem hxF)
    have e : ((dualChar l α) x : O) - 1 =
        (chiO ℚ Ω l O x : O) * ((α x⁻¹ : O) - 1) + ((chiO ℚ Ω l O x : O) - 1) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (hal.trans h1)
  have hine : ∀ x ∈ Ine A, c x = 0 := fun x hx => hunrc A hAF x hx
  have hnτ : n τ = y • w₀ := by rw [hnν τ (hIneA hτ)]; exact hy
  exact hRec Ω l hD.odd_l O α a ha0 w₀ hw₀ hSo N q hN hlN hq hql c n ⟨hlc, hcoc⟩ hncoc hac han hunr hloc
    A hA hdec hine g hg τ hτ y hnτ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_eq_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {M : ℕ} (hM : M ≠ 0) {x : Ω}
    (h : A.valuation (x ^ M) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le h1 hM).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hM).ne'

theorem UpperTheory.V.ML.kolUnr :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n r a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation y = 1) → ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    ∀ A : ValuationSubring Ω, ¬ Over A (F * r * n) → ∀ g ∈ Ine (F := ℚ) A, κ g = 0 := by
  intro Ω _ _ _ M F n r a _ hFn hMF ζ hζ δ hδ y hy hfix hunit κ hκ A hA g hg
  obtain ⟨-, -, hmul, -, hine, hroot, -, -, -, hconj⟩ := placeBasic Ω
  have hM : M ≠ 0 := NeZero.ne M
  have hA1 : ¬ Over A (F * n) := fun h => hA <| by
    rw [mul_right_comm]
    exact (hmul A _ _).2 (Or.inl h)
  have hAr : ¬ Over A r := fun h => hA <| (hmul A _ _).2 (Or.inl ((hmul A _ _).2 (Or.inr h)))
  have hAF : ¬ Over A F := fun h => hA1 ((hmul A _ _).2 (Or.inl h))
  have hAM : ¬ Over A M := fun h => hAF <| by
    obtain ⟨c, rfl⟩ := hMF
    exact (hmul A _ _).2 (Or.inl h)
  have hgFn : g ∈ fixMu ℚ Ω (F * n) := hine A _ hA1 hg
  have hgF : g ∈ fixMu ℚ Ω F := hine A _ hAF hg
  obtain ⟨Y, hY, -⟩ := id hκ
  have key := (kolHom Ω M F n a hFn hMF ζ hζ δ hδ y hy hfix κ hκ).2.2 Y hY g hgF 1
    (by rw [hfix g hgFn, one_pow, div_self hy])
  have h1 : opP δ a (1 : Ω) = 1 := by simp [opP]
  rw [h1, div_one] at key
  have hvY : A.valuation Y = 1 := val_eq_one_of_pow A hM (by rw [hY]; exact hunit A hAr)
  have hvδ : A.valuation (δ Y) = 1 := by
    refine val_eq_one_of_pow A hM ?_
    rw [← map_pow δ, hY]
    have hB : ¬ Over (δ⁻¹ • A) r := fun h => hAr <| by
      have := ((hconj A δ⁻¹).2.2.2.1 (r : Ω)).1 (by rw [map_natCast]; exact h)
      exact this
    have := ((hconj (δ⁻¹ • A) δ).2.2.2.2 y).2 (hunit _ hB)
    rwa [smul_inv_smul] at this
  have hu : A.valuation (opP δ a Y) = 1 := by
    rw [opP, map_div₀, map_pow, hvY, hvδ, one_pow, div_one]
  have hu0 : opP δ a Y ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hlt : A.valuation (ζ ^ (κ g).val - 1) < 1 := by
    have e : ζ ^ (κ g).val - 1 = (g (opP δ a Y) - opP δ a Y) / opP δ a Y := by
      rw [key, sub_div, div_self hu0]
    rw [e, map_div₀, hu, div_one]
    exact hg.2 _ hu.le
  have h2 : ζ ^ (κ g).val = 1 := hroot A M _ hAM (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) hlt
  have h3 : M ∣ (κ g).val := (hζ.pow_eq_one_iff_dvd _).1 h2
  exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

private theorem lift_sg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (b : (ZMod N)ˣ) (g : G ℚ Ω) (hg : Lifts N b g) (x : K) :
    g (ι x) = ι (sg N K b x) := by
  refine DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) (ι.comp (sg N K b).toRingEquiv.toRingHom)
    fun y hy => ?_) x
  change g (ι y) = ι (sg N K b y)
  rw [hg _ (by rw [← map_pow, hy, map_one]), sg_apply N K b hy, map_pow]

private theorem fix_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (g : G ℚ Ω) (hg : g ∈ fixMu ℚ Ω N) (x : K) :
    g (ι x) = ι x :=
  DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) ι
    fun y hy => hg _ (by rw [← map_pow, hy, map_one])) x

private theorem inv_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N q : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q) (g : G ℚ Ω)
    (hg : Pows N q g) (x : K) : g⁻¹ (ι x) = ι ((sg N K u)⁻¹ x) := by
  have h : Lifts N u g := fun y hy => by rw [hg y hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  apply g.injective
  rw [lift_sg N ι u g h]
  change g (g.symm _) = ι (sg N K u ((sg N K u).symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem place_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : K →+* Ω) (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ w : HeightOneSpectrum (𝓞 K), ∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal := by
  letI : Algebra K Ω := ι.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (UpperTheory.V.Kum.placeDict K Ω).2.1 A hA

private theorem ne_top {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {n : ℕ} (hn : n ≠ 0)
    (h : Over A n) : A ≠ ⊤ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rintro rfl
  have h1 : (⊤ : ValuationSubring Ω).valuation (n : Ω)⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one] at h2
  exact lt_irrefl _ h2

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) : (⊤ : ValuationSubring Ω).valuation x = 1 := by
  have h (y : Ω) : (⊤ : ValuationSubring Ω).valuation y ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  refine le_antisymm (h x) ?_
  have h1 := h x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h1

private theorem tower {K K' Ω : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] (M N : ℕ)
    [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ K] [IsCyclotomicExtension {N} ℚ K'] (h : M ∣ N)
    (ι : K →+* Ω) (ι' : K' →+* Ω) : ∃ j : K →+* K', ∀ x, ι' (j x) = ι x := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  have hζ' := (IsCyclotomicExtension.zeta_spec N ℚ K').map_of_injective ι'.injective
  have key : ∀ x : K, ι x ∈ ι'.fieldRange := fun x => by
    have hx : x ∈ Algebra.adjoin ℚ {IsCyclotomicExtension.zeta M ℚ K} := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := h
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := ι x)
        (by rw [Set.mem_singleton_iff.1 hx, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow])
      exact ⟨_, (map_pow ι' _ i).trans hi⟩
    | algebraMap x => exact ⟨(x : K'), by simp⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  choose j hj using key
  exact ⟨{ toFun := j
           map_one' := ι'.injective (by rw [hj, map_one, map_one])
           map_mul' := fun x y => ι'.injective (by rw [map_mul, hj, hj, hj, map_mul])
           map_zero' := ι'.injective (by rw [hj, map_zero, map_zero])
           map_add' := fun x y => ι'.injective (by rw [map_add (f := _), hj, hj, hj, map_add (f := _)]) }, hj⟩

private def XO {Ω : Type} [Field Ω] (N b : ℕ) (A₀ : ValuationSubring Ω) (x : Ω) : Prop :=
  ∃ (_ : NeZero N) (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K) (ι : K →+* Ω)
    (v : HeightOneSpectrum (𝓞 K)) (X : K), (∀ y : 𝓞 K, A₀.valuation (ι (y : K)) < 1 ↔ y ∈ v.asIdeal) ∧
    IsX N K b v.asIdeal X ∧ x = ι X

private theorem xo_ex {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N b : ℕ) (hb : b < N)
    (A₀ : ValuationSubring Ω) (hA : A₀ ≠ ⊤) : ∃ x, XO N b A₀ x := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let K := CyclotomicField N ℚ
  haveI : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra := by
    have h := CyclotomicField.isCyclotomicExtension N ℚ
    have e : (DivisionRing.toRatAlgebra : Algebra ℚ K) = CyclotomicField.algebra N ℚ := Subsingleton.elim _ _
    rw [e]
    exact h
  let ι : K →+* Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom
  obtain ⟨v, hv⟩ := place_emb ι A₀ hA
  obtain ⟨X, hX⟩ := xEx N K b v.asIdeal hb v.ne_bot
  exact ⟨ι X, inferInstance, K, inferInstance, inferInstance, inferInstance, ι, v, X, hv, hX, rfl⟩

private theorem xo_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {N b r : ℕ} {A₀ : ValuationSubring Ω}
    (hr : Over A₀ r) {x : Ω} (h : XO N b A₀ x) :
    x ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g x = x) ∧ ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  have h0 : ι X ≠ 0 := (map_ne_zero ι).2 (left_ne_zero_of_mul_eq_one hX.1)
  refine ⟨h0, fun g hg => fix_emb N ι g hg X, fun A hA => ?_⟩
  by_cases ht : A = ⊤
  · rw [ht]; exact val_top h0
  obtain ⟨w, hw⟩ := place_emb ι A ht
  have h1 := UpperTheory.valuation_kummerElement_eq_one_of_not_over N K b r v w X hX ((hv r).1 (by simpa using hr))
    fun h => hA (by simpa using (hw r).2 h)
  exact (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω ι A w hw).eq_one_iff_eq_one.2 h1

private theorem xo_ord {Ω : Type} [Field Ω] [Algebra ℚ Ω] {F b r : ℕ} (hp : r.Prime) (h1 : r ≡ 1 [MOD F])
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x : Ω} (h : XO F b A₀ x) : HasOrd F r A₀ x fun t => th F b t := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  intro t σ hσ
  let w : HeightOneSpectrum (𝓞 K) := v.comap (sgO F K t).toRingHom (sgO F K t).surjective
  have hw : ∀ y : 𝓞 K, A₀.valuation ((σ.toRingEquiv.toRingHom.comp ι) (y : K)) < 1 ↔ y ∈ w.asIdeal := fun y => by
    change A₀.valuation (σ (ι y)) < 1 ↔ sgO F K t y ∈ v.asIdeal
    rw [lift_sg F ι t σ hσ, ← hv]
    rfl
  have h2 := UpperTheory.valuation_kummerElement_at_conjugate_prime F K b r v w X t hp h1 hX ((hv r).1 (by simpa using hr)) rfl
  rw [← map_zpow₀] at h2
  have h3 := ((UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω _ A₀ w hw).eq_iff).2 h2
  simpa using h3

private theorem xo_pair {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {M q b r : ℕ} (hp : r.Prime)
    (hq : q.Prime) (hco : q.Coprime M) (hr' : ¬ r ∣ q * M) (hbM : b < M) (hbq : b < q)
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x x' : Ω} (h : XO M b A₀ x) (h' : XO (q * M) b A₀ x') :
    ∃ s : ℕ, s ∣ orderOf (r : ZMod (q * M)) ∧
      (∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ φ : G ℚ Ω, Pows M q φ →
        ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧ nrm q τ x' = ζ * (x / φ⁻¹ x) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows M q φ → ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (x' - ζ * φ⁻¹ x ^ s) < 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  obtain ⟨_, K', _, _, _, ι', v', X', hv', hX', rfl⟩ := h'
  obtain ⟨j, hj⟩ := tower M (q * M) (dvd_mul_left M q) ι ι'
  letI : Algebra K K' := j.toAlgebra
  have hj' : ∀ x, ι' (algebraMap K K' x) = ι x := hj
  obtain ⟨s, hs, hn⟩ := UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf (q * M) r K K' hp hr' v v' ((hv' r).1 (by simpa using hr)) fun y => by
    rw [← hv, ← hv', ← hj']
    rfl
  have hXs := (xMul M K b).2.2.1 v.asIdeal X s v.ne_bot hX
  rw [← hn] at hXs
  have hu : ((ZMod.unitOfCoprime q hco : (ZMod M)ˣ) : ZMod M) = q := ZMod.coe_unitOfCoprime q hco
  refine ⟨s, hs, fun τ hτ hg φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨ζ, hζ, he⟩ := xNormDiv M q K K' hq _ hu b hbq v'.asIdeal X' (X ^ s) v'.ne_bot hX' hXs
    refine ⟨ι ζ, ?_, ?_⟩
    · rw [show 2 * (q * M) = 2 * M * q by ring, pow_mul, ← map_pow, hζ, map_one, one_pow]
    · rw [UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator Ω M q K K' ι' hq hco τ hτ hg, hj', he, inv_emb M q ι _ hu φ hφ]
      simp only [map_mul, map_div₀, map_pow, div_pow]
  · have hqr : r.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hr' (h.mul_right M)
    have hq' : (q : 𝓞 K') ∉ v'.asIdeal := fun h =>
      (placeBasic Ω).2.2.2.1 A₀ r q hqr hr (by simpa using (hv' q).2 h)
    have hc : IsCoprime v'.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hq' ((v'.isMaximal.eq_of_le hne le_sup_left).ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    obtain ⟨ζ, hζ, he⟩ := xCong M q K K' hq _ hu b hbM hbq v'.asIdeal X' (X ^ s) hc hX' hXs
    refine ⟨ι' ζ, by rw [← map_pow, hζ, map_one], fun A hA => ?_⟩
    obtain ⟨w, hw⟩ := place_emb ι' A (ne_top hq.ne_zero hA)
    have h3 := (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K' Ω ι' A w hw).lt_one_iff_lt_one.2 (he w ((hw q).1 (by simpa using hA)))
    rw [Valuation.comap_apply, map_sub, map_mul, hj', map_pow, map_pow, ← inv_emb M q ι _ hu φ hφ] at h3
    exact h3

theorem UpperTheory.V.ML.laxEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l F r b : ℕ) [NeZero F], l.Prime → r.Prime → r ≡ 1 [MOD F] → b < F → ∀ A₀ : ValuationSubring Ω, Over A₀ r →
    ∃ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s ∧ HasOrd F r A₀ (X 1) fun t => th F b t := by
  intro Ω _ _ _ l F r b _ hl hr h1 hb A₀ hA
  have hlt : ∀ d, d ≠ 0 → b < F * d := fun d hd => hb.trans_le (Nat.le_mul_of_pos_right F (Nat.pos_of_ne_zero hd))
  have hX : ∀ d : ℕ, ∃ x : Ω, d ≠ 0 → XO (F * d) b A₀ x := fun d => by
    by_cases hd : d = 0
    · exact ⟨0, fun h => absurd hd h⟩
    · obtain ⟨x, hx⟩ := xo_ex (F * d) b (hlt d hd) A₀ (ne_top hr.ne_zero hA)
      exact ⟨x, fun _ => hx⟩
  choose X hX using hX
  have hs : ∀ d q : ℕ, ∃ s : ℕ, q.Prime → ML.admitted l F r (q * d) → ¬ l ∣ s ∧
      (∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
        ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (X (q * d) - ζ * φ⁻¹ (X d) ^ s) < 1 := fun d q => by
    by_cases h : q.Prime ∧ ML.admitted l F r (q * d)
    swap
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
    obtain ⟨hq, ha⟩ := h
    have h0 : q * d ≠ 0 := ha.1.ne_zero
    have hd : d ≠ 0 := right_ne_zero_of_mul h0
    have he : F * (q * d) = q * (F * d) := by ring
    have hqF : q ≡ 1 [MOD F] := (ha.2 q hq (dvd_mul_right q d)).2.1
    have hco : q.Coprime (F * d) := Nat.Coprime.mul_right
      (by rw [Nat.Coprime, hqF.gcd_eq]; exact Nat.gcd_one_left F) (Nat.coprime_of_squarefree_mul ha.1)
    have hFq : F < q := by
      have h2 := Nat.le_of_dvd (by have := hq.two_le; omega) ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)
      have := hq.two_le
      omega
    obtain ⟨hc1, hc2⟩ := UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level l F r (q * d) (NeZero.ne F) hl hr h1 ha
    have hx' := hX (q * d) h0
    rw [he] at hc1 hc2 hx'
    obtain ⟨s, hs, h2, h3⟩ := xo_pair hr hq hco hc2 (hlt d hd) (hb.trans hFq) hA (hX d hd) hx'
    rw [show 2 * (q * (F * d)) = 2 * F * (q * d) by ring] at h2 h3
    exact ⟨s, fun _ _ => ⟨fun h => hc1 (h.trans hs), h2, h3⟩⟩
  choose s hs using hs
  refine ⟨X, s, ⟨fun d hd => (xo_one hA (hX d hd.1.ne_zero)).1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.1,
    fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.2, fun d q hq ha => (hs d q hq ha).1,
    fun d q hq ha => (hs d q hq ha).2.1, fun d q hq ha => (hs d q hq ha).2.2⟩, ?_⟩
  have h := hX 1 one_ne_zero
  rw [mul_one] at h
  exact xo_ord hr h1 hA h
end

