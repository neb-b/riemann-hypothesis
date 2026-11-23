module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AuxwEx
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem ax_cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  apply Units.ext
  show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ l = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)
    simpa using this
  have hl1 : l ^ 1 ≠ 1 := by
    have := hl.out.one_lt
    rw [pow_one]
    omega
  rw [ZMod.val_one'' hl1, pow_one]
  exact hs _ ht'

theorem UpperTheory.V.Fr.auxw_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → ∃ w, FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨a, hη, hbar⟩ := hG.cyc
  have hM := hG.M_ne
  have hlM := hG.l_dvd
  have hL : M ^ (a + 1) * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hM) hQ
  obtain ⟨w, hw, hwgt, hw1⟩ := Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL
  have hMaL : M ^ a ∣ M ^ (a + 1) * Q := Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q
  have hlL : l ∣ M ^ (a + 1) * Q :=
    dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))
  have hML : M ∣ M ^ (a + 1) * Q := dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)
  have hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m := by
    intro m hm hwm
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm
    omega
  refine ⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩
  intro B' hB' s hs
  haveI := Fact.mk hw
  have fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ := by
    intro m hm
    have hcop : m.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs
    intro ζ hζ
    rw [hk ζ hζ]
    have hwk : w ^ k ≡ 1 [MOD m] := by
      have := (Nat.ModEq.of_dvd hm hw1).pow k
      rwa [one_pow] at this
    rw [pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact hη s (fix _ hMaL)
  · exact hbar s (fix _ hMaL)
  · rw [MonoidHom.mem_ker]
    change (Units.map _) ((cycMod ℚ Ω l 1) s) = 1
    rw [ax_cycMod_one l (fix l hlL), map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ClrkTr
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.clrk_tr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (U : Subgroup (G ℚ Ω)), U ≤ galOf ℚ F Ω → GC.clRk l (U.comap (galEmb ℚ F Ω)) = GC.clRk l U := by
  intro Ω _ _ _ l _ F _ _ _ U hU
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have hemb := (galEmbTop ℚ F Ω).1
  have hfam := (galEmbFam ℚ F Ω l).1
  let e : U.comap (galEmb ℚ F Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb ℚ F Ω u.1, u.2⟩
      invFun := fun u => ⟨Kum.toGal F hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Continuous e := (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  have hc' : Continuous e.symm := (hemb.continuous_iff.2 continuous_subtype_val).subtype_mk _
  have hI : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Ine (F := ℚ) A ↔ σ ∈ Ine (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).2 σ
  have hD : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Dec (F := ℚ) A ↔ σ ∈ Dec (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).1 σ
  have key : (Kum.XDual 1 U (ZMod l) (ZMod l)).map (LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).toLinearMap =
      Kum.XDual 1 (U.comap (galEmb ℚ F Ω)) (ZMod l) (ZMod l) := by
    ext φ
    constructor
    · rintro ⟨ψ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hc, fun a b => h2 (e a) (e b), fun A u h => h3 A (e u) ((hI A _).2 h),
        fun A hA u h => h4 A hA (e u) ((hD A _).2 h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨φ ∘ e.symm, ⟨h1.comp_continuous hc', fun a b => h2 (e.symm a) (e.symm b),
        fun A u h => h3 A (e.symm u) ((hI A _).1 h), fun A hA u h => h4 A hA (e.symm u) ((hD A _).1 h)⟩, rfl⟩
  unfold GC.clRk
  rw [← key]
  exact ((LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).submoduleMap _).rank_eq.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DualNontriv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem dual_nontriv (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Nontrivial V] :
    Nontrivial (Module.Dual K V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun φ => by
    rw [Subsingleton.elim φ 0]
    rfl)

theorem UpperTheory.V.Fr.st_loc :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] [Nontrivial M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (∀ g ∈ Dec (F := ℚ) A, cycMod ℚ Ω l 1 g = 1) → ∀ ρ : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M, (∀ g m, ρ g m = m) → Nat.card (H0 ρ) < Nat.card (H1 ρ) := by
  intro hFin hTate hEuler Ω _ _ _ l hl M _ _ _ _ _ _ A v hv hlv hcyc ρ htriv
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl.out⟩
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : Dec (F := ℚ) A × M => ρ p.1 p.2
    simp only [htriv]
    exact continuous_snd
  have hF := hFin ℚ Ω l 1 M A ρ v one_pos hv hcont
  have hE := (hEuler ℚ Ω l 1 M A ρ v one_pos hv hcont).2 hlv
  obtain ⟨⟨e⟩, -, -, -, hbij⟩ := hTate ℚ Ω l 1 M A ρ v one_pos hv hcont
  haveI : Finite (H2 ρ) := hF.2.2.1
  haveI : Finite (H0 ρ) := hF.1
  have hinv : ∀ φ : TDual (ZMod (l ^ 1)) M,
      φ ∈ H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _)) := by
    intro φ g
    apply LinearMap.ext
    intro m
    simp [twDual, hcyc g.1 g.2]
    show φ (ρ g⁻¹ m) = φ m
    rw [htriv]
  haveI : Nontrivial (TDual (ZMod (l ^ 1)) M) := dual_nontriv (ZMod (l ^ 1)) M
  obtain ⟨φ0, hφ0⟩ := exists_ne (0 : TDual (ZMod (l ^ 1)) M)
  set X := H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _))
  have hx0 : (⟨φ0, hinv φ0⟩ : X) ≠ 0 := fun h => hφ0 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod (l ^ 1)) X, f ⟨φ0, hinv φ0⟩ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff (ZMod (l ^ 1)) _).mp h)
  let ψ : X →ₗ[ZMod (l ^ 1)] H2 ((charRep ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype)).comp
      (MonoidHom.id _)) := e.symm.toLinearMap ∘ₗ f
  have hψ : ψ ≠ 0 := by
    intro h
    have h1 : ψ ⟨φ0, hinv φ0⟩ = 0 := by rw [h]; rfl
    exact hf (e.symm.map_eq_zero_iff.mp h1)
  obtain ⟨y, hy⟩ := hbij.2 ψ
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hψ (by rw [← hy, map_zero])
  haveI : Nontrivial (H2 ρ) := ⟨⟨y, 0, hy0⟩⟩
  rw [hE]
  exact lt_mul_of_one_lt_right (Nat.card_pos) Finite.one_lt_card
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EtaleSimplicialCochainSchemeSectionExtensionNatu
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem galois_sqrt_sign {Ω : Type} [Field Ω] [CharZero Ω] (s : G ℚ Ω) {x : Ω} {n : ℤ} (hx : x ^ 2 = n) :
    s x = x ∨ s x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← map_pow, hx, map_intCast]

private theorem decomposition_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {x : Ω} {k : ℤ}
    (hx : x ^ 2 = ((1 + 4 * k : ℤ) : Ω)) (hk : B.valuation (k : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) B) : s x = x := by
  refine (galois_sqrt_sign s hx).resolve_right fun h => ?_
  set y : Ω := (1 + x) / 2 with hy
  have h1 : s y = 1 - y := by rw [hy, map_div₀, map_add (f := _), map_one, h, map_ofNat]; ring
  have h2 : y * (1 - y) = -k := by
    push_cast at hx
    rw [hy]; linear_combination (-1 / 4 : Ω) * hx
  have h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1 := by rw [← h1]; exact valuation_apply_lt_one_iff hs y
  have h4 : B.valuation y < 1 := by
    by_contra h5
    have h6 : 1 ≤ B.valuation (y * (1 - y)) := by
      rw [map_mul]; exact one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))
    rw [h2, Valuation.map_neg] at h6
    exact absurd hk (not_lt.2 h6)
  have h7 := B.valuation.map_add_lt h4 (h3.2 h4)
  have hy' : y + (1 - y) = 1 := by ring
  rw [hy', map_one] at h7
  exact lt_irrefl _ h7

private theorem etaleSimplicialCochain_scheme_section_extension_naturality {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {p n : ℕ} (hp : B.valuation (p : Ω) < 1)
    (h : p.Coprime n) : ¬ B.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz
  have := B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem inertia_fixes_sqrt_discriminant {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {δ : Ω} {D : ℕ}
    (hδ : δ ^ 2 = -(D : Ω)) (hD : ¬ B.valuation ((4 * D : ℕ) : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : s δ = δ := by
  refine (galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_
  have h1 : B.valuation δ ≤ 1 := by
    have : B.valuation δ ^ 2 ≤ 1 := by
      rw [← map_pow, hδ, Valuation.map_neg]; exact (B.valuation_le_one_iff _).2 (natCast_mem B D)
    exact (pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h2 := hs.2 δ h1
  have e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2) := by rw [h]; push_cast; linear_combination (4 : Ω) * hδ
  rw [e, Valuation.map_neg, map_pow]
  exact pow_lt_one₀ zero_le' h2 two_ne_zero

private theorem gauss_sqrt_inertia_negates {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 3)
    (B : ValuationSubring Ω) (hB : B.valuation (p : Ω) < 1) :
    ∃ x : Ω, x ^ 2 = -(p : Ω) ∧ ∃ s ∈ Ine (F := ℚ) B, s x = -x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hm : χ (-1) = -1 := by
    show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1
    rw [quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]; simp
  have hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F := ℚ) B).map (B1.cycN ℚ Ω p) := by
    rw [B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]
    have : ordCompl[p] p = 1 := by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
    have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨s, hs, hs'⟩ := hmem
  refine ⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩
  have h3 := gaussSum_mulShift χ ψ (-1)
  rw [Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg] at h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h3, gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · exact map_intCast s _
  · have h5 : ψ a ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]
    simp

private theorem complex_conjugation_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] {τ : G ℚ Ω} (h : IsCC τ) {z : Ω} {n : ℕ} (hn : 0 < n)
    (hz : z ^ 2 = n) : τ z = z := by
  refine (galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_
  obtain ⟨j, hj⟩ := h
  have h2 : starRingEnd ℂ (j z) = -j z := by rw [← map_neg, ← h1]; exact (hj z).symm
  have h3 := Complex.mul_conj (j z)
  rw [h2, mul_neg, ← sq, ← map_pow, hz, map_natCast] at h3
  have h4 : -(n : ℝ) = Complex.normSq (j z) := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (j z)
  have h6 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem UpperTheory.V.Fr.exists_twistCharacter_continuousCohomology :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ H₀, FrobeniusSplitPrimeDatum η M H₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  have hM := hG.M_ne
  obtain ⟨p, hlt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega)
    isCoprime_one_left.neg_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hmod.dvd
  have ht' : -(p : ℤ) = 1 + 4 * (M * t) := by push_cast at ht; linear_combination ht
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 p hp
  obtain ⟨x, hx, s, hs, hsx⟩ := gauss_sqrt_inertia_negates p (by omega) A hA
  have hsδ : s δ = δ := inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs
  have hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω) := by rw [mul_pow, hδ, hx]; push_cast; ring
  have hpos : 0 < D * p := Nat.mul_pos hD hp.pos
  have hz0 : δ * x ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hz
    exact hpos.ne (by exact_mod_cast hz)
  have hne : -(δ * x) ≠ δ * x := fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)
  have hsz : s (δ * x) = -(δ * x) := by rw [map_mul, hsδ, hsx, mul_neg]
  have hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x := fun g => Iff.rfl
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  refine ⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz,
    fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz.symm.trans (h hs))⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩
    rw [hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]
    rcases galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h
    · rw [h]; exact Or.inr ⟨rfl, hne⟩
    · rw [h, neg_neg]; exact Or.inl ⟨rfl, hne⟩
  · have hk : B'.valuation ((M * t : ℤ) : Ω) < 1 := by
      rw [Int.cast_mul, Int.cast_natCast, map_mul]
      exact mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))
    ext g
    refine and_congr_right fun hg => ?_
    have hgx : g x = x := decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg
    show g (δ * x) = δ * x ↔ η g = 1
    rw [map_mul, hgx, hη]
    rcases Int.units_eq_one_or (η g) with h | h
    · simp [h]
    · rw [h]
      refine iff_of_false (fun h' => hne ?_) (by decide)
      simpa using h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsPlaceRat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_place_rat {w : ℕ} (hw : w.Prime) :
    ∃ v₀ : HeightOneSpectrum (𝓞 ℚ), ∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀ := by
  have hne : ((w : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hw.ne_zero
  have hprime : Prime ((w : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.mp hw
  have hP : (Ideal.span {((w : ℕ) : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hprime
  have hbot : Ideal.span {((w : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hne
  have hmax := hP.isMaximal hbot
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((w : ℕ) : 𝓞 ℚ)}, hP, hbot⟩
  refine ⟨v₀, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HeightOneSpectrum.ext_iff]
    symm
    exact hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  · rw [hv]
    exact Ideal.subset_span (Set.mem_singleton _)

private theorem finite_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(n : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Fr.st_set :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l w N : ℕ), l.Prime → w.Prime → N ≠ 0 → ∀ (C : Type) [Group C] (κ : G ℚ Ω →* C), (∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker) → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v₀ : HeightOneSpectrum (𝓞 ℚ)), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀) ∧ ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), IsPlaceOver A v → (v ∈ S ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨ ¬ Ine (F := ℚ) A ≤ κ.ker) := by
  intro Ω _ _ _ l w N hl hw hN C _ κ hκ
  classical
  obtain ⟨v₀, hv₀⟩ := exists_place_rat hw
  have hT := finite_above (n := l * w * N) (mul_ne_zero (mul_ne_zero hl.ne_zero hw.ne_zero) hN)
  have key : ∀ (A A' : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      IsPlaceOver A' v → Ine (F := ℚ) A ≤ κ.ker → Ine (F := ℚ) A' ≤ κ.ker := by
    intro A A' v hA hA' hle τ hτ
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hA'
    have h1 := hle (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hτ)
    have h2 := κ.normal_ker.conj_mem _ h1 σ
    simpa [mul_assoc] using h2
  have hN' : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      ¬ Ine (F := ℚ) A ≤ κ.ker → ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hA hne
    have h1 : A.valuation (N : Ω) < 1 := by
      by_contra h
      exact hne (hκ A h)
    rw [← hA (N : 𝓞 ℚ)]
    have e : algebraMap ℚ Ω (((N : 𝓞 ℚ) : ℚ)) = (N : Ω) := by simp
    rw [e]
    exact h1
  refine ⟨hT.toFinset.filter (fun v => ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨
    ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ¬ Ine (F := ℚ) A ≤ κ.ker), v₀, hv₀, ?_⟩
  intro v A hA
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h | h | ⟨A', hA', hne⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (fun hle => hne (key A A' v hA hA' hle)))
  · intro h
    refine ⟨?_, ?_⟩
    · have hmem : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨
          ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((hv₀ v).mpr h))
        · exact Or.inr (Or.inr (hN' A v hA h))
      push_cast
      rcases hmem with h | h | h
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h)
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h)
      · exact v.asIdeal.mul_mem_left _ h
    · rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨A, hA, h⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScDisc
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_disc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → (∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ galOf ℚ K Ω) → ¬ (l : ℤ) ∣ discr K := by
  intro Ω _ _ _ l _ K _ _ _ h2 hB
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := {}
  have hl : l.Prime := Fact.out
  rw [← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]
  intro w hw
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w
  have hv : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    simpa only [map_natCast] using h
  have hI := hB A hv
  rw [← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := hI hσ
  ext x
  apply (algebraMap K Ω).injective
  show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x
  rw [AlgEquiv.restrictNormal_commutes]
  exact hσ' x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

theorem UpperTheory.V.Fr.sc_norm :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : c.O), ‖(x : PadicAlgCl l)‖ ≤ 1 ∧ (x ∈ maximalIdeal c.O ↔ ‖(x : PadicAlgCl l)‖ < 1) := by
  intro l _ c x
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hle : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hu : ∀ u : c.Oˣ, ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : c.Oˣ)
    have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have h' : ((l : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : c.O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => ?_
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h] at hl
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, h1, one_pow, mul_one] at hl
    exact absurd hl.symm (inv_lt_one_of_one_lt₀ hl1).ne
  refine ⟨hle x, fun hx => ?_, fun hx => ?_⟩
  · rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hϖ1 (hle y)
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    exact absurd (hu u) hx.ne
end

