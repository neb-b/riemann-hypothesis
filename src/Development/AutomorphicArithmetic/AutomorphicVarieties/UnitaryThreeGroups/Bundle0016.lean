module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInjGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFinitePlaceSetFactoringThroughGS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem place_uniq {l : ℕ} (hl : l.Prime) (v w : HeightOneSpectrum (𝓞 ℚ)) (hv : (l : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (l : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (l : 𝓞 ℚ) ∈ u.asIdeal →
      Ideal.span {(l : ℤ)} = u.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    intro u hu
    apply hmax.eq_of_le
    · rw [Ideal.map_comap_of_equiv]
      exact Ideal.comap_ne_top _ u.isPrime.ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hel : e (l : 𝓞 ℚ) = (l : ℤ) := map_natCast e l
      rw [← hel]
      exact Ideal.mem_map_of_mem _ hu
  apply HeightOneSpectrum.ext
  rw [← Ideal.map_of_equiv (I := v.asIdeal) e, ← Ideal.map_of_equiv (I := w.asIdeal) e, ← key v hv, ← key w hw]

theorem UpperTheory.exists_finite_place_set_factoring_through_GS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (η' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* ℤˣ) (Ψ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* c.Oˣ),
            ContainsAbove S l ∧ (∀ v, IsPlaceOver (A v) v.1) ∧ D.ι.range = Dec (F := ℚ) (A v₀) ∧ (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) ∧
            η'.comp (toGS Ω _) = D.η ∧ Ψ'.comp (toGS Ω _) = D.Ψ := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  classical
  have hlp : l.Prime := Fact.out
  haveI : IsScalarTower ℚ K Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hηopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := by
    rw [D.η_ker]
    let b := Module.finBasis ℚ K
    have heq : (galOf ℚ K Ω : Set (G ℚ Ω)) = ⋂ i, {σ : G ℚ Ω | σ (algebraMap K Ω (b i)) = algebraMap K Ω (b i)} := by
      ext σ
      simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_galOf]
      refine ⟨fun h i => h _, fun h x => ?_⟩
      have h' := b.ext (f₁ := σ.toLinearMap ∘ₗ (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap)
        (f₂ := (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap) h
      exact LinearMap.congr_fun h' x
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := ℚ) _ (fun t => t = algebraMap K Ω (b i))
  obtain ⟨⟨T, hT⟩, -⟩ := ramFinite ℚ ℚ K Ω
  have hlN0 : ((l * N : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hlp.ne_zero (NeZero.ne N))
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := T ∪ hfin.toFinset
  have hmemS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have hcast : ∀ n : ℕ, algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := fun n => by simp
  have hlv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv
  have hNv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hv
  obtain ⟨A₀, hA₀l, hA₀dec, -⟩ := dat_loc D
  have hA₀top : A₀ ≠ ⊤ := by
    intro h
    exact ((places ℚ Ω l A₀).2.1 h).2 hA₀l
  obtain ⟨v₀, hv₀⟩ := (places ℚ Ω l A₀).1 hA₀top
  have hlv₀ : ((l : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
    rw [← hv₀, hcast]
    exact hA₀l
  have hv₀S : v₀ ∈ S := hmemS v₀ (hlv v₀ hlv₀)
  let v₀' : S := ⟨v₀, hv₀S⟩
  let A : S → ValuationSubring Ω := fun v =>
    if v.1 = v₀ then A₀ else Classical.choose (exists_isPlaceOver Ω v.1)
  let H : Subgroup (G ℚ Ω) := (cycZ ℚ Ω l).ker ⊓ (Chr.cls ℚ Ω N).ker ⊓ D.η.ker
  have hHclosed : IsClosed (H : Set (G ℚ Ω)) := by
    simp only [H, Subgroup.coe_inf]
    refine (IsClosed.inter ?_ ?_).inter ?_
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (contTw ℚ Ω l).1
    · exact Subgroup.isClosed_of_isOpen _ (Chr.clsFacts ℚ Ω N).1
    · exact Subgroup.isClosed_of_isOpen _ hηopen
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ H := by
    apply Subgroup.topologicalClosure_minimal _ _ hHclosed
    apply Subgroup.normalClosure_le_normal
    simp only [Set.iUnion_subset_iff]
    intro v hv B hB g hg
    have hg' : g ∈ Ine (F := ℚ) B := hg
    have hvS : v ∉ S := hv
    have hvT : v ∉ T := fun h => hvS (Finset.mem_union_left _ h)
    have hlB : ¬ B.valuation (l : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hlv v ((hB _).mp h)))
    have hNB : ¬ B.valuation (N : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hNv v ((hB _).mp h)))
    refine ⟨⟨(places ℚ Ω l B).2.2.2 hlB hg', (Chr.clsFacts ℚ Ω N).2.2.2.2 B hNB hg'⟩, ?_⟩
    show g ∈ D.η.ker
    rw [D.η_ker]
    exact hT v hvT B hB ⟨by rw [galOf_self]; trivial, hg'⟩
  have hηk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.η.ker := hNS.trans inf_le_right
  have hΨk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.Ψ.ker := by
    intro g hg
    have hH := hNS hg
    have h1 : cycZ ℚ Ω l g = 1 := hH.1.1
    have h2 : Chr.cls ℚ Ω N g = 1 := hH.1.2
    rw [MonoidHom.mem_ker]
    simp [Dat.Ψ, Chr.Psi, chiO, Chr.dirG, h1, h2]
  refine ⟨S, A, v₀', QuotientGroup.lift _ D.η hηk, QuotientGroup.lift _ D.Ψ hΨk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hmemS v (hlv v hv)
  · intro v
    by_cases h : v.1 = v₀
    · simp only [A, if_pos h]
      rw [h]
      exact hv₀
    · simp only [A, if_neg h]
      exact Classical.choose_spec (exists_isPlaceOver Ω v.1)
  · simp only [A, v₀', if_pos rfl]
    exact hA₀dec
  · intro v
    constructor
    · intro hv
      exact Subtype.ext (place_uniq hlp _ _ hv hlv₀)
    · rintro rfl
      exact hlv₀
  · ext g
    rfl
  · ext g
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsGaloisCyclotomicNegOneTrivialOnEtaPsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cycMod_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {σ : G ℚ Ω}
    (h : IsConjOm σ.toRingEquiv) : cycMod ℚ Ω l 1 σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hζl : ζ ^ l = 1 := hζ.pow_eq_one
  have hσζ : σ.toRingEquiv ζ = ζ⁻¹ := by
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := l)
      (by rw [← map_pow, hζl, map_one]) hlp.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ (n := 1) (by rw [pow_one]; exact hζl)
  have hval : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val := rfl
  set a : ZMod (l ^ 1) := PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val with ha
  haveI : NeZero (l ^ 1) := ⟨by simp [hlp.ne_zero]⟩
  have hlt : a.val < l := by simpa using ZMod.val_lt a
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    rw [eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', Nat.sub_add_cancel hlp.one_le, hζl]
  have hav : a.val = l - 1 := by
    apply hζ.pow_inj hlt (Nat.sub_lt hlp.pos one_pos)
    rw [← hspec, hσζ, hinv]
  apply Units.ext
  rw [hval, ← ZMod.natCast_zmod_val a, hav, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero]
  have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    simp
  rw [← h0, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hlp.one_le]

theorem UpperTheory.exists_galois_cyclotomic_neg_one_trivial_on_eta_psi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ g : G ℚ Ω, D.η g = 1 ∧ barChar c.O D.Ψ g = 1 ∧ cycMod ℚ Ω l 1 g = -1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  obtain ⟨-, hηcc, hΨcc, -⟩ := dat_facts D
  have hcyc_cc : cycMod ℚ Ω l 1 D.cc = -1 := by
    apply cycMod_cc l
    obtain ⟨φ, hφ⟩ := D.conj
    exact ⟨φ, hφ⟩
  have hgd := D.gd.eta
  rw [← D.η_ker] at hgd
  obtain ⟨h, hmem, hnot⟩ := SetLike.not_le_iff_exists.mp hgd
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.mp hmem
  rw [MonoidHom.mem_ker] at hh1 hh2 hnot
  have hηh : D.η h = -1 := (Int.units_eq_one_or _).resolve_left hnot
  obtain ⟨⟨w, hw, -⟩, hall⟩ := omT Ω l c
  have hwk : w.ker = (cycMod ℚ Ω l 1).ker := (hall w hw).1
  have hwh : w h = 1 := by
    rw [← MonoidHom.mem_ker, hwk, MonoidHom.mem_ker]
    exact hh1
  obtain ⟨b, -, -, hcong⟩ := (psiBar Ω l c w hw N ψ).1
  have hΨh : barChar c.O D.Ψ h = 1 := by
    have hm := hcong e h
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwh, hh2, one_pow, mul_one, Units.val_one] at hm
    apply Units.ext
    show (residue c.O) ((D.Ψ h : (c.O)ˣ) : c.O) = ((1 : (ResidueField c.O)ˣ) : ResidueField c.O)
    rw [Units.val_one, ← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  refine ⟨D.cc * h, ?_, ?_, ?_⟩
  · rw [map_mul, hηcc, hηh]
    rfl
  · rw [map_mul, hΨh, mul_one]
    simp only [barChar, MonoidHom.coe_comp, Function.comp_apply, hΨcc, map_one]
  · rw [map_mul, hcyc_cc, hh1, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_sum_lt' {F ι : Type} [NormedField F] [IsUltrametricDist F] (s : Finset ι) (f : ι → F) {C : ℝ}
    (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C :=
  _root_.UpperTheory.Reformulated.B.Qe17.norm_sum_lt s f hC h

private theorem det_ne_zero' {F : Type} [NormedField F] [IsUltrametricDist F] {m : ℕ} (t : F) (ht : ‖t‖ = 1)
    (E : Matrix (Fin m) (Fin m) F) (hE : ∀ a b, ‖E a b‖ < 1) : (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qi6.det_ne_zero t ht E hE

private theorem conj_of_close {F Γ : Type} [NormedField F] [IsUltrametricDist F] [Group Γ] [Fintype Γ] {m : ℕ}
    (hΓ : ‖(Fintype.card Γ : F)‖ = 1) (ρ ρ₀ : Γ →* GL (Fin m) F)
    (hi : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1)
    (hc : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ < 1) :
    ∃ M : GL (Fin m) F, ∀ g, (M : Matrix (Fin m) (Fin m) F) * ρ g = ρ₀ g * M := by
  have hi₀ : ∀ g a b, ‖(ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1 := fun g a b => by
    have e : (ρ₀ g : Matrix (Fin m) (Fin m) F) a b = (ρ g : Matrix (Fin m) (Fin m) F) a b +
      -((ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hi g a b) (by rw [norm_neg]; exact (hc g a b).le))
  set M : Matrix (Fin m) (Fin m) F := ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g with hM
  have hsplit : M = (Fintype.card Γ : F) • (1 : Matrix (Fin m) (Fin m) F) +
      ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := by
    have e : ∀ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g =
        1 + (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := fun g => by
      rw [Matrix.mul_sub, ← Units.val_mul (ρ₀ g⁻¹) (ρ₀ g), ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      abel
    rw [hM, Finset.sum_congr rfl fun g _ => e g, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  have hdet : M.det ≠ 0 := by
    rw [hsplit]
    refine det_ne_zero' _ hΓ _ fun a b => ?_
    rw [Matrix.sum_apply]
    refine norm_sum_lt' _ _ one_pos fun g _ => ?_
    rw [Matrix.mul_apply]
    refine norm_sum_lt' _ _ one_pos fun k _ => ?_
    rw [norm_mul, Matrix.sub_apply]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hi₀ _ _ _) (norm_nonneg _) (hc g k b)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun h => ?_⟩
  show M * _ = _ * M
  rw [hM, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight]
  rw [← Matrix.mul_assoc, ← Units.val_mul (ρ₀ h), ← map_mul, map_mul ρ, Units.val_mul, ← Matrix.mul_assoc]
  congr 4
  group

theorem UpperTheory.V.U3.pt_inertia_away :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r),
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ M : GL (Fin 3) (PadicAlgCl l), ∀ g ∈ Ine (F := ℚ) A, D.η g = 1 →
        (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat = (r0 D.η D.ΨQ g).mat * M := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ _ r h A hA
  obtain ⟨-, -, -, -, -, hk0, -, -, -, hK, -⟩ := dat_facts D
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ D.η.ker
  let i : H →* D.η.ker := Subgroup.inclusion inf_le_right
  let χ : H →* c.Oˣ := (Chr.dirG ℚ Ω ψ).comp H.subtype
  let ρ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η r h.mult).comp i
  let ρ₀ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η (r0 D.η D.ΨQ) (hasSimilitudeFactor_diagonalRepr _ _)).comp i
  have hkill : ∀ g : H, g ∈ χ.ker → (g : G ℚ Ω) ∈ D.Kill := fun g hg => (hK g).2 ⟨A, hA, g.2.1, g.2.2, hg⟩
  have hρ : χ.ker ≤ ρ.ker := fun g hg => by
    show (r g).left = 1
    rw [h.kill g (hkill g hg)]; rfl
  have hρ₀ : χ.ker ≤ ρ₀.ker := fun g hg => by
    show tor _ (D.ΨQ g) = 1
    have h1 : tor _ (D.Ψ g) = 1 := congrArg SemidirectProduct.left (hk0 g (hkill g hg))
    have h2 : D.Ψ g = 1 := by
      have : (tor _ (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O) 0 0 = 1 := by rw [h1]; simp
      rw [tor_val] at this
      apply Units.ext
      simpa [wt1] using this
    have h3 : D.ΨQ g = 1 := by
      unfold Dat.ΨQ
      rw [MonoidHom.comp_apply, h2, map_one]
    rw [h3, map_one]
  have hfin : Finite χ.range := by
    have : χ.range ≤ ψ.toUnitHom.range := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, rfl⟩
    have h2 : Finite ψ.toUnitHom.range := Finite.of_surjective _ ψ.toUnitHom.rangeRestrict_surjective
    exact Finite.of_injective _ (Subgroup.inclusion_injective this)
  have hfinQ : Finite (H ⧸ χ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).symm.toEquiv
  letI : Fintype (H ⧸ χ.ker) := Fintype.ofFinite _
  have hpow : ∀ x : H ⧸ χ.ker, x ^ orderOf ψ = 1 := fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    apply Units.ext
    show ((ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ : c.Oˣ) : c.O) = 1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  have hnd : ¬ l ∣ Fintype.card (H ⧸ χ.ker) := fun hd => by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    exact D.gd.ord (hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (hpow x)))
  have hnorm : ‖(Fintype.card (H ⧸ χ.ker) : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd)
  obtain ⟨M, hM⟩ := conj_of_close hnorm (QuotientGroup.lift _ ρ hρ) (QuotientGroup.lift _ ρ₀ hρ₀)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.int g a b)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.red g a b)
  exact ⟨M, fun g hg hη => hM (QuotientGroup.mk (⟨g, hg, hη⟩ : H))⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

abbrev UpperTheory.V.U3.CocVal {O : Type} [CommRing O] (a : O) : Type := Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})

private theorem shaInj_loc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    D.ι.range ∈ shaFam ℚ Ω (l * N) ∧ ∃ s', IsUnit ((D.Ψ (D.ι s') : c.O) ^ 2 - 1) := by
  obtain ⟨A, hA, hD, hIn, -⟩ := dat_loc D
  obtain ⟨s, hs, hsu⟩ := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).2
  rw [← hIn] at hs
  obtain ⟨s', -, hs'⟩ := Subgroup.mem_map.1 hs
  refine ⟨?_, s', by rw [hs']; exact hsu⟩
  rw [hD]
  exact Chr.shaFam_mono (dvd_mul_right l N) (Or.inl ⟨A, hA, rfl⟩)

private theorem shaInj_away {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    ∀ g ∈ D.Kill, ∃ D' ∈ shaFam ℚ Ω (l * N), g ∈ D' := by
  rintro g ⟨A', -, hg', -⟩
  exact ⟨_, Or.inr ⟨A', rfl⟩, hg'⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.V.U3.sha_inj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ b : c.O, b ≠ 0 → ∃ a : c.O, a ≠ 0 ∧
      ∃ γ : Submodule.torsionBy c.O (ShaU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (l * N) ⊤) b →+ (G ℚ Ω → CocVal a),
        Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc D.η D.Ψ D.Kill D.ι D.cc g₁ a := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hM b hb
  exact ⟨b, hb, sha_inj_gen (O := c.O) e (l * N) (Chr.dirG ℚ Ω ψ) D.η D.Kill D.ι D.cc g₁ b hb hM
    (dat_facts D).2.2.2.2.2.2.1 (dat_facts D).2.2.2.2.2.1 (shaInj_away D) (shaInj_loc D).1 _
    (shaInj_loc D).2.choose_spec⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ULocEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem phiCond_quot {Γ : Type} [Group Γ] [TopologicalSpace Γ] (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : PhiCond Γ l) : PhiCond (Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc)
  let π : H.comap (QuotientGroup.mk' M) →* H := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective π :=
    MonoidHom.subgroupComap_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
    IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M)))}) (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ⟩) ?_
  intro φ φ' e
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem exists_univ_loc (hP : Loc.LocalPublishedTheorems) (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (η : GQ l →* ℤˣ) (Ψ : GQ l →* Oˣ)
    (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ)) : Nonempty (Univ (GCond.noCondition O η Ψ)) := by
  haveI : IsAdicComplete (maximalIdeal O) O := (dvrFacts l O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] O) := (dvrFacts l O).2.2.1
  haveI : Finite (ResidueField O) := by
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue O), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] O)]
    refine map_nonunit _ _ ?_
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  haveI : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois _ _
  haveI : (Subgroup.normalClosure (∅ : Set (GQ l))).topologicalClosure.Normal :=
    Subgroup.is_normal_topologicalClosure _
  obtain ⟨U⟩ := exists_univ l η Ψ hη hΨ ∅ (fun g hg => hg.elim) _ rfl
    (phiCond_quot l _ fun H hH => Loc.phiCond hP l l H hH)
  refine ⟨{ R := U.R, r := U.r, rep := fun R' _ _ _ => ⟨fun _ => trivial, fun r' _ => ?_⟩ }⟩
  exact (U.rep R').2 r' fun g hg => hg.elim

theorem UpperTheory.V.U3.exists_uLoc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Nonempty (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι))) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨-, -, -, hη, hΨ, -⟩ := dat_facts D
  exact exists_univ_loc hC.loc l c.O _ _ (hη.comp_continuous D.ι_cont) (hΨ.comp_continuous D.ι_cont)
end

