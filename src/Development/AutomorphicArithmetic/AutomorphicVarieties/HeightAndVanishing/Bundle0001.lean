module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Mathlib.RingTheory.Unramified.LocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CardLeLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem card_le_level (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N]
    (T : Finset (DirichletCharacter O N)) : T.card ≤ N := by
  classical
  have hli := linearIndependent_monoidHom (ZMod N) O
  let g : T → (ZMod N →* O) := fun χ => (χ.1 : MulChar (ZMod N) O).toMonoidHom
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply MulChar.ext'
    intro y
    have := DFunLike.congr_fun h y
    simpa [g] using this
  have hT := (hli.comp g hg).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_coe] at hT
  exact hT

theorem UpperTheory.V.HV.xCard :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N], (∀ T : Finset (DirichletCharacter O N), T.card ≤ N) ∧
      ∀ (M : ℕ), 0 < M → ∀ T : Finset (DirichletCharacter O N), (∀ ψ ∈ T, ψ.conductor ∣ M) → T.card ≤ M := by
  intro O _ _ N _
  refine ⟨card_le_level O N, ?_⟩
  intro M hM T hT
  classical
  set g := Nat.gcd M N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right M N
  have hgM : g ≤ M := Nat.le_of_dvd hM (Nat.gcd_dvd_left M N)
  haveI : NeZero g := ⟨(Nat.gcd_pos_of_pos_left N hM).ne'⟩
  have hex : ∀ ψ ∈ T, ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ := by
    intro ψ hψ
    obtain ⟨hc, χ₀, hχ₀⟩ := ψ.factorsThrough_conductor
    have hcg : ψ.conductor ∣ g := Nat.dvd_gcd (hT ψ hψ) hc
    refine ⟨DirichletCharacter.changeLevel hcg χ₀, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ₀
  let f : DirichletCharacter O N → DirichletCharacter O g := fun ψ =>
    if h : ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ then h.choose else 1
  have hf : ∀ ψ ∈ T, ψ = DirichletCharacter.changeLevel hgN (f ψ) := by
    intro ψ hψ
    have h := hex ψ hψ
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    rw [hf a ha, hf b hb, hab]
  calc T.card = (T.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ g := card_le_level O g _
    _ ≤ M := hgM
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem exists_coef_ge (l : ℕ) [Fact l.Prime] (A : Subalgebra ℤ_[l] (PadicAlgCl l)) [hA : Module.Finite ℤ_[l] A] :
    ∃ c : Coef l, A ≤ c.O := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule A).FG := Module.Finite.iff_fg.1 hA
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  change Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule ((integralClosure ℤ_[l] K).map f)
  rw [← hs, Submodule.span_le]
  intro x hx
  have hxA : x ∈ A := by
    change x ∈ Subalgebra.toSubmodule A
    rw [← hs]
    exact Submodule.subset_span hx
  have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hxA⟩ : A)).map A.val
  exact ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩

private theorem unram_adjoin {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    {ζ : S} (hζ : ζ ^ n = 1) : Algebra.FormallyUnramified R (Algebra.adjoin R {ζ}) := by
  let z : Algebra.adjoin R {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton R ζ⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  let D := KaehlerDifferential.D R (Algebra.adjoin R {ζ})
  have hDz : D z = 0 := by
    have h := D.leibniz_pow z n
    rw [hz, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R] at h
    exact ((IsUnit.of_pow_eq_one hz hn0).pow _).smul_eq_zero.1 (hn.smul_eq_zero.1 h.symm)
  have hD : ∀ x (hx : x ∈ Algebra.adjoin R {ζ}), D ⟨x, hx⟩ = 0 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hDz
    | algebraMap r => exact D.map_algebraMap r
    | add x y hx hy h1 h2 =>
      have := D.map_add ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, add_zero] at this
      exact this
    | mul x y hx hy h1 h2 =>
      have := D.leibniz ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := KaehlerDifferential.span_range_derivation R (Algebra.adjoin R {ζ})
  have h0 : (⊤ : Submodule (Algebra.adjoin R {ζ}) Ω[Algebra.adjoin R {ζ}⁄R]) ≤ ⊥ := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD x.1 x.2
  rw [(Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := a))), (Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := b)))]

private theorem eO_eq_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hm : Ideal.span {(l : O)} = IsLocalRing.maximalIdeal O) : eO l O = 1 := by
  unfold eO
  rw [hm, Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩

private theorem exists_unram (l : ℕ) [hl : Fact l.Prime] (n : ℕ) [NeZero n] (hn : ¬ l ∣ n) :
    ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have hu : IsUnit (n : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
  let A : Subalgebra ℤ_[l] (PadicAlgCl l) := Algebra.adjoin ℤ_[l] {ζ}
  haveI hfin : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.2 hζi.fg_adjoin_singleton
  haveI : Algebra.FormallyUnramified ℤ_[l] A := unram_adjoin (NeZero.ne n) hu hζ.pow_eq_one
  obtain ⟨c, hc⟩ := exists_coef_ge l A
  let f : A →ₐ[ℤ_[l]] c.O := Subalgebra.inclusion hc
  have hf : Function.Injective f := Subalgebra.inclusion_injective hc
  haveI hloc : IsLocalRing A := by
    letI : Algebra A c.O := f.toAlgebra
    haveI : IsScalarTower ℤ_[l] A c.O := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    haveI : Algebra.IsIntegral A c.O := Algebra.IsIntegral.tower_top ℤ_[l]
    haveI : FaithfulSMul A c.O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
    haveI : IsLocalHom (algebraMap A c.O) := inferInstance
    exact (algebraMap A c.O).domain_isLocalRing
  have hinj : Function.Injective (algebraMap ℤ_[l] A) := by
    intro a b hab
    have h := congrArg (fun x : A => (x : PadicAlgCl l)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)
  haveI : FaithfulSMul ℤ_[l] A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsLocalHom (algebraMap ℤ_[l] A) := inferInstance
  have hm : Ideal.span {(l : A)} = IsLocalRing.maximalIdeal A := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ℤ_[l]), PadicInt.maximalIdeal_eq_span_p,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have hnf : ¬ IsField A := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := hm ▸ inferInstance
  have hd : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hp
  refine ⟨⟨A, hd, hfin⟩, ?_, ?_⟩
  · exact eO_eq_one l A hm
  · refine ⟨⟨⟨ζ, Algebra.self_mem_adjoin_singleton _ ζ⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective

theorem UpperTheory.V.HV.coefSup :
    ∀ (l : ℕ) [Fact l.Prime], (∀ c c' : Coef l, ∃ c'' : Coef l, c.O ≤ c''.O ∧ c'.O ≤ c''.O) ∧
      (∀ (n : ℕ) [NeZero n], ¬ l ∣ n → ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n) ∧
      (∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O) ∧
      ∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → (∃ a b : c.O, (b : PadicAlgCl l) ≠ 0 ∧ x * b = a) → x ∈ c.O := by
  intro l _
  refine ⟨fun c c' => ?_, fun n _ hn => exists_unram l n hn, fun c x hx => ?_, fun c x hx ⟨a, b, hb, hab⟩ => ?_⟩
  · haveI := Subalgebra.finite_sup c.O c'.O
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ c'.O)
    exact ⟨d, le_sup_left.trans hd, le_sup_right.trans hd⟩
  · haveI : Module.Finite ℤ_[l] (Algebra.adjoin ℤ_[l] {x}) := Module.Finite.iff_fg.2 hx.fg_adjoin_singleton
    haveI := Subalgebra.finite_sup c.O (Algebra.adjoin ℤ_[l] {x})
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ Algebra.adjoin ℤ_[l] {x})
    exact ⟨d, le_sup_left.trans hd, (le_sup_right.trans hd) (Algebra.self_mem_adjoin_singleton _ x)⟩
  · let g : FractionRing c.O →ₐ[c.O] PadicAlgCl l :=
      IsFractionRing.liftAlgHom (g := Algebra.ofId c.O (PadicAlgCl l)) Subtype.val_injective
    have hg : g (algebraMap c.O _ a / algebraMap c.O _ b) = x := by
      rw [map_div₀, g.commutes, g.commutes]
      exact (div_eq_iff hb).2 hab.symm
    have hi : IsIntegral c.O (algebraMap c.O (FractionRing c.O) a / algebraMap c.O _ b) := by
      rw [← isIntegral_algHom_iff g g.injective, hg]
      exact hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hg, ← hy, g.commutes]
    exact y.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem co_proj_eq_one {N : ℕ} (r : ℕ) (hr : r.Prime) (u : (ZMod N)ˣ)
    (h : ((ordProj[r] N : ℕ) : ZMod N) ∣ (u : ZMod N) - 1) : proj r N u = 1 := by
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < Nat.totient (ordProj[r] N) := by
    rw [Nat.totient_pos]
    exact pow_pos hr.pos _
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h0 : idem r N * ((ordProj[r] N : ℕ) : ZMod N) = 0 := by
    unfold idem
    rw [hk, ← Nat.cast_mul, pow_succ, mul_assoc, mul_comm (ordCompl[r] N),
      Nat.ordProj_mul_ordCompl_eq_self, Nat.cast_mul, ZMod.natCast_self, mul_zero]
  ext
  change idem r N * (u : ZMod N) + (1 - idem r N) = 1
  linear_combination idem r N * ht + t * h0

private theorem co_dvd_of_unitsMap {N d : ℕ} [NeZero N] (hd : d ∣ N) (u : (ZMod N)ˣ)
    (h : ZMod.unitsMap hd u = 1) : ((d : ℕ) : ZMod N) ∣ (u : ZMod N) - 1 := by
  rw [Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
  obtain ⟨t, ht⟩ := h.symm.dvd
  refine ⟨(t : ZMod N), ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod N) ht
  simpa using this

private theorem co_toUnitHom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  simp [comp]

private theorem co_pow_toUnitHom {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (u : (ZMod N)ˣ) :
    (χ ^ k).toUnitHom u = χ.toUnitHom u ^ k := by
  ext
  simp [MulChar.pow_apply_coe]

private theorem co_pow_eq_one_iff {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) :
    χ ^ k = 1 ↔ ∀ u, χ.toUnitHom u ^ k = 1 := by
  simp_rw [← co_pow_toUnitHom]
  constructor
  · intro h u
    rw [h]
    ext
    simp
  · intro h
    ext u
    simpa using congrArg Units.val (h u)

private theorem co_ord_dvd {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) : orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) := by
  rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
  intro u
  have : NeZero (ordProj[r] N) := ⟨(pow_pos hr.pos _).ne'⟩
  rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
  apply co_dvd_of_unitsMap (Nat.ordProj_dvd N r)
  rw [map_pow, ZMod.pow_totient]

private theorem co_tame {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) (h : ¬ r ∣ orderOf (comp r χ)) :
    orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r := by
  have hc : (orderOf (comp r χ)).Coprime r := ((Nat.Prime.coprime_iff_not_dvd hr).2 h).symm
  have h1 := co_ord_dvd χ r hr
  by_cases hN : r ∣ N
  · have hpos : 0 < N.factorization r := hr.factorization_pos_of_dvd (NeZero.ne N) hN
    rw [Nat.totient_prime_pow hr hpos] at h1
    refine ⟨(hc.pow_right _).dvd_of_dvd_mul_left h1, ?_⟩
    apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.factorsThrough_iff_ker_unitsMap hN]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h2 := dvd_sub_pow_of_dvd_sub (co_dvd_of_unitsMap hN u hu) (N.factorization r)
    have h3 : (comp r χ).toUnitHom u ^ (r ^ N.factorization r) = 1 := by
      rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
      rw [one_pow] at h2
      refine dvd_trans ?_ (by simpa using h2)
      rw [Nat.cast_pow]
      exact pow_dvd_pow _ (Nat.le_succ _)
    have h4 := (co_pow_eq_one_iff (comp r χ) _).1 (pow_orderOf_eq_one _) u
    have h5 := pow_gcd_eq_one.2 ⟨h4, h3⟩
    rwa [hc.pow_right _, pow_one] at h5
  · rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.totient_one, Nat.dvd_one] at h1
    refine ⟨by rw [h1]; exact one_dvd _, ?_⟩
    rw [orderOf_eq_one_iff] at h1
    rw [h1, DirichletCharacter.conductor_one]
    exact one_dvd _

theorem UpperTheory.V.HV.compOrd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) ∧ (∃ k, orderOf (comp 2 χ) = 2 ^ k) ∧
      (¬ r ∣ orderOf (comp r χ) → orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r) ∧
      ∀ l s : ℕ, l.Prime → l ≠ r → χ ^ l ^ s = 1 → comp r χ ≠ 1 → r ≡ 1 [MOD l] ∧ (comp r χ).conductor = r := by
  intro O _ _ N _ χ r hr
  refine ⟨co_ord_dvd χ r hr, ?_, co_tame χ r hr, ?_⟩
  · have h1 := co_ord_dvd χ 2 Nat.prime_two
    have h2 : Nat.totient (ordProj[2] N) ∣ 2 ^ (N.factorization 2 - 1) := by
      rcases Nat.eq_zero_or_pos (N.factorization 2) with h | h
      · simp [h]
      · rw [Nat.totient_prime_pow Nat.prime_two h]; simp
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h1.trans h2)
    exact ⟨k, hk⟩
  · intro l s hl hlr hχ hne
    have h1 : orderOf (comp r χ) ∣ l ^ s := by
      rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
      intro u
      rw [co_toUnitHom]
      exact (co_pow_eq_one_iff χ _).1 hχ _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).1 h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hk))
    have h2 : ¬ r ∣ orderOf (comp r χ) := by
      rw [hk]
      intro h
      exact hlr ((Nat.prime_dvd_prime_iff_eq hr hl).1 (hr.dvd_of_dvd_pow h)).symm
    obtain ⟨h3, h4⟩ := co_tame χ r hr h2
    refine ⟨?_, ?_⟩
    · rw [hk] at h3
      exact ((Nat.modEq_iff_dvd' hr.one_le).2 ((dvd_pow_self l hk0).trans h3)).symm
    · rcases (Nat.dvd_prime hr).1 h4 with h | h
      · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hne
      · exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.countZ :
    PropZ → CountZ := by
  intro hZ χ
  refine ⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩
  obtain ⟨hnB, hdiv, rfl⟩ := hc
  have h5 : 5 ≤ l := by
    have h3 : l ≠ 3 := fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)
    have h4 : l ≠ 4 := fun h4 => absurd (h4 ▸ hl.out) (by norm_num)
    have := hl.out.two_le
    omega
  have hev : Even e := by
    have h1 := (h.mem_X.1 hψ).2
    unfold PsiEven at h1
    rw [MulChar.one_apply (isUnit_one.neg)] at h1
    by_contra hne
    rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at h1
    have h2 : (2 : c.O) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have h2e : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  have h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    unfold Vlen
    rw [hd]
    exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le
  refine ⟨by rw [h0]; simp, ?_⟩
  simp [Vn, h0, Chr.nrm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)

def Congr (a b : G ℚ Ω →* c.Oˣ) : Prop := ∀ σ, ((a σ : c.Oˣ) : c.O) - ((b σ : c.Oˣ) : c.O) ∈ IsLocalRing.maximalIdeal c.O

def IsOmT (w : G ℚ Ω →* c.Oˣ) : Prop :=
  w ^ (l - 1) = 1 ∧ Congr c w (UpperTheory.V.Base.chiO (k := ℚ) (Ω := Ω) l c.O)

structure GDlit (K : Type) [Field K] [NumberField K] [Algebra K Ω] (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (w η : G ℚ Ω →* c.Oˣ) (a : ℕ) : Prop where
  om : IsOmT c w
  eta_ker : η.ker = galOf ℚ K Ω
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ σ = w σ ^ a
  a_lt : a < l - 1
  two_a : l - 1 ∣ 2 * a
  par : ∀ σ : G ℚ Ω, IsCC σ → UpperTheory.V.Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ∀ i j : ℕ, ¬ Congr c η (w ^ i * (Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹) ^ j)
  gen : ¬ l - 1 ∣ 2 * (e + a)

end UpperTheory.V.HV

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem coe_unitsMap {g N : ℕ} [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g) = (((u : ZMod N).val : ℕ) : ZMod g) := by
  show ZMod.castHom h (ZMod g) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem pm_iff {n : ℕ} (v : (ZMod n)ˣ) (a : ℕ) (hv : (v : ZMod n) = (a : ZMod n)) :
    (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) := by
  have key : v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ v = 1 ∨ v = -1 := by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with he | ho
      · left
        exact he.neg_one_zpow
      · right
        exact ho.neg_one_zpow
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  rw [key, ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← hv]
  simp only [Units.ext_iff, Units.val_one, Units.val_neg, eq_neg_iff_add_eq_zero]

private theorem jac_iff {p : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (a : ℕ) (hv : (v : ZMod p) = (a : ZMod p)) :
    jacobiSym (a : ℤ) p = 1 ↔ v ∈ (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  haveI := Fact.mk hp
  have ha : ((a : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [← hv]
    exact v.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p ha]
  push_cast
  rw [← hv]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hw]
    simp [sq]

theorem UpperTheory.V.HV.hostLevel :
    ∀ (h : Host) (E : Type) [Field E] [NumberField E], IsChiField h.chi h.ex h.q1 h.d E → Chr.HasLevel E h.N h.H := by
  intro h E _ _ hchi
  have hc := (isCompField_ofChar h.chi h.ex h.q1 h.d E).mpr hchi
  obtain ⟨H', hlev, hmem⟩ := Chr.abLevel.2 (AbF.ofChar h.chi) h.ex h.q1 h.d E hc h.N h.two_pow_dvd h.q_dvd h.host_q1_dvd_N h.d_dvd
  have hq1 : h.q1.Prime := h.pair.1
  have hd : h.d.Prime := h.pair.2.2.1
  convert hlev using 1
  ext u
  have hu : (u : ZMod h.N) = (((u : ZMod h.N).val : ℕ) : ZMod h.N) := (ZMod.natCast_zmod_val _).symm
  rw [hmem u _ hu]
  simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [← pm_iff (ZMod.unitsMap h.two_pow_dvd u) _ (coe_unitsMap _ u),
    ← jac_iff hq1 (ZMod.unitsMap h.host_q1_dvd_N u) _ (coe_unitsMap _ u),
    ← jac_iff hd (ZMod.unitsMap h.d_dvd u) _ (coe_unitsMap _ u)]
  have hk : (ZMod.unitsMap h.q_dvd u) ∈ (MulChar.toUnitHom h.chi.χ).ker ↔
      (AbF.ofChar h.chi).ker ((u : ZMod h.N).val) := by
    constructor
    · intro hv
      exact ⟨_, hv, coe_unitsMap _ u⟩
    · rintro ⟨w, hw, hwa⟩
      have hweq : w = ZMod.unitsMap h.q_dvd u := Units.ext (hwa.trans (coe_unitsMap _ u).symm)
      rwa [← hweq]
  rw [hk]
  tauto
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PZeroLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.pZeroLe :
    ∀ m : ℕ, 0 < m → (pZero m).Prime ∧ 5 ≤ pZero m ∧ ¬ pZero m ∣ m ∧ pZero m ≤ 2 * m + 10 := by
  intro m hm
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 5) (by omega)
  have hmem : p ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} :=
    ⟨hp, by omega, fun h => by have := Nat.le_of_dvd hm h; omega⟩
  have h3 : UpperTheory.V.HV.pZero m ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} := Nat.sInf_mem ⟨p, hmem⟩
  have h4 : UpperTheory.V.HV.pZero m ≤ p := Nat.sInf_le hmem
  exact ⟨h3.1, h3.2.1, h3.2.2, by omega⟩
end

