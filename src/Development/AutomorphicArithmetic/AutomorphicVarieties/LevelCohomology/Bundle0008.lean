module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoResAway
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.resAway :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [AddCommGroup V] [Module C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), (∀ g h, c (g * h) = c g + ρ g (c h)) → (∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := ℚ) A, c s = ρ s x - x) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := K) A, c (s.restrictScalars ℚ) = ρ (s.restrictScalars ℚ) x - x := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ ρ c hc hyp w hw
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  obtain ⟨B, hB⟩ := exists_isPlaceOver (F := K) Ω w
  have hne : w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)
  let p : HeightOneSpectrum (𝓞 ℚ) := ⟨w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)), Ideal.comap_isPrime _ _, hne⟩
  have hBp : IsPlaceOver B p := by
    intro y
    have key := hB (algebraMap (𝓞 ℚ) (𝓞 K) y)
    have hcoe : ((algebraMap (𝓞 ℚ) (𝓞 K) y : 𝓞 K) : K) = algebraMap ℚ K (y : ℚ) := rfl
    rw [hcoe, ← IsScalarTower.algebraMap_apply] at key
    exact key
  have hlp : ((l : ℕ) : 𝓞 ℚ) ∉ p.asIdeal := by
    show _ ∉ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨A, hA, x, hx⟩ := hyp p hlp
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hBp
  refine ⟨B, hB, ρ σ x - c σ, ?_⟩
  intro s hs
  have ht : s.restrictScalars ℚ ∈ Ine (F := ℚ) B := ⟨hs.1, fun y hy => hs.2 y hy⟩
  rw [← hσ] at ht
  have hu := hx _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' ht)
  have htu : s.restrictScalars ℚ * σ = σ * (σ⁻¹ * s.restrictScalars ℚ * σ) := by group
  have e1 := hc (s.restrictScalars ℚ) σ
  have e2 := hc σ (σ⁻¹ * s.restrictScalars ℚ * σ)
  rw [htu] at e1
  have hct := eq_sub_of_add_eq (e1.symm.trans e2)
  have hm : ρ σ (ρ (σ⁻¹ * s.restrictScalars ℚ * σ) x) = ρ (s.restrictScalars ℚ) (ρ σ x) := by
    rw [← Module.End.mul_apply, ← map_mul, ← htu, map_mul, Module.End.mul_apply]
  rw [hct, hu, map_sub, hm, map_sub]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoTwCont
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have : (fun x => ((f x)⁻¹ : Rˣ).val) = (fun s => (f s : R)) ∘ (fun x => x⁻¹) := by
    funext x
    simp [map_inv]
  rw [this]
  exact h.comp continuous_inv

private theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  apply continuous_of_continuousAt_one
  have hev : (fun _ : Γ => (1 : H)) =ᶠ[nhds 1] f :=
    Filter.eventually_of_mem (hU.mem_nhds h1) fun s hs => (h s hs).symm
  exact (continuousAt_const (y := (1 : H))).congr hev

private theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  classical
  have hS : {ζ : Ω | ζ ^ M = 1} = ((Polynomial.nthRoots M (1 : Ω)).toFinset : Set Ω) := by
    ext ζ
    simp [Polynomial.mem_nthRoots (by omega : 0 < M)]
  haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := by
    rw [hS]
    infer_instance
  let E := IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ M = 1}
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine cont_of_ker φ (E.fixingSubgroup : Set (G ℚ Ω)) E.fixingSubgroup_isOpen E.fixingSubgroup.one_mem ?_
  intro s hs
  apply hφ
  intro ζ hζ
  exact (IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ (IntermediateField.subset_adjoin ℚ _ hζ)

theorem UpperTheory.V.X.Kato.twCont :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (W : G ℚ Ω →* GL (Fin n) (Qbar l)), Continuous W → ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ → ∀ j : ℤ, Continuous (tw W (cycBar ℚ Ω l ^ j * φ)) := by
  intro l _ Ω _ _ _ n W hW M hM φ hφ j
  have hc1 : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)
  have hc2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
  have hcyc : Continuous (cycBar ℚ Ω l) := by
    apply cont_units
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc2.comp hc1)
  have hχ : Continuous (cycBar ℚ Ω l ^ j * φ) := by
    have e : ⇑(cycBar ℚ Ω l ^ j * φ) = fun s => (cycBar ℚ Ω l s) ^ j * φ s := by
      funext s
      simp
    rw [e]
    exact (hcyc.zpow j).mul (cont_kills M hM φ hφ)
  apply cont_units
  have e2 : (fun s => (((tw W (cycBar ℚ Ω l ^ j * φ)) s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) =
      fun s => ((cycBar ℚ Ω l ^ j * φ) s : Qbar l) • (W s : Matrix (Fin n) (Fin n) (Qbar l)) :=
    funext (tw_val W _)
  rw [e2]
  exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hW)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_linearMap_zmod_eq_card (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N]
    [Finite N] : Nat.card (N →ₗ[ZMod n] ZMod n) = Nat.card N := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hfinD : Finite (N →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : N →ₗ[ZMod n] ZMod n => (f : N → ZMod n)) DFunLike.coe_injective
  have hcard : Nat.card (AddChar N ℂ) = Nat.card N := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  apply le_antisymm
  · have hinj : Function.Injective
        (fun f : N →ₗ[ZMod n] ZMod n => ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom) := by
      intro f g h
      have := AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar h
      ext x
      exact DFunLike.congr_fun this x
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ hinj
  · let φ : AddChar N ℂ → N → AddChar (ZMod n) ℂ := fun ψ x =>
      ψ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod n) N x).toAddMonoidHom
    have hφ : ∀ ψ x y, φ ψ (x + y) = φ ψ x + φ ψ y := by
      intro ψ x y
      ext k
      simp [φ, smul_add, AddChar.map_add_eq_mul]
    let g : AddChar N ℂ → (N →ₗ[ZMod n] ZMod n) := fun ψ =>
      AddMonoidHom.toZModLinearMap n (AddMonoidHom.mk' (fun x => AddChar.zmodAddEquiv.symm (φ ψ x))
        (fun x y => by rw [hφ, map_add (f := _)]))
    have hg : Function.Injective g := by
      intro ψ ψ' h
      ext x
      have h1 : φ ψ x = φ ψ' x := by
        have := LinearMap.congr_fun h x
        simpa [g] using this
      have := DFunLike.congr_fun h1 1
      simpa [φ] using this
    rw [← hcard]
    exact Nat.card_le_card_of_injective g hg

theorem UpperTheory.V.X.So.locCard :
    LocalFiniteness → LocalTateDuality → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) (Dec (F := k) A) M), ContAction ρ → ∀ (τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M)), (∀ g φ m, τ g φ m = (cycMod k Ω l r g : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H2 ρ) = Nat.card (H0 τ) := by
  intro hfin hdual k Ω _ _ _ _ _ l _ r hr v A hA M _ _ _ _ _ ρ hcont τ hτ
  obtain ⟨-, h1, h2, -⟩ := hfin k Ω l r M A ρ v hr hA hcont
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hdual k Ω l r M A ρ v hr hA hcont
  refine ⟨h1, h2, ?_⟩
  have hτ' : τ = twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ := by
    ext g φ
    apply DFunLike.ext
    intro m
    rw [hτ]
    rfl
  subst hτ'
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfinD : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ r)) M => (f : M → ZMod (l ^ r))) DFunLike.coe_injective
  have hA1 := Nat.card_congr (Equiv.ofBijective _ hb)
  have hA2 := Nat.card_congr (LinearEquiv.congrRight (M := ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))) e).toEquiv
  have hA3 := card_linearMap_zmod_eq_card (l ^ r) ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))
  exact hA1.trans (hA2.trans hA3)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem arith (l n : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hn : 0 < n) (hnd : ¬ l ∣ n) :
    0 < orderOf (l : ZMod (Nat.lcm 4 n)) ∧ Nat.lcm 4 n ∣ l ^ orderOf (l : ZMod (Nat.lcm 4 n)) - 1 := by
  have hm0 : Nat.lcm 4 n ≠ 0 := Nat.lcm_ne_zero (by norm_num) hn.ne'
  haveI : NeZero (Nat.lcm 4 n) := ⟨hm0⟩
  have h2 : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have h4 : Nat.Coprime l 4 := by
    have e := Nat.Coprime.pow_right 2 h2
    norm_num at e
    exact e
  have hn' : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hnd
  have hc : Nat.Coprime l (Nat.lcm 4 n) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul 4 n) (Nat.Coprime.mul_right h4 hn')
  have hue : ((ZMod.unitOfCoprime l hc : (ZMod (Nat.lcm 4 n))ˣ) : ZMod (Nat.lcm 4 n)) = (l : ZMod (Nat.lcm 4 n)) :=
    ZMod.coe_unitOfCoprime l hc
  have hord : orderOf (l : ZMod (Nat.lcm 4 n)) = orderOf (ZMod.unitOfCoprime l hc) := by
    rw [← hue, orderOf_units]
  refine ⟨by rw [hord]; exact orderOf_pos _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow,
    pow_orderOf_eq_one, Nat.cast_one, sub_self]

theorem UpperTheory.V.X.th1Facts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) (l : ℕ), l.Prime → l ≠ 2 → ψ = psi2 ψ * th1 l ψ * kap l ψ ∧ (∃ s, kap l ψ ^ l ^ s = 1) ∧ Odd (th1 l ψ ^ 2).conductor ∧ 0 < f0 l ψ ∧ 4 ∣ l ^ f0 l ψ - 1 ∧ th1 l ψ ^ (l ^ f0 l ψ - 1) = 1 ∧ l - 1 ∣ l ^ f0 l ψ - 1 := by
  intro O _ _ N _ ψ l hl hl2
  obtain ⟨-, hmul, hone, hinv, hpow, hidem, -, -⟩ := compAlg O N 2 Nat.prime_two
  have hfin : 0 < orderOf ψ := orderOf_pos ψ
  obtain ⟨hoK, -, hndvd, -, -, -, -⟩ := partOrd _ l hl ψ hfin
  have hkapOrd : orderOf (kap l ψ) = l ^ (orderOf ψ).factorization l := hoK
  have hc2k : comp 2 (kap l ψ) = 1 := by
    obtain ⟨k, hk⟩ := (compOrd O N (kap l ψ) 2 Nat.prime_two).2.1
    have hd : orderOf (comp 2 (kap l ψ)) ∣ orderOf (kap l ψ) := (hidem (kap l ψ)).2.1
    rw [hk, hkapOrd] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ l ^ (orderOf ψ).factorization l := dvd_trans (dvd_pow_self 2 hk0) hd
      have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      exact hl2 e.symm
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hψ : th0 l ψ * kap l ψ = ψ := dirichletPrimeToLPart_mul_lPowerPart l ψ
  have hc2 : comp 2 ψ = comp 2 (th0 l ψ) := by
    conv_lhs => rw [← hψ]
    rw [hmul, hc2k, mul_one]
  have hth1c : comp 2 (th1 l ψ) = 1 := by
    show comp 2 (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) = 1
    rw [hmul, hinv, (hidem _).1, mul_inv_cancel]
  have hth1pow : th1 l ψ ^ orderOf (th0 l ψ) = 1 := by
    show (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) ^ orderOf (th0 l ψ) = 1
    rw [mul_pow, inv_pow, ← hpow, pow_orderOf_eq_one, hone, inv_one, mul_one]
  have hdvd1 : orderOf (th1 l ψ) ∣ orderOf (th0 l ψ) := orderOf_dvd_of_pow_eq_one hth1pow
  have hnd1 : ¬ l ∣ orderOf (th1 l ψ) := fun h => hndvd (dvd_trans h hdvd1)
  have hpos1 : 0 < orderOf (th1 l ψ) := orderOf_pos _
  obtain ⟨hf0, hdiv⟩ := arith l (orderOf (th1 l ψ)) hl hl2 hpos1 hnd1
  have hf : f0 l ψ = orderOf ((l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ))))) := rfl
  refine ⟨?_, ⟨(orderOf ψ).factorization l, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ψ = comp 2 ψ * (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) * kap l ψ
    rw [hc2, mul_comm (comp 2 (th0 l ψ)) (th0 l ψ * _), inv_mul_cancel_right]
    exact hψ.symm
  · rw [← hkapOrd]
    exact pow_orderOf_eq_one _
  · have h1 : comp 2 (th1 l ψ ^ 2) = 1 := by
      rw [hpow, hth1c, one_pow]
    have h := ((compCond O N (th1 l ψ ^ 2) 2 Nat.prime_two).2.1).mp h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · rw [hf]
    exact hf0
  · rw [hf]
    exact dvd_trans (Nat.dvd_lcm_left 4 _) hdiv
  · rw [hf]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right 4 _) hdiv)
  · have e := Nat.sub_dvd_pow_sub_pow l 1 (f0 l ψ)
    rwa [one_pow] at e
end

