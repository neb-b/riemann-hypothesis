module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityPrimeToResidueChar
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    IsPlaceOver A w → ∀ M : ℕ, (M : 𝓞 F) ∉ w.asIdeal → ∀ s ∈ Ine (F := F) A, ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ w A hA M hM s hs ζ hζ
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simpa using w.asIdeal.zero_mem)
  have hvM : A.valuation (M : Ω) = 1 := by
    have h1 := (hA (M : 𝓞 F)).not.mpr hM
    have h2 : (algebraMap F Ω) ((M : 𝓞 F) : F) = (M : Ω) := by simp
    rw [h2] at h1
    refine le_antisymm ?_ (not_lt.mp h1)
    simpa using A.valuation_le_one (M : A)
  have hvz : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ M = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with h | h | h
    · exact absurd hp (pow_lt_one₀ zero_le' h hM0).ne
    · exact h
    · exact absurd hp (one_lt_pow₀ h hM0).ne'
  have hI : s ∈ Inertia A := hs
  unfold Inertia at hI
  obtain ⟨-, hI⟩ := hI
  have hd : A.valuation (s ζ - ζ) < 1 := hI ζ hvz.le
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hvz
  set η := s ζ / ζ with hηdef
  have hsz : s ζ = η * ζ := (div_mul_cancel₀ _ hζ0).symm
  have hη : η ^ M = 1 := by
    rw [hηdef, div_pow, ← map_pow, hζ, map_one, div_one]
  have hη1 : A.valuation (η - 1) < 1 := by
    have e : s ζ - ζ = (η - 1) * ζ := by rw [hsz]; ring
    rw [e, map_mul, hvz, mul_one] at hd
    exact hd
  have hvη : A.valuation η = 1 := by
    have e : η = 1 + (η - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hη1
  by_contra hne
  have hne' : η ≠ 1 := by
    intro h1
    apply hne
    rw [hsz, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, η ^ i = 0 := by
    have e := mul_geom_sum η M
    rw [hη, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne')
  have hMsum : (M : Ω) = ∑ i ∈ Finset.range M, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  have hlt : A.valuation (M : Ω) < 1 := by
    rw [hMsum]
    refine Valuation.map_sum_lt _ one_ne_zero ?_
    intro i _
    have e := mul_geom_sum η i
    have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
      refine Valuation.map_sum_le _ ?_
      intro j _
      rw [map_pow, hvη, one_pow]
    rw [Valuation.map_sub_swap, ← e, map_mul]
    calc A.valuation (η - 1) * A.valuation (∑ j ∈ Finset.range i, η ^ j)
        ≤ A.valuation (η - 1) * 1 := by gcongr
      _ = A.valuation (η - 1) := mul_one _
      _ < 1 := hη1
  rw [hvM] at hlt
  exact lt_irrefl _ hlt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_zpow_eq_ringEquiv_on_roots_of_unity {K : Type*} [Field K] (M : ℕ) (hM : 1 ≤ M) (σ : K ≃+* K) :
    ∃ m : ℤ, ∀ x : K, x ^ M = 1 → σ x = x ^ m := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((σ.toMulEquiv.restrictRootsOfUnity M).toMonoidHom)
  refine ⟨m, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : M ≠ 0)] at hx
  let g : rootsOfUnity M K := ⟨Units.mk0 x hx0, by rw [mem_rootsOfUnity]; ext; simp [hx]⟩
  have := congrArg (fun y : rootsOfUnity M K => ((y : Kˣ) : K)) (hm g)
  simpa [g] using this

private theorem commutator_fixes_root_of_unity {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) (hM : 1 ≤ M)
    (σ τ : Ω ≃ₐ[F] Ω) (ζ : Ω) (hζ : ζ ^ M = 1) : (σ * τ * σ⁻¹ * τ⁻¹) ζ = ζ := by
  obtain ⟨a, ha⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM σ.toRingEquiv
  obtain ⟨b, hb⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM τ.toRingEquiv
  have ha' : ∀ x : Ω, x ^ M = 1 → σ x = x ^ a := ha
  have hb' : ∀ x : Ω, x ^ M = 1 → τ x = x ^ b := hb
  have hμ : ∀ (ρ : Ω ≃ₐ[F] Ω) (x : Ω), x ^ M = 1 → (ρ x) ^ M = 1 := fun ρ x hx => by
    rw [← map_pow, hx, map_one]
  have hz : (σ⁻¹ (τ⁻¹ ζ)) ^ M = 1 := hμ _ _ (hμ _ _ hζ)
  have key : σ (τ (σ⁻¹ (τ⁻¹ ζ))) = τ (σ (σ⁻¹ (τ⁻¹ ζ))) := by
    rw [ha' _ (hμ τ _ hz), hb' _ hz, hb' _ (hμ σ _ hz), ha' _ hz, ← zpow_mul, ← zpow_mul, mul_comm]
  simp only [AlgEquiv.mul_apply]
  rw [key]
  simp

theorem UpperTheory.irreducible_weilDeligne_tame_level_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M : ℕ), 1 ≤ M →
    ∀ (m : ℕ) (b : WDRep h (Fin m → ℂ)), b.ρ.IsIrreducible →
    (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → b.ρ (ineIncl h s) = 1) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), WD.mk b = WD.lpOfChar h ξ hξ ∧ ∀ σ, b.ρ σ = 1 → ξ σ = 1 := by
  intro F Ω _ _ _ _ _ w A h M hM m b hirr hine
  haveI := hirr
  have hcomm : ∀ σ τ : Weil h, b.ρ σ * b.ρ τ = b.ρ τ * b.ρ σ := by
    intro σ τ
    have hdeg : deg (σ * τ * σ⁻¹ * τ⁻¹) = 0 := by
      simp only [deg_mul, deg_inv]
      ring
    have hc : ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ∈ Ine A := deg_eq_zero_iff.1 hdeg
    have hρc : b.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
      have e : ineIncl h ⟨_, hc⟩ = σ * τ * σ⁻¹ * τ⁻¹ := rfl
      rw [← e]
      apply hine
      intro ζ hζ
      show ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ζ = ζ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using commutator_fixes_root_of_unity M hM (σ : G F Ω) τ ζ hζ
    have hst : σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
    rw [← map_mul, hst, map_mul, hρc, one_mul, map_mul]
  have hnt : Nontrivial (Fin m → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation b.ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  have hscal : ∀ τ : Weil h, ∃ c : ℂ, ∀ v, b.ρ τ v = c • v := by
    intro τ
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.ρ τ)
    refine ⟨c, ?_⟩
    let S : Subrepresentation b.ρ := ⟨Module.End.eigenspace (b.ρ τ) c, fun g v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have := congrArg (fun f => f v) (hcomm τ g)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hvS : v ∈ S.toSubmodule := hv.1
      rw [hS] at hvS
      exact hv.2 ((Submodule.mem_bot ℂ).1 hvS)
    · intro v
      have hvS : v ∈ S.toSubmodule := by
        rw [hS]
        exact Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 hvS
  obtain ⟨v0, hv0⟩ := exists_ne (0 : Fin m → ℂ)
  have hspan : Submodule.span ℂ {v0} = ⊤ := by
    let S : Subrepresentation b.ρ := ⟨Submodule.span ℂ {v0}, fun g v hv => by
      obtain ⟨c, hc⟩ := hscal g
      rw [hc]
      exact Submodule.smul_mem _ _ hv⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      have hvS : v0 ∈ S.toSubmodule := Submodule.subset_span rfl
      rw [hS] at hvS
      exact hv0 ((Submodule.mem_bot ℂ).1 hvS)
    · exact congrArg Subrepresentation.toSubmodule hS
  have hm1 : m = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  subst hm1
  let v1 : Fin 1 → ℂ := fun _ => 1
  have hEnd : ∀ (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ), f v = f v1 0 • v := by
    intro f v
    have hv : v = v 0 • v1 := by
      funext i
      fin_cases i
      simp [v1]
    rw [hv, map_smul]
    funext i
    fin_cases i
    simp [v1, mul_comm]
  have hne : ∀ σ : Weil h, b.ρ σ v1 0 ≠ 0 := by
    intro σ h0
    have hinv : b.ρ σ⁻¹ (b.ρ σ v1) = v1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hEnd (b.ρ σ) v1, h0, zero_smul, map_zero] at hinv
    have := congrFun hinv 0
    simp [v1] at this
  let ξ : Weil h →* ℂˣ :=
    { toFun := fun σ => Units.mk0 _ (hne σ)
      map_one' := by
        ext
        simp [v1]
      map_mul' := by
        intro σ τ
        ext
        simp only [Units.val_mk0, Units.val_mul, map_mul, Module.End.mul_apply]
        rw [hEnd (b.ρ σ) (b.ρ τ v1)]
        simp }
  have hξ1 : ∀ σ, ξ σ = 1 ↔ b.ρ σ = 1 := by
    intro σ
    constructor
    · intro hσ
      have h1 : b.ρ σ v1 0 = 1 := by simpa [ξ] using congrArg Units.val hσ
      apply LinearMap.ext
      intro v
      rw [hEnd, h1, one_smul]
      rfl
    · intro hσ
      ext
      simp [ξ, hσ, v1]
  have hsm : IsSmooth ξ := by
    simpa only [IsSmooth, hξ1] using b.smooth
  have hN : b.N = 0 := by
    obtain ⟨k, hk⟩ := b.nilpotent
    set c := b.N v1 0 with hc
    have hNv : b.N v1 = c • v1 := hEnd b.N v1
    have hp : ∀ n : ℕ, (b.N ^ n) v1 = c ^ n • v1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, pow_succ]
    have hck : c ^ k = 0 := by
      have := congrFun (hp k) 0
      rw [hk] at this
      simpa [v1] using this.symm
    have hc0 : c = 0 := pow_eq_zero_iff'.1 hck |>.1
    apply LinearMap.ext
    intro v
    rw [hEnd, ← hc, hc0, zero_smul]
    rfl
  refine ⟨ξ, hsm, ?_, fun σ hσ => (hξ1 σ).2 hσ⟩
  unfold WD.lpOfChar
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    fin_cases i
    rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, hEnd (b.ρ σ) v]
    simp [WDRep.ofChars, diagEnd, ξ]
  · simp [hN, WDRep.ofChars]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.mem_iSup_automorphicReps_of_invariant_form :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ φ : UA E n → ℂ, IsAutFormU φ → φ ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdef hinv φ hφ
  classical
  haveI : FiniteDimensional ℂ (admitted.X φ) := hφ.kfin
  have hXA : admitted.X φ ≤ autU E n := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact RU_mem_autU _ _ (mem_autU.2 hφ))
  have haut : ∀ v : admitted.X φ, IsAutFormU (v : UA E n → ℂ) := fun v => mem_autU.1 (hXA v.2)
  let Z : Subrepresentation ((RU E n).comp (infU E n).subtype) :=
    ⟨admitted.X φ, fun g v hv => admitted.RU_mem_X φ g hv⟩
  let ρ : Representation ℂ (infU E n) (admitted.X φ) := Z.toRepresentation
  have hρ : ∀ g (v : admitted.X φ), ((ρ g v : admitted.X φ) : UA E n → ℂ) = RU E n g v := fun _ _ => rfl
  let B' : admitted.X φ →ₗ⋆[ℂ] admitted.X φ →ₗ[ℂ] ℂ := (B.comp (admitted.X φ).subtype).compl₂ (admitted.X φ).subtype
  have hx := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (infU E n) (admitted.X φ) ρ B'
    (fun v hv => Subtype.ext (hdef _ (haut v) hv))
    (fun g u v => hinv g _ _ (haut u) (haut v))
    (fun v => ⟨⊥, fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; rfl, inferInstance,
      fun w => Set.finite_range _⟩)
    ⟨φ, admitted.self_mem_X φ⟩
  have hle : (⨆ U : {U : Submodule ℂ (admitted.X φ) // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
      (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap (admitted.X φ).subtype := by
    refine iSup_le ?_
    rintro ⟨U, h0, hst, hirr⟩ u hu
    let Y : Subrepresentation ρ := ⟨U, fun g v hv => hst g v hv⟩
    let τ : Representation ℂ (infU E n) U := Y.toRepresentation
    have hτ : τ.IsIrreducible := by
      refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun N hN => ?_⟩
      rcases hirr (N.map U.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨τ g w, hN g w hw, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype
          (by rw [h, Submodule.map_top, Submodule.range_subtype])
    exact UpperTheory.admissible_equivariantForms_representation E n B hdef hinv U τ
      (GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ τ hτ)
      ((admitted.X φ).subtype ∘ₗ U.subtype) (fun v => haut v.1) (fun _ _ => rfl) ⟨u, hu⟩
  exact hle hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactAndCongruentOfMemPrincipalCongr
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ), ∀ g ∈ UpperTheory.V.Af.KLoc F w n M,
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) ∧
    ∀ i j, valuation (w.adicCompletion F) ((g.val - 1) i j) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) := by
  intro F _ _ w n M g hg
  obtain ⟨k, hk, hkg⟩ := hg
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hint : ∀ x : UpperTheory.V.Af.Ohat F,
      valuation (w.adicCompletion F) (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := fun x => by
    have h1 : Valued.v (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := Subring.mem_iInf.1 x.2 w
    rw [← map_one (valuation (w.adicCompletion F)), ← Valuation.Compatible.vle_iff_le,
      Valuation.Compatible.vle_iff_le
        (v := (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))), map_one]
    exact h1
  let φ : UpperTheory.V.Af.Ohat F →+* w.adicCompletion F := (GlobalTheory.CuspRep.pLoc F w).comp (UpperTheory.V.Af.Ohat F).subtype
  let ψ : UpperTheory.V.Af.Ohat F →+* 𝒪[w.adicCompletion F] := φ.codRestrict _ fun x => hint x
  have hent : ∀ i j, g.val i j = φ (k.val i j) := fun i j => by
    have h1 := GlobalTheory.CuspRep.pLoc_locGL w g
    rw [← hkg] at h1
    rw [← h1]
    rfl
  refine ⟨⟨Matrix.GeneralLinearGroup.map ψ k, ?_⟩, fun i j => ?_⟩
  · ext i j
    rw [hent]
    rfl
  · have h1 : Ideal.Quotient.mk (Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) (k.val i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j :=
      congrArg (fun u : GL (Fin n) (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) => u.val i j)
        (MonoidHom.mem_ker.1 hk)
    have h2 : (k.val - 1) i j ∈ Ideal.span {(M : UpperTheory.V.Af.Ohat F)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    have h3 : (g.val - 1) i j = φ y * M := by
      rw [← map_natCast φ, ← map_mul, hy, Matrix.sub_apply, Matrix.sub_apply, map_sub, hent, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul]
    exact mul_le_of_le_one_left' (hint y)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormLocPowSubOneLeOfValuationSubOneLe
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_of_valuation_lt {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y < 1) :
    ‖j y‖ < 1 := by
  have h2 := Valued.tendsto_zero_pow_of_v_lt_one hy
  have h3 := (hj.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr (fun n => ?_)
  simp

private theorem norm_le_one_of_valuation_le {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y ≤ 1) :
    ‖j y‖ ≤ 1 := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t := algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) with ht
  have h1 : Valued.v t < 1 := by
    have : Valued.v t = w.valuation F (algebraMap (𝓞 F) F a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [this]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have ht0 : t ≠ 0 := by
    rw [ht, map_ne_zero]
    exact fun h => ha0 (by simpa using h)
  have hpos : 0 < ‖j t‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr ht0)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖j t‖⁻¹) hlt
  have h4 : Valued.v (t * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v t * Valued.v y ^ n ≤ Valued.v t * 1 := by
          gcongr
          exact pow_le_one' hy n
      _ < 1 := by rwa [mul_one]
  have h5 := norm_lt_one_of_valuation_lt j hj _ h4
  rw [map_mul, map_pow, norm_mul, norm_pow] at h5
  rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
  exact absurd (hn.trans h5) (lt_irrefl _)

theorem UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (M : ℕ)
    (u : w.adicCompletion F), valuation (w.adicCompletion F) (u - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    ‖GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w u - 1‖ ≤ ‖(M : Qbar p)‖ := by
  intro F _ _ w p _ ι M u h
  have hv : Valued.v (u - 1) ≤ Valued.v (M : w.adicCompletion F) :=
    ((Valuation.Compatible.vle_iff_le (v := valuation (w.adicCompletion F)) _ _).mpr h :)
  have hM1 : ‖(M : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ M
  have key : ∀ j : w.adicCompletion F →+* Qbar p, Continuous j → ‖j u - 1‖ ≤ ‖(M : Qbar p)‖ := by
    intro j hj
    by_cases hM : (M : w.adicCompletion F) = 0
    · rw [hM, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hv
      simp [hv]
    · have hx : Valued.v ((u - 1) / (M : w.adicCompletion F)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ hv zero_le
      have h1 := norm_le_one_of_valuation_le j hj _ hx
      have hM' : (M : Qbar p) ≠ 0 := by
        rw [← map_natCast j]
        exact (map_ne_zero j).mpr hM
      rw [map_div₀, map_sub, map_one, map_natCast, norm_div, div_le_one (norm_pos_iff.mpr hM')] at h1
      exact h1
  unfold GlobalTheory.HeckeGal.locPow
  refine finprod_induction (fun z : Qbar p => ‖z - 1‖ ≤ ‖(M : Qbar p)‖) (by simp) ?_ ?_
  · intro x y hx hy
    have hx1 : ‖x‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (x - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (hx.trans hM1) le_rfl)
    have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx1).trans hy
  · intro j
    rw [zpow_one]
    exact key j.1 j.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitBoundOfShapiroFunctorial
section
theorem UpperTheory.orbit_bound_of_shapiro_functorial :
    UpperTheory.V.Af.CohB.ShapiroFun → UpperTheory.V.Af.CohB.OrbBound := by
  intro h Γ Y _ _ y hB
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, ?_⟩
  intro X _ p hp hsurj D hD d ξ
  rw [h Γ X Y p hp y hsurj d ξ]
  refine (hc _).trans ?_
  have h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D := hD
  have hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y) :=
    Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt Cardinal.natCast_lt_aleph0)
  have hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) =
      Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d := by
    change Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _
    rw [rank_pi]
    simp only [rank_fun', Fintype.card_fin]
    rw [Cardinal.sum_const']
  rw [hr]
  push_cast
  rw [mul_assoc]
  gcongr
end

