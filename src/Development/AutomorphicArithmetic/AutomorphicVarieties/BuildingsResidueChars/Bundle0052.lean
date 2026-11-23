module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.adelicSolution_parallel :
    UpperTheory.V.Af.Sol.Parallel := by
  intro F _ _ _ χ a ha
  exact UpperTheory.heckeChar_parallel_weight F χ a ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.building_component_uniqueness :
    CompUnique := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CharacterExtendsToGaloisGroup
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem ext_two {Γ H A : Type} [Group Γ] [Group H] [CommGroup A] (i : H →* Γ) (hi : Function.Injective i)
    (δ : H →* A) (c : Γ) (hcc : c * c = 1) (hc : ∀ s, i s ≠ c) (hall : ∀ g, ∃ s, i s = g ∨ i s = g * c)
    (hinv : ∀ s, ∃ t, i t = c * i s * c ∧ δ t = δ s) :
    ∃ δ' : Γ →* A, δ'.comp i = δ ∧ δ' c = 1 := by
  choose p hp using hall
  have huniq : ∀ g s, (i s = g ∨ i s = g * c) → p g = s := by
    intro g s hs
    rcases hp g with h | h <;> rcases hs with h' | h'
    · exact hi (h.trans h'.symm)
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc ((p g)⁻¹ * s))
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc (s⁻¹ * p g))
    · exact hi (h.trans h'.symm)
  refine ⟨MonoidHom.mk' (fun g => δ (p g)) fun g g' => ?_, MonoidHom.ext fun s => ?_, ?_⟩
  · rcases hp g with h | h
    · rw [huniq (g * g') (p g * p g') (by
        rw [map_mul, h]
        rcases hp g' with h' | h'
        · exact Or.inl (by rw [h'])
        · exact Or.inr (by rw [h', mul_assoc])), map_mul]
    · obtain ⟨t, ht, hδ⟩ := hinv (p g')
      rw [huniq (g * g') (p g * t) (by
        rw [map_mul, h, ht, mul_assoc g c, mul_assoc c (i _), ← mul_assoc c c, hcc, one_mul]
        rcases hp g' with h' | h'
        · exact Or.inr (by rw [h', mul_assoc])
        · exact Or.inl (by rw [h', mul_assoc g', hcc, mul_one])), map_mul, hδ]
  · change δ (p (i s)) = δ s
    rw [huniq _ s (Or.inl rfl)]
  · change δ (p c) = 1
    rw [huniq c 1 (Or.inr (by rw [map_one, hcc])), map_one]

private theorem conj_on {F M Ω : Type} [Field F] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra F Ω]
    [Algebra M Ω] {c : G F Ω} (hc : IsConjEl c) (x : M) :
    c (algebraMap M Ω x) = algebraMap M Ω (IsCMField.complexConj M x) := by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ?_
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm

private theorem conj_comm {K M : Type} [Field K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (x : M) : IsCMField.complexConj M (σ x) = σ (IsCMField.complexConj M x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  refine φ.injective ?_
  rw [IsCMField.complexEmbedding_complexConj]
  exact (IsCMField.complexEmbedding_complexConj M (φ.comp (σ : M →+* M)) x).symm

private theorem lift_fix {F M Ω : Type} [Field F] [Field M] [Field Ω] [Algebra F M] [Algebra F Ω] [Algebra M Ω]
    [IsScalarTower F M Ω] (g : G F Ω) (hg : ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) :
    ∃ s : G M Ω, resG F M Ω s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, AlgEquiv.ext fun _ => rfl⟩

private theorem ex_conj (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ c : G (maximalRealSubfield K) Ω, IsConjEl c := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  let φ : K →+* ℂ := Classical.choice inferInstance
  letI : Algebra K ℂ := φ.toAlgebra
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := K) (S := Ω) (M := ℂ)).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := maximalRealSubfield K) j
    (ComplexEmbedding.conjugate j) (RingHom.ext fun x =>
      ((mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))).symm)
  exact ⟨σ.symm, j, fun x => DFunLike.congr_fun hσ x⟩

theorem UpperTheory.character_extends_to_galois_group :
    UpperTheory.V.Af.Sol.ExtChar := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
  have kill : ∀ t : G K Ω, (∀ x : M, t (algebraMap M Ω x) = algebraMap M Ω x) → δ t = 1 := fun t ht => by
    obtain ⟨s, rfl⟩ := lift_fix t ht
    exact DFunLike.congr_fun hδ s
  obtain ⟨c, hc⟩ := ex_conj K Ω
  have hcc : c * c = 1 := by
    obtain ⟨j, hj⟩ := hc
    exact AlgEquiv.ext fun x => j.injective (by
      rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply])
  have hKM : ∀ (g : G (maximalRealSubfield K) Ω), (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) →
      ∃ s : G K Ω, resG (maximalRealSubfield K) K Ω s = g ∧ δ s = 1 := fun g hg => by
    obtain ⟨s, rfl⟩ := lift_fix (M := K) g fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω, hg]
    exact ⟨s, rfl, kill s hg⟩
  obtain ⟨δ', h1, h2⟩ := ext_two (resG (maximalRealSubfield K) K Ω) (AlgEquiv.restrictScalars_injective _) δ c hcc
    (fun s hs => IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (algebraMap K Ω).injective (by
      rw [← conj_on hc, ← hs]
      exact s.commutes x)))
    (fun g => by
      have h2 : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 :=
        (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸
          IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K
      rw [Nat.card_eq_two_iff' 1] at h2
      by_cases hg : g.restrictNormal K = 1
      · obtain ⟨s, hs⟩ := lift_fix (M := K) g fun x => by
          rw [← AlgEquiv.restrictNormal_commutes, hg, AlgEquiv.one_apply]
        exact ⟨s, Or.inl hs⟩
      · have hg' := h2.unique hg (IsCMField.complexConj_ne_one K)
        obtain ⟨s, hs⟩ := lift_fix (M := K) (g * c) fun x => by
          rw [AlgEquiv.mul_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, hg',
            IsCMField.complexConj_apply_apply]
        exact ⟨s, Or.inr hs⟩)
    (fun s => by
      obtain ⟨t, ht, hδt⟩ := hKM (c * resG _ K Ω s * c * (resG _ K Ω s)⁻¹) fun x => by
        obtain ⟨y, rfl⟩ := (s.restrictNormal M).surjective x
        change c (s (c (s.symm _))) = _
        rw [AlgEquiv.restrictNormal_commutes, s.symm_apply_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes,
          conj_on hc, conj_comm, IsCMField.complexConj_apply_apply, AlgEquiv.restrictNormal_commutes]
      exact ⟨t * s, by rw [map_mul, ht, inv_mul_cancel_right], by rw [map_mul, hδt, one_mul]⟩)
  have h3 : ∀ g : G (maximalRealSubfield K) Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → δ' g = 1 :=
    fun g hg => by
      obtain ⟨s, rfl, hs⟩ := hKM g hg
      exact (DFunLike.congr_fun h1 s).trans hs
  refine ⟨δ', h1, fun d hd => ?_, ?_⟩
  · have h4 := h3 (d * c) fun x => by
      rw [AlgEquiv.mul_apply, conj_on hc, conj_on hd, IsCMField.complexConj_apply_apply]
    rwa [map_mul, h2, mul_one] at h4
  · let f : M →ₐ[maximalRealSubfield K] Ω := IsScalarTower.toAlgHom (maximalRealSubfield K) M Ω
    haveI : FiniteDimensional (maximalRealSubfield K) f.fieldRange :=
      (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen f.fieldRange)
    exact h3 g fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompatiblePolarizationOfLink
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.compatible_polarization_of_link :
    HypothesesH → CompatCsd → SatLink → CompatPol := by
  intro PH hC hS E Ω _ _ _ _ _ _ l _ ι a ha P χ ξ m hreg hpol hξ hd σ hσ
  have Pr := PH.toClassicalTheorems
  obtain ⟨r, wt, HT, H⟩ := (_root_.GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair Pr.litN.aut.gk).2 Pr.litN.aut.gal E Ω l ι a ha P χ hreg hpol
  have hatt : AttC ι r P := by
    refine ⟨H.ss, (((hS E a P).2).and (eventually_not_mem E l)).mono ?_⟩
    rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, satFrob Pr E Ω l ι a r H.cont w hw (σ w) B (((hS E a P).1 w _ (hσ w) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc _ (hσ w)⟩
  obtain ⟨art, hart⟩ := Pr.litN.aut.art E Ω
  obtain ⟨μ, hμc, hμ⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hξ)
  have hL := hC E Ω l ι a ha (tw r μ) (P.twist ξ) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ H.cont hμc) (regAlg_twist hreg hξ) hd
    (Cq.attTwist E Ω l ι a r P hatt art ξ m μ hart hμ)
  obtain ⟨T⟩ := Loc.tiedP l
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w A h O _ _ _ Bw hj => ?_, fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩⟩,
    H.weights⟩
  · exact ⟨(H.above _ _ ⟨T⟩ w A h O Bw hj).deRham, (H.above _ _ ⟨T⟩ w A h O Bw hj).jumps⟩
  · exact H.away w hw A h rc hrc _ (hσ w)
  · have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) :=
      Pr.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val))
        (H.above _ _ ⟨T⟩ w A h O Bw hj).deRham
    obtain ⟨c1, c2⟩ := (hL w _ ((hσ w).twist ξ) A h rc hrc).2 O Bw hj
    exact ⟨hpst, Lev.untwistS Pr.litN.aut.chA Pr.litN.aut.chW Pr.litN.aut.berger E Ω l ι a r H.cont art ξ m μ hart
      (isAlgPos_of_isAlg hξ) hμc hμ w A h O Bw hj hpst c1 (σ w) rc hrc c2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConjugatesAgree
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem conj_val {K M Ω : Type} [Field K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] (hM : RC M) :
    ∃ s : M → M, ∀ c : G K Ω, IsConjEl c → ∀ x : M, c (algebraMap M Ω x) = algebraMap M Ω (s x) := by
  rcases hM with hM | hM
  · refine ⟨id, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    have h : ComplexEmbedding.IsReal (j.comp (algebraMap M Ω)) := IsTotallyReal.complexEmbedding_isReal _
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 h) x
  · refine ⟨fun x => IsCMField.complexConj M x, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.cyclotomic_char_conj_invariant :
    UpperTheory.V.Af.Sol.CycConj := by
  intro F Ω _ _ _ _ _ l _ c hc
  obtain ⟨j, hj⟩ := hc
  haveI : CharZero Ω := j.charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩
  have hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹ := by
    intro x m hm hx
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm
    have hs : Complex.normSq (j x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]; norm_num
    rw [Complex.inv_def, hs]; simp
  set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg
  have hcyc : cyclotomicCharacter Ω l g = -1 := by
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow]
    have hk : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
    rw [← modularCyclotomicCharacter.unique Ω _ g (c := -1)]
    · simp
    · intro t ht
      have ht' : (t : Ω) ^ (l ^ n) = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      have hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
      obtain ⟨m, hm⟩ := hdvd
      have hne : (t : Ω) ≠ 0 := t.ne_zero
      have key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, hm, pow_mul, ht', one_pow]
      rw [key]
      exact hinv _ (l ^ n) (NeZero.ne _) ht'
  show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1
  have : ReciprocityTheory.Gal.cycZ F Ω l c = -1 := hcyc
  rw [this]
  ext; simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont F Ω l

private theorem mem_plus {F₀ F : Type} [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F]
    [IsTotallyReal F₀] (x : F₀) : algebraMap F₀ F x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  exact DFunLike.congr_fun
    (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F₀ F)))) x

theorem UpperTheory.cyclotomicCharacter_plusPart :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.CycConj → UpperTheory.V.Af.Sol.ToPolC := by
  intro hA hC F Ω _ _ _ _ _ _ l _ ι n r hpol
  obtain ⟨F₀, _, _, _, _, _, _, hR, μ, c, P, hμ, hs, ⟨j, hj⟩, hp⟩ := hpol
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  letI : Algebra F₀ (maximalRealSubfield F) :=
    ((algebraMap F₀ F).codRestrict (maximalRealSubfield F) mem_plus).toAlgebra
  haveI : IsScalarTower F₀ (maximalRealSubfield F) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply F₀ F Ω x
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hcyc : IsAlgChar ι (cycBar (maximalRealSubfield F) Ω l ^ ((n : ℤ) - 1)) := by
    refine (hA (maximalRealSubfield F) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, (n : ℤ) - 1, 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hres := (hA F₀ Ω l ι).2.2 (maximalRealSubfield F) μ hμ
  obtain ⟨χ, hc, art, a, h1, h2, h3⟩ := ((hA (maximalRealSubfield F) Ω l ι).2.1 _ _ hcyc hres).1
  refine ⟨_, χ, c', P, ⟨hc, art, a, h1, h2, h3⟩, fun d d' hd hd' => ?_, ⟨j, hj⟩, fun s s' hss => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply]
    rw [hC _ Ω l d hd, hC _ Ω l d' hd', hs (resG F₀ _ Ω d) (resG F₀ _ Ω d') hd hd']
  · rw [hp s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hss x)]
    congr 2
    change μ (resG F₀ F Ω s) = cycBar F Ω l s ^ (1 - (n : ℤ)) * (cycBar F Ω l s ^ ((n : ℤ) - 1) * μ (resG F₀ F Ω s))
    rw [← mul_assoc, ← zpow_add]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterEqLocalDetSplitNonsplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_finGL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (k : GL (Fin n) (Af E))
    (hk : ∀ u, cLoc u g = Matrix.GeneralLinearGroup.map (pLoc E u) k) : (g : GA E n) = finGL E n k := by
  have hinf : cInf g = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1
  refine ga_ext (hinf.trans (pInf_finGL k).symm) ?_
  rw [pFin_finGL]
  refine Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)
  exact congrArg Units.val (hk u)

private theorem cLoc_off {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w u : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (hu : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    cLoc u g = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)

theorem UpperTheory.detCharacter_eq_localDet_split_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E), GlobalTheory.ThetaPull.thetaChar ν = ν → ∀ (w : Plc E), ∀ g ∈ locU n w, (IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n (ν * ν) w (cLoc w g)) ∧ (¬ IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n ν w (cLoc w g)) := by
  intro E _ _ _ n ν hν w g hg
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨hne, hun, hover⟩ := GlobalTheory.SplitPts.over_split hw
    set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'
    have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g)) := by
      refine eq_finGL hg _ fun u => ?_
      rw [map_mul]
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]
      · by_cases h2 : u = w'
        · rw [h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]
        · rw [pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]
          exact cLoc_off hg fun h => (hover u h).elim h1 h2
    have hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) =
        (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      have h := congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      refine Eq.trans ?_ h
      exact congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)
    have h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g) := by
      change ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) =
        ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))
      have h3 := GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))
      rw [hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv] at h3
      exact h3
    rw [e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]
    rfl
  · have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g)) := by
      refine eq_finGL hg _ fun u => ?_
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL]
      · rw [pLoc_locGL_of_ne h1]
        exact cLoc_off hg fun h => hw ⟨u, h1, h⟩
    rw [e, CuspSub.chiDet_locGL]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterKerOpenTrivialRationalArchimedean
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_root (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (hm : 0 < m)
    (d : Ideles E) (hd : pFin E (d : Ad E) = 1) : ∃ y : Ideles E, y ^ m = d := by
  have h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h
  let Y : Ad E := ((y : InfiniteAdeleRing E), (1 : Af E))
  have hY : Y ^ m = (d : Ad E) := Prod.ext (funext hy) ((one_pow m).trans hd.symm)
  have hu : IsUnit Y := (isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩

theorem UpperTheory.detCharacter_ker_open_trivial_rational_archimedean :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E) (m : ℕ), 0 < m → ν.OrderDvd m → IsOpen (((chiDet n ν).comp (UA E n).subtype).ker : Set (UA E n)) ∧ (∀ g ∈ ratU E n, chiDet n ν (g : UA E n) = 1) ∧ ∀ g ∈ infU E n, chiDet n ν (g : UA E n) = 1 := by
  intro E _ _ _ n ν m hm h
  have h1 : ∀ x, ν.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  refine ⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩
  · exact ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  · intro g hg
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
    rw [← hγ, chiDet_ratGL]
  · intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1 := hg
    obtain ⟨y, hy⟩ := exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by
      rw [← GlobalTheory.CuspRep.det_map, hg']; simp)
    change ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1
    rw [← hy, map_pow, h1]
end

