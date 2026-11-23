module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationNormalisedBlowupSiegelModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PoincCov

theorem isProper_of_blowup {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S₀ : Scheme.{0}} {π₀ : S₀ ⟶ Z} (hB : FinalTheorems.Blowup π₀ J) : IsProper π₀ := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, -⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  obtain ⟨f, hf, -⟩ := hb.2 S₀ π₀ hB.1
  obtain ⟨f', hf', -⟩ := hB.2 X' b hb.1
  have e1 : f ≫ f' = 𝟙 S₀ := (hB.2 S₀ π₀ hB.1).unique (by simp [hf', hf]) (by simp)
  have e2 : f' ≫ f = 𝟙 X' := (hb.2 X' b hb.1).unique (by simp [hf, hf']) (by simp)
  haveI : IsIso f := ⟨f', e1, e2⟩
  haveI : IsSeparated z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsProper (b ≫ z) := by
    obtain ⟨m, e, he, he'⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b z
  rw [← hf]
  infer_instance

theorem isProper_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J) : IsProper π := by
  obtain ⟨-, S₀, π₀, ν, U, hB, rfl, hfin, -, -, -⟩ := h
  haveI := isProper_of_blowup z hz hB
  infer_instance

theorem isIso_restrict_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J)
    (V : Z.Opens) (hV : ∀ x ∈ V, x ∉ J.support) : IsIso (π ∣_ V) := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨hS, S₀, π₀, ν, U, hB, rfl, hfin, hUd, hνd, hνU⟩ := h
  haveI hπ₀V : IsIso (π₀ ∣_ V) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB V hV
  haveI := isProper_of_blowup z hz hB
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (π₀ ≫ z)
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hoi : IsOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme (π₀ ⁻¹ᵁ V).toScheme := .of_isOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀)
  haveI : IsIso (ν ∣_ (π₀ ⁻¹ᵁ V)) :=
    _root_.GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal ν U (π₀ ⁻¹ᵁ V) ((GlobalTheory.isNormalScheme_iff_pred S).mp hS) (GlobalTheory.IsNormalScheme.pred _) hUd hνd hνU
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' (by assumption) hπ₀V

end GlobalTheory.PoincCov

namespace GlobalTheory.PoincCov

theorem exists_normalisation_cover : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z), (∀ x ∈ J.support, x ∉ Set.range i) → IsNormBl π J → ∀ X₁ : Setup F W i, ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ X₁.M.Z) (ν : S₁ ⟶ S), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ IsFinite ν ∧ ν ≫ π = p₁ ≫ X₁.π ∧ IsIso (p₁ ∣_ (X₁.π ⁻¹ᵁ i.opensRange)) ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ X₁.π)) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (b : Sp R ⟶ X₁.M.Z), a ≫ π = b ≫ X₁.π → Set.range (jK R ≫ b ≫ X₁.π) ⊆ Set.range i → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν = a ∧ ξ₁ ≫ p₁ = b := by
  intro g _ n _ _ F Z z i _ hz hZ hiz hdense W J S π hJi hNB X₁
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI hπP : IsProper π := isProper_of_isNormBl z hz hNB
  let Vi : Z.Opens := i.opensRange
  haveI hπV : IsIso (π ∣_ Vi) := isIso_restrict_of_isNormBl z hz hZ hNB Vi (fun x hx hJ => hJi x hJ hx)
  have monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ S), u ≫ π = v ≫ π → Set.range (u ≫ π) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    have hu : Set.range u ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨w, rfl⟩
    have hv : Set.range v ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      have := hr ⟨w, rfl⟩
      rw [huv] at this
      exact this
    have hm : Mono ((π ⁻¹ᵁ Vi).ι ≫ π) := by
      rw [← morphismRestrict_ι]; infer_instance
    rw [← Scheme.Opens.range_ι] at hu hv
    rw [← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]
    congr 1
    rw [← cancel_mono ((π ⁻¹ᵁ Vi).ι ≫ π)]
    simp only [← Category.assoc, IsOpenImmersion.lift_fac]
    exact huv
  let U : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ Vi
  have hUne : (U : Set X₁.M.Z).Nonempty := by
    refine ⟨X₁.M.pt (show Sp X₁.Ω₁ from IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    show X₁.π (X₁.M.pt _) ∈ Vi
    rw [← Scheme.Hom.comp_apply, X₁.comp]
    exact ⟨_, rfl⟩
  haveI : Nonempty U := hUne.to_subtype
  let c : (U : Scheme.{0}) ⟶ S := X₁.π ∣_ Vi ≫ inv (π ∣_ Vi) ≫ (π ⁻¹ᵁ Vi).ι
  have hc : c ≫ π = U.ι ≫ X₁.π := by
    simp only [c, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  let j : (U : Scheme.{0}) ⟶ pullback π X₁.π := pullback.lift c U.ι hc
  haveI := X₁.fin
  haveI : LocallyOfFiniteType (X₁.π ≫ z) := inferInstance
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ z)
  haveI : IsLocallyNoetherian (pullback π X₁.π) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π X₁.π ≫ π ≫ z)
  have hjs : j ≫ pullback.snd π X₁.π = U.ι := pullback.lift_snd _ _ _
  haveI : QuasiCompact (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd π X₁.π)
  haveI : QuasiSeparated (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd π X₁.π)
  haveI : LocallyOfFiniteType (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd π X₁.π)
  haveI hfin : IsFinite j.fromNormalization :=
    GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) j
      (pullback.fst π X₁.π ≫ π ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap
  haveI : GlobalTheory.IsNormalScheme X₁.M.Z := X₁.normal
  haveI : GlobalTheory.IsNormalScheme (U : Scheme.{0}) := .of_isOpenImmersion U.ι
  let p₁ : j.normalization ⟶ X₁.M.Z := j.fromNormalization ≫ pullback.snd π X₁.π
  let ν : j.normalization ⟶ S := j.fromNormalization ≫ pullback.fst π X₁.π
  have hp₁ : j.toNormalization ≫ p₁ = U.ι := by
    show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd π X₁.π = U.ι
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, pullback.lift_snd]
  have hcomm : ν ≫ π = p₁ ≫ X₁.π := by simp [ν, p₁, pullback.condition]
  refine ⟨j.normalization, inferInstance, p₁, ν, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · show IsProper (j.fromNormalization ≫ pullback.snd π X₁.π)
    infer_instance
  · constructor
    have hUd : Dense (U : Set X₁.M.Z) := U.isOpen.dense hUne
    refine hUd.mono ?_
    intro x hx
    refine ⟨j.toNormalization ⟨x, hx⟩, ?_⟩
    rw [show p₁ (j.toNormalization ⟨x, hx⟩) = (j.toNormalization ≫ p₁) ⟨x, hx⟩ from rfl, hp₁]
    rfl
  · show IsFinite (j.fromNormalization ≫ pullback.fst π X₁.π)
    infer_instance
  · let O : (pullback π X₁.π).Opens := pullback.snd π X₁.π ⁻¹ᵁ U
    have hjO : Set.range j ⊆ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      show pullback.snd π X₁.π (j x) ∈ U
      rw [← Scheme.Hom.comp_apply, hjs]
      exact x.2
    let f0 : (U : Scheme.{0}) ⟶ O := IsOpenImmersion.lift O.ι j hjO
    have hf0 : f0 ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
    let s' := pullback.snd π X₁.π ∣_ U
    have hs' : s' ≫ U.ι = O.ι ≫ pullback.snd π X₁.π := morphismRestrict_ι _ _
    have e1 : f0 ≫ s' = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, hs', ← Category.assoc, hf0, hjs, Category.id_comp]
    have e2 : s' ≫ f0 = 𝟙 _ := by
      rw [← cancel_mono O.ι, Category.assoc, hf0, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hs', Category.assoc, Category.assoc, pullback.condition]
        · rw [Category.assoc, hc, ← Category.assoc]
          rintro _ ⟨w, rfl⟩
          rw [Scheme.Hom.comp_apply]
          exact (s' w).2
      · rw [Category.assoc, pullback.lift_snd, hs']
    haveI : IsIso s' := ⟨f0, e2, e1⟩
    haveI : IsIso f0 := ⟨s', e1, e2⟩
    have H := GlobalTheory.isPullback_toNormalization_of_mono f0 O.ι j (H := hf0.symm)
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict j.fromNormalization O) H.flip
    haveI : IsIso (j.fromNormalization ∣_ O) := by rw [← e]; infer_instance
    show IsIso ((j.fromNormalization ≫ pullback.snd π X₁.π) ∣_ U)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (by assumption) (by assumption)
  · obtain ⟨-, S₀, π₀, ν₀, U₀, hB, hνπ, -, -, -, -⟩ := hNB
    obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1
    have hpe : p₁ ≫ X₁.π = (ν ≫ ν₀) ≫ π₀ := by rw [← hcomm, Category.assoc ν ν₀ π₀, hνπ]
    have hK : D.KeepsRegular (ν ≫ ν₀) := by
      refine D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)
      rintro _ ⟨x, rfl⟩
      show (ν ≫ ν₀) (j.toNormalization x) ∉ D.idealSheaf.support
      rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
      intro h
      apply hJi _ h
      have : j.toNormalization ≫ (ν ≫ ν₀) ≫ π₀ = U.ι ≫ X₁.π := by rw [← hpe, ← Category.assoc, hp₁]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
      exact x.2
    have e : J.comap (p₁ ≫ X₁.π) = (D.pull (ν ≫ ν₀) hK).idealSheaf := by
      rw [GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]
    rw [e]
    exact GlobalTheory.EffCartierData.effCartier_idealSheaf _
  · intro R _ _ _ _ a b hab hgen
    let d : Sp R ⟶ pullback π X₁.π := pullback.lift a b hab
    have hr : Set.range (jK R ≫ b) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show X₁.π ((jK R ≫ b) w) ∈ Vi
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      exact hgen ⟨w, rfl⟩
    let y := IsOpenImmersion.lift U.ι (jK R ≫ b) hr
    have hy : y ≫ U.ι = jK R ≫ b := IsOpenImmersion.lift_fac _ _ _
    have hyj : y ≫ j = jK R ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc]
          exact hgen
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hy]
    obtain ⟨ξ, ⟨-, hξ⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R)
      (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d
      (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])
    refine ⟨ξ, ?_, ?_⟩
    · show ξ ≫ j.fromNormalization ≫ pullback.fst π X₁.π = a
      rw [← Category.assoc, hξ, pullback.lift_fst]
    · show ξ ≫ j.fromNormalization ≫ pullback.snd π X₁.π = b
      rw [← Category.assoc, hξ, pullback.lift_snd]

end GlobalTheory.PoincCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentation
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  intro R₀ R₁ _ _ _ q hq X₀ X₁ s₀ s₁ pr hp U
  have hqs : Function.Surjective (q : R₁ →+* R₀) := fun x ↦ ⟨algebraMap R₀ R₁ x, q.commutes x⟩
  have hid : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun x ↦ q.commutes x
    rw [this]
    exact Spec.map_id _
  let σ : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀)) (by rw [Category.id_comp, Category.assoc, hid, Category.comp_id])
  have hσ : σ ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hσ2 : σ ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (σ ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hσ, hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hleft : IsPullback σ s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hσ2 hp
  have hk2 : RingHom.ker (q : R₁ →+* R₀) ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    exact hq a b (RingHom.mem_ker.1 ha) (RingHom.mem_ker.1 hb)
  have hsurj : Surjective σ := surjective_of_isPullback_sqZero hk2 hqs rfl hleft
  refine ⟨σ ⁻¹ᵁ U, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hsurj.surj x
  have e : pr (σ y) = y := by
    have := congrArg (fun f : X₀ ⟶ X₀ ↦ f y) hσ
    simpa only [Scheme.Hom.comp_apply] using this.trans (by simp)
  change σ (pr (σ y)) ∈ U ↔ σ y ∈ U
  rw [e]

end GlobalTheory.SqZeroBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTraceCoefficientsNonvanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ProperDenom

variable {M W : Scheme.{0}}

end GlobalTheory.ProperDenom

namespace GlobalTheory.ProperDenom

theorem exists_local_denom : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] [IsProper f] [IsLocallyNoetherian W] (L : LB M), IsAmpleLB L → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → ∀ y : W, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, ∀ (V' : W.Opens), y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator
  | exact _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator
  | (apply _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator ..)

end GlobalTheory.ProperDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentation
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_opens_preimage_eq_of_sqZero_aug (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
    (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀)
    (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (W : X₁.Opens) :
    ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  have hcomp : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun r ↦ q.commutes r
  have hsp : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  let i : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀))
    (by rw [Category.id_comp, Category.assoc, hsp, Category.comp_id])
  have hi1 : i ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hi2 : i ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (i ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hi1, hsp]; exact IsPullback.id_horiz s₀
  have hsq : IsPullback i s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hi2 hp
  have hsurj : Function.Surjective (q : R₁ →+* R₀) := fun r ↦ ⟨algebraMap R₀ R₁ r, q.commutes r⟩
  have hI : (RingHom.ker (q : R₁ →+* R₀)) ^ 2 = 0 := by
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro y hy y' hy'
    exact (Ideal.mem_bot).2 (hq y y' (RingHom.mem_ker.1 hy) (RingHom.mem_ker.1 hy'))
  have hisurj : Surjective i := surjective_of_isPullback_sqZero hI hsurj rfl hsq
  have key : ∀ x : X₁, i.base (pr.base x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hisurj.surj x
    have h : pr.base (i.base y) = y := by rw [← Scheme.Hom.comp_apply, hi1]; rfl
    rw [h]
  refine ⟨i ⁻¹ᵁ W, ?_⟩
  ext x
  change i.base (pr.base x) ∈ W ↔ x ∈ W
  rw [key]

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombination
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_ordQ_eq_ord_div : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ),
    φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  intro k K _ _ c φ
  induction φ using Finsupp.induction with
  | zero => intro _; exact ⟨1, 1, one_pos, fun E => by simp⟩
  | single_add a b f ha hb ih =>
    intro h0
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h0
      exact hb h0
    have hf0 : f 0 = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha0), zero_add] at h0
      exact h0
    obtain ⟨m, g, hm, hg⟩ := ih hf0
    refine ⟨m * b.den, g ^ b.den * (Units.mk0 a ha0) ^ (b.num * m), ?_, fun E => ?_⟩
    · exact Nat.mul_pos hm b.pos
    · have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [map_add (f := _), Place.ordQ_single, hg E, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, E.ord_mul (pow_ne_zero _ g.ne_zero)
          (zpow_ne_zero _ (Units.mk0 a ha0).ne_zero), E.ord_pow, E.ord_zpow, Units.val_mk0]
      push_cast
      rw [← Rat.mul_den_eq_num b]
      field_simp
      ring

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_sections_embed_functionField_regular : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  first | exact @GlobalTheory.Desc.BCChart.exists_tensor_fnOf | exact GlobalTheory.Desc.BCChart.exists_tensor_fnOf | (intros; apply GlobalTheory.Desc.BCChart.exists_tensor_fnOf <;> assumption)
end

