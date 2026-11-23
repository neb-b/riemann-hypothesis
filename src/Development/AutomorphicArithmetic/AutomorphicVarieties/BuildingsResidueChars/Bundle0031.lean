module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeComplexConjInvariance
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 E), normV v = Ideal.absNorm v.asIdeal := by
    intro v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [cPl_asIdeal]
  exact (Ideal.map_symm _).symm

private theorem conj_algebraMap {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E]
    [Algebra F E] (x : F) : IsCMField.complexConj E (algebraMap F E x) = algebraMap F E x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))
  exact RingHom.congr_fun h x

theorem UpperTheory.baseChange_complexConj_invariance :
    UpperTheory.V.Af.Bc.BcConj := by
  intro F E _ _ _ _ _ _ _ n π P h
  have h1 := h.unr
  have h2 := (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually h1
  filter_upwards [h1, h2] with w a b
  obtain ⟨B, hB, hP⟩ := a (w.under (𝓞 F)) rfl _ (normV_under w)
  obtain ⟨B', hB', hP'⟩ := b (w.under (𝓞 F)) (by
    have e := cPl_asIdeal w
    change _ = (cPl w).asIdeal.comap _
    rw [e]
    ext x
    have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) =
        algebraMap (𝓞 F) (𝓞 E) x := RingOfIntegers.ext (conj_algebraMap (x : F))
    rw [Ideal.mem_comap, Ideal.mem_comap, e2]
    rfl) _ ((normV_cPl w).trans (normV_under w))
  obtain rfl := TR.CuspSub.HasSat.unique hB hB'
  exact ⟨_, hP, hP'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyRankEqHomologyRank
section
open CategoryTheory

theorem UpperTheory.cohomology_rank_eq_homology_rank :
    UpperTheory.V.Af.CohB.RankHomology := by
  intro C q
  have h1 : Function.Surjective (C.homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h2 : Function.Injective (C.iCycles q).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (LinearMap.rank_le_of_surjective _ h1).trans (LinearMap.rank_le_of_injective _ h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologySumBound
section
private theorem UpperTheory.V.Af.CohB.cardSum_eq (I : Type) [hI : Fintype I] :
    ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i := by
  refine Fintype.induction_empty_option (P := fun I _ => ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i)
    ?_ ?_ ?_ I
  · intro α β _ e h f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Equiv.sum_comp e f, ← h]
    exact Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := fun b => (f b).out) e).symm
  · intro f
    simp [Cardinal.sum]
  · intro α _ h f
    rw [Fintype.sum_option, ← h]
    have e0 : (Σ o : Option α, (f o).out) ≃ (f none).out ⊕ (Σ a : α, (f (some a)).out) :=
      { toFun := fun x => match x with
          | ⟨none, y⟩ => Sum.inl y
          | ⟨some a, y⟩ => Sum.inr ⟨a, y⟩
        invFun := fun x => match x with
          | Sum.inl y => ⟨none, y⟩
          | Sum.inr ⟨a, y⟩ => ⟨some a, y⟩
        left_inv := by rintro ⟨_ | a, y⟩ <;> rfl
        right_inv := by rintro (y | ⟨a, y⟩) <;> rfl }
    have e := Cardinal.mk_congr e0
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_out] at e
    exact e

open CategoryTheory in
theorem UpperTheory.cohomology_sum_bound :
    UpperTheory.V.Af.CohB.SumBound := by
  intro Γ I _ _ A B π ι h q
  let F : Rep.{0} ℂ Γ ⥤ ModuleCat.{0} ℂ :=
    groupCohomology.cochainsFunctor ℂ Γ ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) q
  have hF : ∑ i, F.map (π i) ≫ F.map (ι i) = 𝟙 (F.obj A) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← F.map_id, ← h, F.map_sum]
    simp only [Functor.map_comp]
  change Module.rank ℂ (F.obj A) ≤ ∑ i, Module.rank ℂ (F.obj (B i))
  let φ : F.obj A →ₗ[ℂ] (∀ i, F.obj (B i)) := LinearMap.pi fun i => (F.map (π i)).hom
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg (fun f => ModuleCat.Hom.hom f x) hF
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : (F.map (π i)).hom x = 0 := congrFun hx i
    rw [h2, map_zero]
  have h3 := LinearMap.rank_le_of_injective φ hφ
  rw [rank_pi] at h3
  rw [← UpperTheory.V.Af.CohB.cardSum_eq]
  simpa using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsInjective
section
open scoped Matrix

theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsSurjective
section
open scoped Matrix in
theorem UpperTheory.cohomology_to_coinvariants_surjective :
    UpperTheory.V.Af.CohB.ToCoSurj := by
  intro Γ X Y _ _ _ p hp y h d ξ F
  choose c hc using h
  have hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y := fun x => by
    change p (c x • x) = y
    rw [hp, hc]
  have key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 →
      ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z := by
    intro g g' z z' hz
    have hz' : z.1 = (g * g'⁻¹) • z'.1 := by rw [mul_smul, ← hz, smul_inv_smul]
    have hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y := by
      have h1 : p z.1 = y := z.2
      have h2 : p z'.1 = y := z'.2
      rw [hz', hp, h2] at h1
      exact h1
    have h3 := congrFun (F.2 ⟨_, hs⟩ g') z
    have h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z' := by
      apply Subtype.ext
      change (g * g'⁻¹)⁻¹ • z.1 = z'.1
      rw [hz', inv_smul_smul]
    change F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3
    rw [h4, inv_mul_cancel_right] at h3
    rw [h3, map_mul, Matrix.mulVec_mulVec]
  refine ⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩
  apply Subtype.ext
  funext g z
  rw [UpperTheory.V.Af.CohB.toCo_apply]
  exact key g _ z _ (by simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharEqLocPowOfLocalArtinUnit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (σ : Weil h),
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    ((cycBar F Ω p σ : (Qbar p)ˣ) : Qbar p) = GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w (a σ : w.adicCompletion F) := by
  intro hG F Ω _ _ _ _ _ w A h a ha p _ ι σ hv
  obtain ⟨art, hart⟩ := hG F Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1)
  have e := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hL
  have h1 := hL.loc (a σ) σ (ha.glob art hart σ)
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hu : Valued.v (a σ : w.adicCompletion F) = 1 := he.eq_one_iff_eq_one.1 hv
  have h2 : (GlobalTheory.HeckeGal.Model.absPow F ((1 : ℕ) : ℝ)).loc w (a σ) = 1 :=
    (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F ((1 : ℕ) : ℝ)).1 w _ hu
  rw [h2, e, pow_one, cyc_eq_map_cycZ] at h1
  simp only [Units.val_one, map_one, one_mul, Nat.cast_one] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeformationSpaceLocalCharactersContinuous
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem l_mem {l : ℕ} [Fact l.Prime] (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
  intro hu
  have h0 := IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu
  rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one] at h0
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith

private theorem inc_mem {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  obtain ⟨hinj, -⟩ := dvrFacts l c.O
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hx' : π ∣ x := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    exact hx
  have hl0 : (l : c.O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] c.O)]
    exact (map_ne_zero_iff _ hinj).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  obtain ⟨w, hw⟩ : (l : c.O) ∣ x ^ n := hn.dvd_iff_dvd_left.2 (pow_dvd_pow_of_dvd hx' n)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.pow n
  rw [← map_pow, hw, map_mul, map_natCast] at hu'
  exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem c') (isUnit_of_mul_isUnit_left hu')

theorem UpperTheory.deformationSpace_local_characters_continuous :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Ok → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (R : Type) [CommRing R] [IsLocalRing R] (f : X.B →+* R), (∀ b ∈ maximalIdeal X.B, f b ∈ maximalIdeal R) → (∀ a ∈ maximalIdeal c'.O, f (algebraMap c'.O X.B a) = 0) → (l : R) = 0 ∧ ∃ κ : ∀ v : T.ι, Fin 4 → Dec (F := T.F) (T.pl v) →* Rˣ, ∀ v i, (∀ s, ((κ v i s : Rˣ) : R) = f (X.ψ v i s)) ∧ AdicCont (maximalIdeal R) (fun s => ((κ v i s : Rˣ) : R)) ∧ ∀ s : Dec (F := T.F) (T.pl v), (s : G T.F Ω) ∈ Ine (F := T.F) (T.pl v) → ((κ v i s : Rˣ) : R) - 1 ∈ maximalIdeal R ∧ κ v i s * κ v i.rev s = 1 := by
  intro Ω _ _ _ l _ c D T hT c' h X R _ _ f hf hf0
  have hl' : f (algebraMap c'.O X.B (l : c'.O)) = 0 := hf0 _ (l_mem c')
  rw [map_natCast, map_natCast] at hl'
  have hP := UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude (T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) X.P X.pair
  have one : ∀ v i, X.ψ v i 1 = 1 := by
    intro v i
    apply X.inj
    rw [X.ψ_map v i 1 (Subgroup.one_mem _), map_one]
    exact (hP v i).1
  have mul : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v, ∀ t ∈ (T.fr ∅).Gv v,
      X.ψ v i (s * t) = X.ψ v i s * X.ψ v i t := by
    intro v i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map v i _ (Subgroup.mul_mem _ hs ht), X.ψ_map v i s hs, X.ψ_map v i t ht]
    exact (hP v i).2.1 s hs t ht
  have nu : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v,
      X.ψ v i s * X.ψ v i.rev s = algebraMap c'.O X.B (inc h ↑((T.fr ∅).ν s)) := by
    intro v i s hs
    apply X.inj
    rw [map_mul, X.ψ_map v i s hs, X.ψ_map v i.rev s hs, (hP v i).2.2 s hs, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply c'.O X.B X.A]
  have hunit : ∀ (v : T.ι) (i : Fin 4) (s : Dec (F := T.F) (T.pl v)), IsUnit (f (X.ψ v i s)) := by
    intro v i s
    have hu : IsUnit (X.ψ v i s * X.ψ v i.rev s) := by
      rw [nu v i s s.2]
      exact ((Units.isUnit _).map (inc h)).map (algebraMap c'.O X.B)
    exact (isUnit_of_mul_isUnit_left hu).map f
  have key : ∀ u : (c.O)ˣ, residue c.O ↑u = 1 → f (algebraMap c'.O X.B (inc h ↑u)) = 1 := by
    intro u hu
    have h1 : (↑u : c.O) - 1 ∈ maximalIdeal c.O :=
      (residue_eq_zero_iff _).1 (by rw [map_sub, hu, map_one, sub_self])
    have h2 := hf0 _ (inc_mem h h1)
    rwa [map_sub, map_one, map_sub, map_one, map_sub, map_one, sub_eq_zero] at h2
  refine ⟨hl', fun v i => IsUnit.liftRight
    { toFun := fun s => f (X.ψ v i s)
      map_one' := by
        simp only [OneMemClass.coe_one]
        exact (congrArg f (one v i)).trans (map_one f)
      map_mul' := by
        intro s t
        simp only [Subgroup.coe_mul]
        rw [mul v i s s.2 t t.2, map_mul] } (fun s => hunit v i s), ?_⟩
  intro v i
  refine ⟨fun s => rfl, ?_, ?_⟩
  · intro N
    have hle : maximalIdeal X.B ^ N ≤ (maximalIdeal R ^ N).comap f := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (hf b hb))) N
    exact (X.ψ_cont v i N).comp (Ideal.quotientMap (maximalIdeal R ^ N) f hle)
  · intro s hs
    have hr := hT.ineL (T.pl v) (T.ovl v) s hs
    have hps : ∀ j, residue c.O ↑(D.ps j (resQ T.F s)) = 1 := fun j => by
      have e := congrArg (fun M => M j j) hr
      simpa [Raw.rbar, Raw.r0, mapRep_apply, diagRep] using e
    refine ⟨?_, ?_⟩
    · show f (X.ψ v i s) - 1 ∈ maximalIdeal R
      have hres : residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) = 1 := by
        have h1 : (↑(D.ps (lab T.pr i) (resQ T.F s)) : c.O) - 1 ∈ maximalIdeal c.O :=
          (residue_eq_zero_iff _).1 (by rw [map_sub, hps, map_one, sub_self])
        have h2 := inc_mem h h1
        rw [map_sub, map_one, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at h2
        exact h2
      have hB : X.ψ v i s - 1 ∈ maximalIdeal X.B := by
        rw [← res_eq_zero_iff c'.O X.B, map_sub, map_one, X.ψ_red v i s s.2]
        show residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) - 1 = 0
        rw [hres, sub_self]
      have := hf _ hB
      rwa [map_sub, map_one] at this
    · apply Units.ext
      show f (X.ψ v i s) * f (X.ψ v i.rev s) = 1
      rw [← map_mul, nu v i s s.2]
      exact key _ (hps 0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAlgebraicHeckeCharCyclotomic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isOpen_ker_kills {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (G F Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

private theorem exists_hchar_fin {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    ∃ χ : HChar F, IsAlgPos χ 0 ∧ IsLAdicOf art ι χ 0 φ := by
  have ho := isOpen_ker_kills hM hφ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨χ, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem exists_hchar_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ j) := by
  have key : ∀ m : ℕ, ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ m) := fun m => by
    have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F m
    obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
    have e : μ = cycBar F Ω l ^ m := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
    exact ⟨_, _, h, e ▸ hL⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using key m
  · obtain ⟨χ, n, h1, h2⟩ := key m
    exact ⟨_, _, isAlgPos_inv h1, by simpa using h2.inv⟩

private theorem continuous_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Continuous (cycBar F Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar F Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  exact e ▸ hμ

end Hecke

theorem UpperTheory.exists_algebraic_heckeChar_cyclotomic :
    UpperTheory.V.Af.Bc.CycHecke := by
  intro H F Ω _ _ _ _ _ l _ ι wt θ hθ
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨M, φ, hM, hφ, rfl⟩ := hθ
  obtain ⟨χ, h1, h2⟩ := exists_hchar_fin ha ι hM hφ
  obtain ⟨χ', n, h3, h4⟩ := exists_hchar_cyc ha ι wt
  refine ⟨?_, _, art, _, ha, isAlgPos_mul h3 h1, h4.mul h2⟩
  have hc : Continuous φ := continuous_of_isOpen_ker' φ (isOpen_ker_kills hM hφ)
  exact ((continuous_cyc ha ι).zpow wt).mul hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicDoubleCosets
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep

private theorem ohat_of {F : Type} [Field F] [NumberField F] {x : Af F} (hx : x ∈ PIW.ClassFinD.Ohat F) :
    x ∈ UpperTheory.V.Af.Ohat F :=
  UpperTheory.V.Af.mem_Ohat.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 hx)

theorem UpperTheory.finite_adelic_double_cosets :
    UpperTheory.V.Af.CohB.FinDC := by
  intro F _ _ n
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of _root_.GlobalTheory.IwasawaFinAd.iwasawaAf _root_.GlobalTheory.UnipApproxGL.unipApprox PIW.ClassFinD.idele_class_finite F n
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS g
  refine ⟨γ, s, hs, k, UpperTheory.V.Af.mem_KLev.2 ⟨fun a b => ohat_of (hk.1 a b), fun a b => ohat_of (hk.2 a b),
    fun a b => ⟨_, sub_mem (ohat_of (hk.1 a b)) (ohat_of (PIW.ClassFinD.matInt_one F n a b)), ?_⟩⟩, hx⟩
  rw [Nat.cast_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfRatEigensystemCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem trace_conj_gl3 {k : Type} [Field k] (g x : GL (Fin 3) k) :
    ((g * x * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = (x : Matrix (Fin 3) (Fin 3) k).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw
end

