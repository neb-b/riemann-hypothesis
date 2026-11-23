module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftOfUniqueOfSimilitude
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.JoinModels

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isPullback_toImage_comp {U P Z : Scheme.{0}} (j : U ⟶ P) (q : P ⟶ Z) (v : U ⟶ Z)
    (h : j ≫ q = v) [QuasiCompact j] [IsSeparated q] [Flat v] [Mono v] :
    IsPullback (𝟙 U) j.toImage v (j.imageι ≫ q) := by
  have Hu := IsPullback.of_hasPullback v q
  have : Mono (pullback.snd v q) := inferInstance
  let c : U ⟶ pullback v q := pullback.lift (𝟙 U) j (by simpa using h.symm)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have H := (GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ hc₂).paste_horiz Hu
  rwa [hc₁] at H

theorem exists_common_projective {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ j ≫ p i = u i := by
  classical
  have key : ∀ S : Finset I, ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i ∈ S, ∃ p : P ⟶ X i, p ≫ s i = r ∧ j ≫ p = u i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨X i, s i, u i, hs i, hu i, by simp⟩
    | insert k S _ ih =>
      obtain ⟨P, r, j, h1, h2, h3⟩ := ih
      refine ⟨pullback r (s k), pullback.fst _ _ ≫ r, pullback.lift j (u k) (h2.trans (hu k).symm),
        GlobalTheory.ProjSpace.isProjOver_pullback h1 (hs k), by rw [pullback.lift_fst_assoc, h2], fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨p, hp1, hp2⟩ := h3 i hi
        exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp1], by rw [pullback.lift_fst_assoc, hp2]⟩
  have := Fintype.ofFinite I
  obtain ⟨P, r, j, h1, h2, h3⟩ := key Finset.univ
  choose p hp using fun i => h3 i (Finset.mem_univ i)
  exact ⟨P, r, j, p, h1, h2, hp⟩

theorem isProper_of_proj {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str O N
  infer_instance

theorem exists_join {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) [∀ i, Flat (u i)] [∀ i, Mono (u i)]
    [∀ i, QuasiCompact (u i)] :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ IsPullback (𝟙 U) j (u i) (p i) := by
  obtain ⟨P, r, j, p, h1, h2, h3⟩ := exists_common_projective σ X s hs u hu
  have := isProper_of_proj h1
  have hsep : ∀ i, IsSeparated (p i) := fun i => by
    have : IsSeparated (p i ≫ s i) := by rw [(h3 i).1]; infer_instance
    exact IsSeparated.of_comp (p i) (s i)
  have : QuasiCompact j := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have : QuasiCompact (j ≫ p i) := by rw [(h3 i).2]; infer_instance
    exact QuasiCompact.of_comp j (p i)
  obtain ⟨N, e, he, hr⟩ := h1
  refine ⟨j.image, j.imageι ≫ r, j.toImage, fun i => j.imageι ≫ p i,
    ⟨N, j.imageι ≫ e, inferInstance, by rw [Category.assoc, hr]⟩, by simpa using h2, fun i => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h3 i).1]
  · exact isPullback_toImage_comp j (p i) (u i) (h3 i).2

theorem exists_join_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  intro E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hR _ _
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  have hβ : algebraMap O F = β := rfl
  have hcl : ∀ i, ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (κ : (C i).X ⟶ X'), IsProjOver s' ∧
      IsPullback κ (C i).s s' (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact GlobalTheory.ProjClosure.exists_projective_closure O (R i) (a i) (C i).X (C i).s (C i).proj
  choose X' s' κ hs' hk using hcl
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hko : ∀ i, IsOpenImmersion (κ i) := fun i => MorphismProperty.of_isPullback (hk i).flip (hbo i)
  have hj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ QuasiCompact (C i).j ∧ QuasiCompact (κ i) :=
    fun i => by
      obtain ⟨⟨⟨_, _⟩, _, hfr⟩, _, _⟩ := hR i
      letI := (ω i).toAlgebra
      obtain ⟨-, -, -, h1, h2, -, h3⟩ := GlobalTheory.genericPart_dense_proOpen (R i) F (C i).X U (C i).s (C i).jQ
        (C i).flat (C i).proj (C i).jQ_open (C i).jQ_dense
      exact ⟨h1, h2, h3, MorphismProperty.of_isPullback (hk i).flip inferInstance⟩
  have hωb : ∀ i, spMap (ω i) ≫ spMap (b i) = spMap β := fun i => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, (hR i).2.1]
  have hjs : ∀ i, (C i).j ≫ (C i).s = c ≫ spMap (ω i) := fun i => by
    rw [Cpt.j, Category.assoc, pullback.condition, reassoc_of% (C i).jQ_over]
  have h1 := fun i => (hj i).1
  have h2 := fun i => (hj i).2.1
  have h3 := fun i => (hj i).2.2.1
  have h4 := fun i => (hj i).2.2.2
  obtain ⟨P, r, j, p, hr, hjr, hp⟩ := exists_join (c ≫ spMap β) X' s' hs' (fun i => (C i).j ≫ κ i)
    (fun i => by rw [Category.assoc, (hk i).w, reassoc_of% (hjs i), hωb])
  have hjp : ∀ i, j ≫ p i = (C i).j ≫ κ i := fun i => by simpa using (hp i).2.w.symm
  let jP : U ⟶ pullback r (spMap β) := pullback.lift j c hjr
  have hjP₁ : jP ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have hjP₂ : jP ≫ pullback.snd _ _ = c := pullback.lift_snd _ _ _
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U :=
    isNormalScheme_of_flat_preimmersion (C i₀).j (C i₀).normal
  have hjPo : IsOpenImmersion jP := by
    have G := (IsPullback.of_hasPullback (C i₀).s (spMap (ω i₀))).flip.paste_vert (hk i₀).flip
    rw [hωb] at G
    let ρ : pullback r (spMap β) ⟶ pullback (C i₀).s (spMap (ω i₀)) :=
      G.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p i₀)
        (by rw [Category.assoc, (hp i₀).1, pullback.condition])
    have hρ₁ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ := G.lift_fst _ _ _
    have hρ₂ : ρ ≫ pullback.fst _ _ ≫ κ i₀ = pullback.fst _ _ ≫ p i₀ := G.lift_snd _ _ _
    have A : IsPullback ρ (pullback.fst r (spMap β)) (pullback.fst _ _ ≫ κ i₀) (p i₀) := by
      refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := s' i₀) (v₁₃ := spMap β) ?_ hρ₂ G
      rw [hρ₁, (hp i₀).1]
      exact (IsPullback.of_hasPullback _ _).flip
    have B : IsPullback (𝟙 U) jP (C i₀).jQ ρ := by
      refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) (v₂₂ := pullback.fst _ _ ≫ κ i₀) (h₃₁ := p i₀)
        ?_ ?_ A
      · rw [hjP₁, ← Category.assoc]
        exact (hp i₀).2
      · refine G.hom_ext ?_ ?_
        · rw [Category.id_comp, Category.assoc, hρ₁, hjP₂, (C i₀).jQ_over]
        · rw [Category.id_comp, Category.assoc, hρ₂, reassoc_of% hjP₁, hjp, Cpt.j, Category.assoc]
    exact MorphismProperty.of_isPullback B (C i₀).jQ_open
  obtain ⟨Y, π, jQ, -, hY, hproj, hflat, hq₁, hq₂, hqo, hqd, hqr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O F P U r c j jP.opensRange jP.isoOpensRange.hom hr hU inferInstance
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₁)
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₂)
  let f : ∀ i, pullback (π ≫ r) (spMap (b i)) ⟶ (C i).X := fun i =>
    (hk i).lift (pullback.fst _ _ ≫ π ≫ p i) (pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, (hp i).1, pullback.condition])
  have hf : ∀ i, f i ≫ κ i = pullback.fst _ _ ≫ π ≫ p i := fun i => (hk i).lift_fst _ _ _
  refine ⟨Y, π ≫ r, jQ, f, hY, hproj, hflat, hq₁, hqo, hqd, fun i => ⟨(hk i).lift_snd _ _ _, ?_, ?_⟩⟩
  · intro g hg
    have hq₂' : jQ ≫ pullback.fst (π ≫ r) (spMap β) ≫ π = j := hq₂
    rw [← cancel_mono (κ i), Category.assoc, hf, reassoc_of% hg, reassoc_of% hq₂', hjp]
  · rintro x ⟨y, hy⟩
    have e1 : p i (π (pullback.fst (π ≫ r) (spMap (b i)) x)) = ((C i).j ≫ κ i) y := by
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply (f i), hf]
      simp only [Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hp i).2 y _ e1.symm
    obtain ⟨w, hw⟩ : pullback.fst (π ≫ r) (spMap (b i)) x ∈ Set.range (pullback.fst (π ≫ r) (spMap β)) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨c z, ?_⟩
      rw [Scheme.Hom.comp_apply π r, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjr]
    obtain ⟨v, hv⟩ := (hqr w).mpr ⟨jP.isoOpensRange.hom z, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact (congrArg (fun m : U ⟶ P => m z) hjP₁).trans (hz.trans (congrArg π hw.symm))⟩
    exact ⟨v, by rw [Scheme.Hom.comp_apply, ← hw]; exact congrArg _ hv⟩

end GlobalTheory.JoinModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelChangeLiftKeepingEtaA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem GlobalTheory.LiftAut.exists_lift_keeping_etaA :
    Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → l₁.A.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k) → r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → ∃ (r₁ : (Xo l₁).X ≅ (Xo l₁).X) (ν₁ : SABMap (Xo l₁).univ.t (Xo l₁).univ.t r₁.hom), r₁.hom ≫ (Xo l₁).s = (Xo l₁).s ∧ r₁.hom ≫ r = r ≫ r₀.hom ∧ ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ ∧ ∀ x, ((Xo l₁).univ.etaA x).left ≫ ν₁.φ = r₁.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LiftAut.lift_of_unique_of_similitude GlobalTheory.LevUniq.map_to_univ_unique GlobalTheory.exists_sim_of_aut_mod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → Geo.Tor.IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C b k r hr ν _ hD hβ hN hfin
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hD
  let _ := β'.toAlgebra
  have hsq : spMap β' ≫ spMap b = spMap k ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hβ]
  have hjs : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hopen := C.jQ_open
  let s₁ := pullback.snd C.s (spMap b)
  let q : pullback s₁ (spMap β') ⟶ pullback C.s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
        Category.assoc])
  have q₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have q₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd s₁ (spMap β')) (pullback.snd C.s (spMap β)) (spMap k) := by
    refine IsPullback.of_right ?_ q₂ (IsPullback.of_hasPullback C.s (spMap β))
    rw [q₁, ← hsq]
    exact (IsPullback.of_hasPullback s₁ (spMap β')).paste_horiz (IsPullback.of_hasPullback C.s (spMap b))
  let f : U' ⟶ pullback C.s (spMap b) := pullback.lift (r ≫ C.j) (c' ≫ spMap β') (by
    rw [Category.assoc, hjs, ← Category.assoc, hr, Category.assoc, Category.assoc, hsq])
  have f₁ : f ≫ pullback.fst _ _ = r ≫ C.j := pullback.lift_fst _ _ _
  let u : U' ⟶ pullback s₁ (spMap β') := pullback.lift f c' (pullback.lift_snd _ _ _)
  have u₁ : u ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have u₂ : u ≫ pullback.snd _ _ = c' := pullback.lift_snd _ _ _
  have hu : r ≫ C.jQ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, q₁, ← Category.assoc u, u₁, f₁, Cpt.j]
    · rw [Category.assoc, Category.assoc, q₂, ← Category.assoc u, u₂, C.jQ_over, hr]
  let g := pullback.snd C.jQ q
  let v : U' ⟶ pullback C.jQ q := pullback.lift r u hu
  have v₁ : v ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have v₂ : v ≫ g = u := pullback.lift_snd _ _ _
  have hp : IsPullback (pullback.fst C.jQ q) (g ≫ pullback.snd _ _) c (spMap k) := by
    have := (IsPullback.of_hasPullback C.jQ q).paste_vert hq
    rwa [C.jQ_over] at this
  have hv : IsFinite v := by
    have e : v = pullback.lift r c' hr ≫ hp.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · rw [Category.assoc, hp.isoPullback_hom_fst, v₁, pullback.lift_fst]
      · rw [Category.assoc, hp.isoPullback_hom_snd, ← Category.assoc, v₂, u₂, pullback.lift_snd]
    rw [e]; infer_instance
  have hW : (v ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = u := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, v₂]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O' F' _ U' s₁ c' f g.opensRange (v ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b C.proj) hN inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₁)
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₂)
  obtain ⟨pp, cub, sym, adj, prim, mu, hmu⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst C.s (spMap b)) C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b) =
      r ≫ C.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ f₁
    rw [← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap t' C.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b)),
      n'.φ = ν.φ ≫ C.m.φ := by
    rw [hj]; exact ⟨n, hn⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) ∈ abLocus C.t.G := by
    intro p
    have e : pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) = pullback.fst C.s (spMap β) (q p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q₁]
    rw [e]
    change p ∈ Set.range (pullback.snd C.jQ q) ↔ q p ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G
    rw [C.ab_gen, Scheme.Pullback.range_snd]
    rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩,
    ⟨⟨π ≫ pullback.fst _ _, ?_, ?_, mu, hj, hm.symm.trans hn'⟩⟩⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne C.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β') ⟶ pullback s₁ (spMap β') :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β') (w y) = π (pullback.fst (π ≫ s₁) (spMap β') y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst C.s (spMap b) z ∈ abLocus C.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.TripleCompare

section Cech

variable {X Y Z : Scheme.{0}}

theorem gen_refine {A B : LB Y} (n : ℤ) (σ : B.ι → A.ι) (hle : ∀ i, B.U i ≤ A.U (σ i))
    (hg : ∀ i j, B.g i j = res (inf_le_inf (hle i) (hle j)) (A.g (σ i) (σ j)) ^ n)
    (h : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen B, t.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun i => res (hle i) (t.s (σ i)) ^ n⟩, fun i j => ?_⟩
  have e := congrArg (res (inf_le_inf (hle i) (hle j))) (ht (σ i) (σ j))
  rw [map_mul, DVR.res_res', DVR.res_res'] at e
  rw [hg, map_zpow, map_zpow, DVR.res_res', DVR.res_res', ← mul_zpow]
  exact congrArg (· ^ n) e

theorem div_g_res (M L : LB Y) (p q : M.ι × L.ι) {V : Y.Opens}
    (h : V ≤ (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) (h₁ : V ≤ M.U p.1 ⊓ M.U q.1)
    (h₂ : V ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div M L).g p q) = res h₁ (M.g p.1 q.1) * (res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (DVR.res_res' _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (DVR.res_res' _ _ _))))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sum_g_res (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K' ⊕ K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L (Sum.elim φ' φ) j ⊓ LB.wchart L (Sum.elim φ' φ) j')
    (h₁ : V ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl))
    (h₂ : V ≤ LB.wchart L φ (j ∘ Sum.inr) ⊓ LB.wchart L φ (j' ∘ Sum.inr)) :
    res h ((LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)).g j j') =
      res h₁ ((LB.LinComb L φ' ε').g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        (res h₂ ((LB.LinComb L φ ε).g (j ∘ Sum.inr) (j' ∘ Sum.inr)))⁻¹ := by
  rw [DVR.linComb_g_res, DVR.linComb_g_res, DVR.linComb_g_res, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp]

theorem wchart_sum (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j =
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := by
  refine le_antisymm (fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩) fun y hy => ?_
  refine Set.mem_iInter.2 fun k => ?_
  rcases k with k | k
  · exact Set.mem_iInter.1 hy.1 k
  · exact Set.mem_iInter.1 hy.2 k

theorem lbIso_iff_gen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    Geo.Tor.LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  constructor
  · refine gen_refine (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun j => (j ∘ Sum.inl, j ∘ Sum.inr)) (fun j => (wchart_sum φ φ' j).le) fun j j' => ?_
    have a := (wchart_sum φ φ' j).le
    have b := (wchart_sum φ φ' j').le
    refine (DVR.res_refl' _).symm.trans ((sum_g_res φ ε φ' ε' j j' le_rfl
      (inf_le_inf (a.trans inf_le_left) (b.trans inf_le_left))
      (inf_le_inf (a.trans inf_le_right) (b.trans inf_le_right))).trans (Eq.symm ?_))
    exact (zpow_one _).trans (div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) _ _ _ _ _)
  · refine gen_refine (B := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun p => Sum.elim p.1 p.2) (fun p => (wchart_sum φ φ' (Sum.elim p.1 p.2)).ge) fun p q => ?_
    refine (DVR.res_refl' _).symm.trans ((div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    exact (zpow_one _).trans (sum_g_res φ ε φ' ε' (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) _ _ _)

theorem wchart_id (L : LB X) (j : PUnit.{1} → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j = L.U (j ⟨⟩) :=
  le_antisymm (fun _ hy => Set.mem_iInter.1 hy PUnit.unit) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_id_g_res (L : LB X) (j j' : PUnit.{1} → L.ι) {V : X.Opens}
    (h : V ≤ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j ⊓ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j')
    (h' : V ≤ L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩)) :
    res h ((L.pull (𝟙 X)).g j j') = res h' (L.g (j ⟨⟩) (j' ⟨⟩)) := by
  rw [DVR.linComb_g_res, Fintype.prod_unique, zpow_one, DVR.tr_def L (ψ := 𝟙 X) h']
  exact DVR.pullU_of_eq_id _ rfl _ _ _ _ _

theorem lbIso_iff_pull_id (L M : LB X) :
    Geo.Tor.LBIso L M ↔ Geo.Tor.LBIso M (L.pull (𝟙 X)) := by
  constructor
  · refine gen_refine (A := LB.div M L) (B := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (p.2, p.1 ⟨⟩))
      (fun p => le_inf inf_le_right (inf_le_left.trans (wchart_id L p.1).le)) fun p q => ?_
    have a := (wchart_id L p.1).le
    have b := (wchart_id L q.1).le
    refine (DVR.res_refl' _).symm.trans ((div_g_res (L.pull (𝟙 X)) M p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res M L (p.2, p.1 ⟨⟩) (q.2, q.1 ⟨⟩) _
      (inf_le_inf inf_le_right inf_le_right)
      (inf_le_inf (inf_le_left.trans a) (inf_le_left.trans b)))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) ((inv_inv _).trans ?_) rfl)
    exact (pull_id_g_res L p.1 q.1 _ _).symm
  · refine gen_refine (B := LB.div M L) (A := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (fun _ => p.2, p.1))
      (fun p => le_inf (inf_le_right.trans (wchart_id L fun _ => p.2).ge) inf_le_left) fun p q => ?_
    have a := (wchart_id L fun _ => p.2).ge
    have b := (wchart_id L fun _ => q.2).ge
    refine (DVR.res_refl' _).symm.trans ((div_g_res M L p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res (L.pull (𝟙 X)) M (fun _ => p.2, p.1)
      (fun _ => q.2, q.1) _ (inf_le_inf (inf_le_right.trans a) (inf_le_right.trans b))
      (inf_le_inf inf_le_left inf_le_left))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) (inv_inv _) (congrArg (·⁻¹) ?_))
    exact pull_id_g_res L (fun _ => p.2) (fun _ => q.2) _ _

end Cech

section Clauses

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

end Clauses

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
  {S S' : Scheme.{0}}

end Triples

end GlobalTheory.TripleCompare
end
end

