module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeZeroCurvePositive
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurvePositivity

theorem change_gen {Ω : Type} [Field Ω] (σ π e f : Ω) (M : ℕ) (hf : f ≠ 0) :
    π / (σ / e) ^ M = π / (σ / f) ^ M * (e / f) ^ M := by
  have hfM : f ^ M ≠ 0 := pow_ne_zero _ hf
  rw [div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
  by_cases hσ : σ ^ M = 0
  · simp [hσ]
  · field_simp

theorem val_one {K : Type} [Field K] (C : Crv.ACurve K) (hw : ∀ i, 0 < C.w i) (c : K) (hc : c ≠ 0)
    (r t : C.I → K) (M : ℕ) (hr : ∀ i, r i ≠ 0) (hfin : {i | C.v i (r i) ≠ 1}.Finite)
    (hd : ∑ᶠ i, (C.w i : ℤ) * (-WithZero.log (C.v i (r i))) = 0)
    (ht : ∀ i, C.v i (t i) ≤ 1) (hct : ∀ i, c = t i * r i ^ M) (i : C.I) : C.v i (t i) = 1 := by
  have ht0 : ∀ j, t j ≠ 0 := fun j h => hc (by rw [hct j, h, zero_mul])
  have hvt : ∀ j, C.v j (t j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (ht0 j)
  have hvr : ∀ j, C.v j (r j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (hr j)
  have hL : ∀ j, WithZero.log (C.v j c) =
      WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j)) := by
    intro j
    rw [hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]
    simp
  have hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0 := by
    intro j
    have := (WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)
    rwa [WithZero.log_one] at this
  set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA
  set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB
  set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD
  have hsB : (Function.support B).Finite := (C.fin c hc).subset (fun j hj => by
    simp only [Function.mem_support, hB] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, mul_zero])
  have hsD : (Function.support D).Finite := hfin.subset (fun j hj => by
    simp only [Function.mem_support, hD] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, neg_zero, mul_zero])
  have hABD : A = fun j => B j + (M : ℤ) * D j := by
    funext j; simp only [hA, hB, hD]; rw [hL j]; ring
  have hsMD : (Function.support fun j => (M : ℤ) * D j).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsA : (Function.support A).Finite := by
    rw [hABD]; exact (hsB.union hsMD).subset (Function.support_add _ _)
  have hsum : ∑ᶠ j, A j = 0 := by
    rw [hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]
    simp only [hB, hD]
    rw [C.prod c hc, hd, mul_zero, add_zero]
  have hnn : ∀ j, 0 ≤ -A j := fun j => by
    simp only [hA]; have := hle j; have := hw j; nlinarith
  have hsA' : (Function.support fun j => -A j).Finite :=
    hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)
  have h1 := single_le_finsum i hsA' hnn
  rw [finsum_neg_distrib, hsum, neg_zero] at h1
  have h2 : WithZero.log (C.v i (t i)) = 0 := by
    have h3 : A i = 0 := by have := hnn i; linarith
    simp only [hA] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (by have := hw i; omega)
    · exact h4
  rw [← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]

end PositivityTheory.Xgn.CurvePositivity

theorem PositivityTheory.Xgn.degree_zero_curve_positive : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (L : Lat ξ Ω) (σ π : Ω) (M : ℕ) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → L.IsVB 1 ⊤ → 0 < M → Γ.HasDeg L 0 → (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → π / (σ / e) ^ M ∈ regAt ξ p) → (∀ e, L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e → unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ (π / (σ / e) ^ M)) → ∀ (i : Γ.C.I) (h : genPt ξ ⤳ centre (Γ.z i)) (e : Ω), L.IsGenAt ⟨centre (Γ.z i), h⟩ e → unitAt ξ ⟨centre (Γ.z i), h⟩ (π / (σ / e) ^ M) := by
  intro X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he
  obtain ⟨e0, f, r, he0, hf, hr, hfin, hd⟩ := hdeg
  have hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j) := fun j => (hf j).2
  obtain ⟨c, hc⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)
  choose g hg using fun j => hreg _ _ (hf' j)
  let t : ∀ j, (Γ.C.v j).valuationSubring := fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)
  have hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j) := fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩
  have hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ) := fun j =>
    ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)
  have hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M := fun j => by
    have h2 := CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)
    rw [← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1] at h2
    exact CoordModel.valAt_unique hξ hc h2
  have hv := PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M
    (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i
  have ht0 : (t i : Γ.κ) ≠ 0 := fun h0 => by simp [h0] at hv
  have hu : IsUnit (t i) := by
    refine IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
    change Γ.C.v i _ ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hgu : IsUnit (g i) := (Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu
  obtain ⟨u, hu1, hu2⟩ := (CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))
  refine (CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩
  rw [PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]
  exact congrArg (· * (e / f i) ^ M) (hg i)
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveInFibreDegree
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurveInFibre

theorem valAt_inv {X : Scheme.{0}} {Ω K : Type} [Field Ω] [Field K] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {η : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (h : ValAt ξ η a r) (hr : r ≠ 0) :
    ValAt ξ η a⁻¹ r⁻¹ := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hl := Scheme.isLocalHom_stalkClosedPointTo η
  have hs : IsUnit s := hl.map_nonunit s (IsUnit.mk0 _ hr)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · exact map_units_inv _ u
  · exact map_units_inv _ u

theorem finite_not_integral {K O A : Type} [Field K] [CommRing O] [CommRing A] (C : Crv.ACurve K) (g : O →+* A)
    (hg : g.FiniteType) (φ : A →+* K) (hO : ∀ i a, φ (g a) ∈ (C.v i).valuationSubring) :
    {i | ¬ ∀ a, φ a ∈ (C.v i).valuationSubring}.Finite := by
  let := g.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O A from hg).out
  have hfin : ∀ a : A, {i | φ a ∉ (C.v i).valuationSubring}.Finite := by
    intro a
    by_cases h0 : φ a = 0
    · simp [h0]
    · exact (C.fin _ h0).subset fun i hi h1 => hi (le_of_eq h1)
  refine (t.finite_toSet.biUnion fun a _ => hfin a).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hc
  refine hi fun a => ?_
  have ha : a ∈ Algebra.adjoin O (t : Set A) := ht ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact hc y hy
  | algebraMap r => exact hO i r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem ae_centre {X : Scheme.{0}} {K O : Type} [Field K] [CommRing O] (s : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated s] [LocallyOfFiniteType s] (C : Crv.ACurve K) (η : Spec (CommRingCat.of K) ⟶ X)
    (z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X)
    (hz : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η)
    (U : X.Opens) (hU : centre η ∈ U) : {i | centre (z i) ∉ U}.Finite := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hU
  have hV : IsAffineOpen V := hV
  have hr : Set.range η ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hxV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec η hr)
  have hφ' : Spec.map φ ≫ hV.fromSpec = η := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨g, hg⟩ := Spec.map_surjective (hV.fromSpec ≫ s)
  have hgf : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 (hg ▸ inferInstance)
  choose ψ hψ using fun i => Spec.map_surjective (z i ≫ s)
  have hsq : ∀ i, ψ i ≫ CommRingCat.ofHom (C.v i).valuationSubring.subtype = g ≫ φ := fun i => by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, hg, ← Category.assoc, ← Category.assoc, hz, hφ']
  have hsq' : ∀ i a, φ.hom (g.hom a) = ((ψ i).hom a : K) := fun i a =>
    (congrArg (fun f => f.hom a) (hsq i)).symm
  refine (finite_not_integral C g.hom hgf φ.hom fun i a => ?_).subset fun i hi hc => hi ?_
  · rw [hsq' i a]
    exact ((ψ i).hom a).2
  · let χ : Γ(X, V) ⟶ CommRingCat.of (C.v i).valuationSubring :=
      CommRingCat.ofHom (φ.hom.codRestrict (C.v i).valuationSubring hc)
    have : IsDominant (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) :=
      ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (C.v i).valuationSubring.subtype).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
        exact bot_le)⟩
    have e : z i = Spec.map χ ≫ hV.fromSpec := by
      refine ext_of_isDominant_of_isSeparated s ?_
        (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) ?_
      · rw [Category.assoc, ← hg, ← hψ, ← Spec.map_comp]
        congr 1
        ext a
        exact (hsq' i a).symm
      · rw [hz, ← Category.assoc, ← Spec.map_comp, ← hφ']
        rfl
    refine hVU ?_
    change centre (z i) ∈ (V : Set X)
    rw [e, ← hV.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end PositivityTheory.Xgn.CurveInFibre

theorem PositivityTheory.Xgn.exists_curve_in_fibre_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  intro X Ω _ ξ O _ s _ _ ϖ Γ _
  refine ⟨⟨Γ.z, Γ.z_gen, PositivityTheory.Xgn.CurveInFibre.ae_centre s Γ.C Γ.η Γ.z Γ.z_gen⟩, rfl, fun L n _ => ⟨?_, ?_⟩⟩
  · rintro ⟨e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨Γ.η_spec, Γ.z_spec, e, f, fun i => (r i)⁻¹, he, fun i => (hf i).2, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩,
      ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [← hd]
      simp
  · rintro ⟨h₀, h, e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨e, f, fun i => (r i)⁻¹, he, fun i => ⟨h i, hf i⟩, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩, ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [hd]
      simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeProperPushdown
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticePushdown

theorem exists_lift {X X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (f : X' ⟶ X) [IsProper f] (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V Ω']
    [IsFractionRing V Ω'] (z : Spec (CommRingCat.of V) ⟶ X)
    (w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ z) :
    ∃ p' : Cpt ξ', f p'.1 = z (IsLocalRing.closedPoint V) ∧
      ∀ a ∈ regAt ξ' p', ∃ v : V, algebraMap V Ω' v = a := by
  have hex : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X',
      Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ l = ξ' ∧ l ≫ f = z := by
    obtain ⟨l, hl₁, hl₂⟩ := (hex { R := V, K := Ω', commSq := ⟨w⟩, .. }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  have hsp : genPt ξ' ⤳ l (IsLocalRing.closedPoint V) := by
    unfold genPt
    rw [← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have key : X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ' =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω') := by
    apply Spec.map_injective
    rw [← cancel_mono (X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))]
    have h1 : Spec.map (X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ') ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      refine Eq.trans (congrArg (· ≫ X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))
        (Spec.map_comp (X'.presheaf.stalkSpecializes hsp) (Scheme.stalkClosedPointTo ξ'))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ') ≫ ·)
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)) ?_
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
    have h2 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω')) ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      rw [Spec.map_comp, Category.assoc]
      refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk l)) hl₁
    exact h1.trans h2.symm
  refine ⟨⟨_, hsp⟩, ?_, ?_⟩
  · rw [← hl₂]
    exact (Scheme.Hom.comp_apply l f _).symm
  · rintro _ ⟨g, rfl⟩
    exact ⟨(Scheme.stalkClosedPointTo l).hom g, (congrArg (fun t => t.hom g) key).symm⟩

theorem spec_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) :
    Spec.map (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk q.1 = ξ := by
  refine Eq.trans (congrArg (· ≫ X.fromSpecStalk q.1)
    (Spec.map_comp (X.presheaf.stalkSpecializes q.2) (Scheme.stalkClosedPointTo ξ))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2)) ?_
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem exists_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    [IsLocallyNoetherian X] {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {f : X' ⟶ X} {i : Ω →+* Ω'} [IsProper f] (hD : Dominates ξ' ξ f i) (hi : Function.Bijective i)
    (hg : IsCptGen ξ) (hn : NormalCpt ξ) (q : Cpt ξ) (hd : ringKrullDim (X.presheaf.stalk q.1) = 1) :
    ∃ p' : Cpt ξ', f p'.1 = q.1 ∧ ∀ a : Ω, i a ∈ regAt ξ' p' → a ∈ regAt ξ q := by
  obtain ⟨hfr, -, -⟩ := RegAtRing.regAt_ring X Ω ξ hg q
  have : IsFractionRing (regAt ξ q) Ω := hfr
  have : IsIntegrallyClosed (regAt ξ q) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn q x hx⟩, rfl⟩
  have hdom : IsDomain (X.presheaf.stalk q.1) := (hg.inj q).isDomain (genMap ξ q)
  have : IsIntegrallyClosed (X.presheaf.stalk q.1) :=
    IsIntegrallyClosed.of_equiv (RegAtRing.stalkEquiv hg q).symm
  have : IsDiscreteValuationRing (X.presheaf.stalk q.1) := normal_noeth_local_dim_one_isDVR _ hd
  let _ : Algebra (X.presheaf.stalk q.1) Ω' := (i.comp (genMap ξ q)).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hi.1.comp (hg.inj q))
  have hfr' : IsFractionRing (X.presheaf.stalk q.1) Ω' := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨y, rfl⟩ := hi.2 z
    obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, rfl⟩ := RegAtRing.exists_div hg q y
    exact ⟨a, b, map_div₀ i _ _⟩
  have w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω')) ≫
      X.fromSpecStalk q.1 := by
    have e : CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω') =
        (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ CommRingCat.ofHom i := rfl
    refine hD.trans ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (spec_genMap ξ q).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ X.fromSpecStalk q.1) (Spec.map_comp _ _).symm
  have hv : ValuationRing (X.presheaf.stalk q.1) := inferInstance
  obtain ⟨p', h1, h2⟩ := @exists_lift X X' Ω' _ ξ' f _ (X.presheaf.stalk q.1) _ hdom hv _ hfr'
    (X.fromSpecStalk q.1) w
  refine ⟨p', h1.trans Scheme.fromSpecStalk_closedPoint, fun a ha => ?_⟩
  obtain ⟨v, hv⟩ := h2 _ ha
  exact ⟨v, hi.1 hv⟩

end PositivityTheory.Xgn.LineLatticePushdown

theorem PositivityTheory.Xgn.line_lattice_proper_pushdown : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  intro X Ω _ ξ _ X' Ω' _ ξ' f i _ hD hi hg hn L T p t hL hT hp
  have ht : t ≠ 0 := by
    have h0 := (hp ⟨genPt ξ', specializes_rfl⟩ (by
      show f (genPt ξ') ⤳ p.1
      rw [hD.map_genPt]; exact p.2)).1
    rintro rfl
    exact h0 (map_zero i)
  refine PositivityTheory.Xgn.line_lattice_generator_codim_one X Ω ξ hg hn L T p t hL hT ht fun q hqp hd => ?_
  obtain ⟨p', hq, hreg⟩ := PositivityTheory.Xgn.LineLatticePushdown.exists_over hD hi hg hn q hd
  obtain ⟨q, hq0⟩ := q
  obtain rfl : f p'.1 = q := hq
  obtain ⟨U, hU, b, -, h⟩ := hL _ (hT _ hqp)
  obtain ⟨h1, h2⟩ := h _ (hT _ hqp) hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  rw [hr] at h2
  have he : b 0 ≠ 0 := h1.ne_zero 0
  obtain ⟨_, -, hpull⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  have g1 := hpull L (b 0) ⟨he, h2⟩
  have g2 := hp p' hqp
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq g2.1 (g2.2.symm.trans g1.2)
  have hu' : u = i (t / b 0) := by
    rw [map_div₀, e, smul_eq_mul, mul_div_cancel_right₀ _ g1.1]
  subst hu'
  have hu2 : unitAt ξ ⟨f p'.1, hq0⟩ (t / b 0) :=
    ⟨div_ne_zero ht he, hreg _ hu.2.1, hreg _ (by rw [map_inv₀]; exact hu.2.2)⟩
  refine ⟨ht, h2.trans (span_singleton_eq_of_unitAt hu2 ?_).symm⟩
  rw [smul_eq_mul, div_mul_cancel₀ _ he]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_pull_exists
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_exists
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)
open PositivityTheory.Xgn.A_pull_line (comb mseg_join map_mem)
open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC (smul_mem_spanOver mem_spanOver_of_mem locFree_baseChange)

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} (x : (Σ k, ι k) → Ω) (s t : ∀ k, ι k) (hs : mseg x s ≠ 0) (a : Ω)
    (ha : a ∈ chartRing O (mseg x) s) :
    ∃ n : ℕ, (mseg x s / mseg x t) ^ n * a ∈ chartRing O (mseg x) t := by
  have hq := div_mem_chartRing (o := O) (mseg x) t s
  unfold chartRing at ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have h : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
      rw [pow_one, mul_comm, div_mul_div_cancel₀ hs]
    have h2 := div_mem_chartRing (o := O) (mseg x) t u
    rw [← h] at h2
    exact h2
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a + b) =
        (mseg x s / mseg x t) ^ n * ((mseg x s / mseg x t) ^ m * a) +
        (mseg x s / mseg x t) ^ m * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact add_mem (mul_mem (pow_mem hq n) hm) (mul_mem (pow_mem hq m) hn)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a * b) =
        ((mseg x s / mseg x t) ^ m * a) * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact mul_mem hm hn

theorem closure_eq {O Ω₁ V V₁ : Type} [CommRing O] [Field Ω₁] [Algebra O Ω₁] [AddCommGroup V₁]
    [Module Ω₁ V₁] (R : Subalgebra O Ω₁) (f : V → V₁) (L : Set V) :
    spanOver R (f '' L) = AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • f e} := by
  unfold spanOver
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

theorem main (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type)
    [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V)
    (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type)
    [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁)
    (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, ∀ s, mseg (bcCoord x z) s ≠ 0 →
      EB.lat s = AddSubgroup.closure
        {v | ∃ a ∈ chartRing O (mseg (bcCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • bc e} := by
  let φ : Ω →ₐ[O] Ω₁ := IsScalarTower.toAlgHom O Ω Ω₁
  obtain ⟨hfam, hloc⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  have hj : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) :=
    fun s => mseg_join φ x z s
  have hne : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s ≠ 0 →
      mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    rw [hj, h, map_zero, zero_mul] at hs
    exact hs rfl
  suffices hov : IsLatFamily O (bcCoord x z) (fun s =>
      spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))) by
    obtain ⟨EB, hEB⟩ :=
      (PositivityTheory.Xgn.t_bundle_of_family O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1 _ hov
        (fun s hs => locFree_baseChange _ _ (fun a ha => map_mem φ x z s hs a ha) bc hbc N _
          (hloc _ (hne s hs)))
    exact ⟨EB, fun s hs => (hEB s hs).trans (closure_eq _ _ _)⟩
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, ?_⟩
  intro s t hs ht v hv
  beta_reduce at hv ⊢
  have hq := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t s
  set q := mseg (bcCoord x z) s / mseg (bcCoord x z) t with hqdef
  rw [spanOver] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
    obtain ⟨n, hn⟩ := pow_mul_mem (bcCoord x z) s t hs a ha
    obtain ⟨m, hm⟩ := hfam.2 _ _ (hne s hs) (hne t ht) e he
    have hw := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (comb (restrictChart t) s)
    set w := mseg (bcCoord x z) (comb (restrictChart t) s) / mseg (bcCoord x z) t with hwdef
    have ht' : algebraMap Ω Ω₁ (mseg x (restrictChart t)) ≠ 0 := (map_ne_zero _).mpr (hne t ht)
    have hqw : q = w * algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) := by
      have h1 : mseg (bcCoord x z) (comb (restrictChart t) s) =
          algebraMap Ω Ω₁ (mseg x (restrictChart t)) * mseg z (fun k => s (.inr k)) := hj _
      rw [hqdef, hwdef, h1, hj s, map_div₀]
      field_simp
    refine ⟨n + m, ?_⟩
    have h : q ^ (n + m) • a • bc e = (q ^ n * a * w ^ m) •
        bc ((mseg x (restrictChart s) / mseg x (restrictChart t)) ^ m • e) := by
      rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m : Ω), smul_smul, smul_smul, map_pow, pow_add,
        mul_assoc (q ^ n * a), ← mul_pow, ← hqw]
      congr 1
      ring
    rw [h]
    exact smul_mem_spanOver _ _ (mul_mem hn (pow_mem hw m)) (mem_spanOver_of_mem _ ⟨_, hm, rfl⟩)
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : q ^ (m + n) • (a + b) = q ^ n • q ^ m • a + q ^ m • q ^ n • b := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [h]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hq n) hm) (smul_mem_spanOver _ _ (pow_mem hq m) hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

end PositivityTheory.Xgn.A_pull_exists

theorem PositivityTheory.Xgn.t_pull_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_, fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc =>
    PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω₁ K' ι' z V₁ bc hbc⟩
  exact PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω K' ι' z V (LinearEquiv.refl Ω V).toLinearMap
    (IsBaseChange.ofEquiv _)
end

