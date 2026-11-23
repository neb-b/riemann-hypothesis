module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_expandsF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  intro R _ _ I hI hC D A G _ _ U hG F _ _ _ N hN w₀ hw₀ lab hlab
  haveI := hC
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have gf : GlobalFnsSt := hL.1.globalFns
  have hN1 : 1 ≤ N := hN.pos
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F N hN1 w₀ hw₀
  choose E hE using fun s => (b₂ s).exists
  obtain ⟨f, hf, hfN⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN1
  have hlabf : ∀ p, lab p = f p := fun p => (hf.1 p (lab p)).1 (hlab p)
  have hSF := GlobalTheory.SymFrameClause.symFrame_clause R I hI D A G hG U F N hN
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hE⟩
  · refine ⟨fun s s' h => ?_, fun t => ?_⟩
    · have h1 := hE s
      rw [h] at h1
      exact (b₁ (E s')).unique h1 (hE s')
    · obtain ⟨s, hs, -⟩ := b₁ t
      exact ⟨s, (b₂ s).unique (hE s) hs⟩
  · intro s s' s'' h j
    have hT := hlin F N w₀ (E s) (E s') (SecOps.secAdd (E s) (E s')) s s' 1 (hE s) (hE s') (fun j => by
      simp [SecOps.secAdd, liftFun])
    have e : (1 : F) • s + s' = s'' := fam_ext fun α j => by rw [h]; simp
    rw [e] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ s'').unique (hE s'') hT)
  · intro c s s' hs j
    obtain rfl := (isSmul_iff c s s').1 hs
    obtain ⟨z, hz, -⟩ := b₁ SecOps.secZero
    have hz0 : z = 0 := by
      have h2 := hlin F N w₀ _ _ SecOps.secZero z z 1 hz hz (fun j => by simp [SecOps.secZero])
      have h3 := (b₁ _).unique hz h2
      rw [one_smul] at h3
      exact left_eq_add.1 h3
    have hT := hlin F N w₀ (E s) SecOps.secZero
      (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F c)) (E s)) s z c (hE s) hz (fun j => by
        show _ = _ + 0
        rw [add_zero]
        rfl)
    rw [hz0, add_zero] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ _).unique (hE _) hT)
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hf.2.1 x hx
      exact ⟨p, (hlabf p).trans hp⟩
    · rintro ⟨p, rfl⟩
      rw [hlabf]
      exact hfN p
  · intro p
    exact (hSF p).1.1
  · intro p
    exact ((hSF p).2 (lab p) (hlab p)).1
  · intro p w θ s s' hw hθ hrel
    obtain ⟨t', ht'⟩ := GlobalTheory.RootShift.exists_isActOf A.isLB θ (E s)
    obtain ⟨s'', hs'', -⟩ := b₁ t'
    have h1 := ((hSF p).2 (lab p) (hlab p)).2 θ hθ w₀ hw₀ w hw (E s) t' s s'' (hE s) hs'' ht'
    obtain rfl := GlobalTheory.ThetaTranslate.phiRel_unique gf p hw.1 hrel h1
    have e := (b₂ s').unique (hE s') hs''
    rw [← e] at ht'
    exact ht'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantLift_functional_quotient_projective : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  first | exact @GlobalTheory.eqLift_tensorModOf | exact GlobalTheory.eqLift_tensorModOf | (intros; apply GlobalTheory.eqLift_tensorModOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOne
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem exists_faithfullyFlat_algHom : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    Algebra.IsIntegral R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    (∃ s : C →+* FractionRing A, s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O), Module.FaithfullyFlat R O ∧ Nonempty (C →ₐ[R] O) := by
  intro A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hint hEt hs
  obtain ⟨s, hs⟩ := hs
  have ht0 : ρ t = 0 := RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self t)
  have htm : t ∈ maximalIdeal R := by
    by_contra h
    have hu : IsUnit (ρ t) := ((IsLocalRing.notMem_maximalIdeal.1 h)).map ρ
    rw [ht0] at hu
    exact not_isUnit_zero hu
  obtain ⟨g, -, hg⟩ := exists_integral_point A R C ρ hint s hs
  choose f hf using GlobalTheory.T.exists_algHom_quotient_pow_lifting_point A R C ρ hρ t hker ht hEt g hg
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)).comp (f n) = f m := by
    intro m n hle
    refine GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow A R C ρ hρ t hker ht hEt m _ _ fun c => ?_
    set φ := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)
    have h1 := hf n c
    have h2 := hf m c
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    have h1' := map_dvd φ h1
    have e1 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) t) = Ideal.Quotient.mk (Ideal.span {t} ^ m) t := rfl
    have e2 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c))) =
        Ideal.Quotient.mk (Ideal.span {t} ^ m) (algebraMap A R (g c)) := rfl
    rw [map_sub, e1, e2] at h1'
    have := dvd_sub h1' h2
    simpa using this
  exact ⟨AdicCompletion (Ideal.span {t}) R, inferInstance, inferInstance,
    faithfullyFlat_adicCompletion_span R t htm, ⟨AdicCompletion.liftAlgHom _ f compat⟩⟩

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_fibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  intro R _ _ _ _ D C W _ _ _ T F _ _ _ hF

  have hρ : Function.Injective ((algebraMap (FractionRing W) F).comp ((algebraMap W (FractionRing W)).comp T.φ)) :=
    (algebraMap (FractionRing W) F).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
  obtain ⟨ga, hga, hy⟩ := Modif.factor_gp R C.toModif F _ (jFK (R := W) F ≫ jK W ≫ T.ξ) hρ (by
    rw [Category.assoc, Category.assoc, T.ξ_π]
    simp only [jK, jFK, spMap, ← Spec.map_comp]
    rfl)
  have hga' : ga = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (hga r).trans (hF r).symm)
  subst hga'
  have hu : jFK (R := W) F ≫ jK W ≫ T.ξ = jFK (R := R) F ≫ C.gp := hy

  have s₁ : IsPullback (pullback.snd (jFK (R := W) F) T.A.A.hom) (pullback.fst (jFK (R := W) F) T.A.A.hom)
      T.A.A.hom (jFK (R := W) F) := (IsPullback.of_hasPullback _ _).flip
  haveI : IsIso T.U.gen.inv.left := ⟨⟨T.U.gen.hom.left, by rw [← Over.comp_left, T.U.gen.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, T.U.gen.hom_inv_id, Over.id_left]⟩⟩
  have s₂ : IsPullback T.U.gen.inv.left T.A.A.hom (pullback.snd T.G.hom (jK W)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w T.U.gen.inv⟩
  have s₃ : IsPullback (pullback.fst T.G.hom (jK W)) (pullback.snd T.G.hom (jK W)) T.G.hom (jK W) :=
    IsPullback.of_hasPullback _ _
  have hW : IsPullback ((pullback.snd (jFK (R := W) F) T.A.A.hom) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β)
      (pullback.fst (jFK (R := W) F) T.A.A.hom) C.G.hom (jFK (R := R) F ≫ C.gp) := by
    have := ((s₁.paste_horiz s₂).paste_horiz s₃).paste_horiz T.cart.1
    rw [← hu]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this

  have t₁ : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.A.A.hom (jFK (R := R) F) := (IsPullback.of_hasPullback _ _).flip
  have hR : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom ≫ C.α) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.G.hom (jFK (R := R) F ≫ C.gp) := t₁.paste_horiz C.α_cart.1
  refine ⟨(hW.isoIsPullback _ _ hR).hom, inferInstance, hW.isoIsPullback_hom_snd _ _ hR, ?_⟩
  exact hW.isoIsPullback_hom_fst _ _ hR

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineChartCoverOverModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finite_affine_chart_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  intro R _ _ M G hG L hL
  haveI := M.proper
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hx : ∀ x : G.left, ∃ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens),
      x ∈ W ∧ W ≤ L.U j ∧ W ≤ G.hom ⁻¹ᵁ U ∧ IsAffineOpen W ∧ IsAffineOpen U := by
    intro x
    have hxt : x ∈ (⊤ : G.left.Opens) := trivial
    rw [← hL.cover] at hxt
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxt
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.S.isBasis_affineOpens)
      (show G.hom x ∈ (⊤ : M.S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens)
      (show x ∈ L.U j ⊓ G.hom ⁻¹ᵁ U from ⟨hj, hxU⟩)
    exact ⟨j, W, U, hxW, hWle.trans inf_le_left, hWle.trans inf_le_right, hW, hU⟩
  choose j W U hxW hWj hWU hWa hUa using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set G.left)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  refine ⟨t.card, fun b => j (e.symm b), fun b => W (e.symm b), fun b => U (e.symm b), ?_,
    fun b => hWj _, fun b => hWU _, fun b => hWa _, fun b => hUa _⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨e ⟨y, hy⟩, by simpa using hxy⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FieldDesc
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_comp_proj {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  exact GlobalTheory.PullDegCompGen.exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)

theorem exists_finite_common_pull : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (E₁ E₂ : DegPre K) (E' : DegPre L), IsPullDeg β E₁ E' → IsPullDeg β E₂ E' → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (E₃ : DegPre K'), io.Finite ∧ Nonempty (IsPullDeg io E₁ E₃) ∧ Nonempty (IsPullDeg io E₂ E₃) := by
  intro K L _ _ _ β E₁ E₂ E' h₁ h₂
  haveI := h₁.e_hom
  haveI := h₂.e_hom
  obtain ⟨K', _, io, Ω, _, j, l, φ, hfin, hl, hφ, hcomp⟩ :=
    _root_.GlobalTheory.IsoFinExt.exists_finite_iso K L β E₁.P.A E₂.P.A E₁.P.isAb E₂.P.isAb (h₁.e.symm ≪≫ h₂.e) (by dsimp; infer_instance)
  have hP := GlobalTheory.polBaseChange_holds
  obtain ⟨E₃, h₃, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₁ ⊤ (FieldPull.nonempty_psiOn_field E₁) trivial
  obtain ⟨E₄, h₄, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₂ ⊤ (FieldPull.nonempty_psiOn_field E₂) trivial
  obtain ⟨E'', h', -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP L Ω j E' ⊤ (FieldPull.nonempty_psiOn_field E') trivial
  obtain ⟨c₁, pc₁⟩ : ∃ c : IsPullDeg (l.comp io) E₁ E'', proj c = proj h' ≫ proj h₁ := by
    rw [hl]; exact exists_comp_proj j.injective h₁ h'
  obtain ⟨c₂, pc₂⟩ : ∃ c : IsPullDeg (l.comp io) E₂ E'', proj c = proj h' ≫ proj h₂ := by
    rw [hl]; exact exists_comp_proj j.injective h₂ h'
  obtain ⟨g₃, pg₃⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₁ E₃ E'' h₃ c₁
  obtain ⟨g₄, pg₄⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₂ E₄ E'' h₄ c₂
  have w₁ : proj h' ≫ E'.P.A.hom = E''.P.A.hom ≫ spMap j := (pull_grp h').1.w
  have w₃ : proj g₃ ≫ E₃.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₃).1.w
  have w₄ : proj g₄ ≫ E₄.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₄).1.w
  have key : proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left = proj g₄ ≫ h₄.e.hom.left := by
    apply pullback.hom_ext
    · have := hcomp E''.P.A.left (proj h' ≫ h₁.e.hom.left) (proj g₃ ≫ h₃.e.hom.left) E''.P.A.hom
        (by simp only [Category.assoc]; exact (pc₁.symm.trans pg₃.symm))
        (by rw [Category.assoc]; exact (congrArg (proj h' ≫ ·) (Over.w h₁.e.hom)).trans w₁)
        (by rw [Category.assoc]; exact (congrArg (proj g₃ ≫ ·) (Over.w h₃.e.hom)).trans w₃)
      simp only [Category.assoc] at this ⊢
      rw [← this]
      have e₁ : h₁.e.hom.left ≫ (h₁.e.symm ≪≫ h₂.e).hom.left = h₂.e.hom.left := by
        rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
          Over.id_left, Category.id_comp]
      rw [reassoc_of% e₁]
      exact (pg₄.trans pc₂).symm
    · simp only [Category.assoc]
      have a := Over.w φ.hom
      have b := Over.w h₃.e.hom
      have c := Over.w h₄.e.hom
      erw [a, b, w₃, c, w₄]
  let Ψ : E₃.P.A ≅ E₄.P.A := h₃.e ≪≫ φ ≪≫ h₄.e.symm
  haveI := h₃.e_hom
  haveI := h₄.e_hom
  haveI := hφ
  have hΨ : IsMonHom Ψ.hom := by dsimp [Ψ]; infer_instance
  have cΨ : g₃.e.hom.left ≫ pullback.fst E₃.P.A.hom (specOf l) ≫ Ψ.hom.left =
      g₄.e.hom.left ≫ pullback.fst E₄.P.A.hom (specOf l) := by
    have k2 : (proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left) ≫ h₄.e.inv.left = proj g₄ := by
      rw [key, Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
    refine Eq.trans ?_ k2
    simp only [Ψ, Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc]
  obtain ⟨q⟩ := _root_.GlobalTheory.nonempty_isPullDeg_id_of_common_pull K' Ω l E₄ E₃ E'' g₄ g₃ Ψ hΨ cΨ
  have hh := nonempty_isPullDeg_comp_of_injective K K' K' io (RingHom.id K') E₂ E₄ E₃ (fun _ _ h => h) ⟨h₄⟩ ⟨q⟩
  rw [RingHom.id_comp] at hh
  exact ⟨K', inferInstance, io, E₃, hfin, ⟨h₃⟩, hh⟩

end GlobalTheory.FieldDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  first | (exact @GlobalTheory.HTSympRep.exists_sympLevScheme) | (exact GlobalTheory.HTSympRep.exists_sympLevScheme) | (intros; apply GlobalTheory.HTSympRep.exists_sympLevScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionFractionFieldUniformStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_fraction_field_uniform : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  first | exact @GlobalTheory.Mum.RatTors.torsion_rational | exact GlobalTheory.Mum.RatTors.torsion_rational | (intros; apply GlobalTheory.Mum.RatTors.torsion_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrdStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | exact GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | (intros; apply GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  first | exact @GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | exact GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | (intros; apply GlobalTheory.GenRestrict.exists_genericPoints_equiv_any <;> assumption)
end

