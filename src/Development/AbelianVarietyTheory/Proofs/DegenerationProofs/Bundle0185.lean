module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSmulTopOfForallMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverLocalRing
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

theorem exists_ideal_complex (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := _root_.GlobalTheory.AbLaw.exists_free_complex_of_primitive A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  let K := AlgebraicClosure p.ResidueField
  let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
  have hk : RingHom.ker φ = p := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
  · exact Or.inl hi

theorem exists_section_translate : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL _ V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing P.A.hom P.g P.smoothDim (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  have := P.isAb.comm
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hL.globalFns P.A P.isAb proj P.smoothDim P.isLB hO
    ⟨c.t, c.isGen⟩ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_tfae (algebraMap V R)).out 3 1).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) P.g (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverLocalRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

theorem exists_secsOver : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u x hx
  obtain ⟨w, hw⟩ := u.lb
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  have := ρ.P.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  have hx' : ∀ a, (x a).left ≫ u.φ = τ ≫ (ρ.pt a).left := hx
  obtain ⟨rig, hrig, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec u.A.A) (φ := fun _ => eSec ρ.P.A)
    (ε := fun _ => 1) (h := spMap u.yK) hw hL₀ hL₁ (fun _ => PolBaseChange.eSec_comm hp) ρ.rig ρ.rig_gen
  choose e he He using fun a => exists_gen_through (φ' := fun _ : Fin 1 => (x a).left) (h := τ) hw hL₀ hL₁
    (fun _ => hx' a) (ρ.fr a) (ρ.fr_tors a).2.1
  have hfr : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) := fun a =>
    FrameMove.isTorsFrame_move hp hw
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx' a) (ρ.fr_tors a) (he a) (fun z J J' hJ hJ' => by
        have := He a _ (𝟙 _) z J J' hJ hJ'
        rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, ρ.pt (n • a) = ρ.pt a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := ρ.pt_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => FrameMove.pow_eq_one_of hp (hx' _) (by
    rw [hpow, ← pow_mul]
    exact (ρ.fr_tors a).1)
  refine ⟨rig, e, th, s, hrig, hfr, fun a z J hJ => ?_, fun i a z J hJ => ?_,
    ⟨α, hα, ThetaGeom.norm_move hp τ hτ hL₀ hL₁ Hr vα ρ.α_norm,
      isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero⟩, fun a => ?_⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (He a) hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [ThetaGeom.val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (ThetaGeom.genThrough_pow τ (He a) S.N) (hs i)
      (ρ.ev_val i a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    exact q
  · obtain ⟨θ, hθ, H⟩ := ClassWeight.symLift_act_move hp τ hτ hw hL₀ hL₁ (hx' _).symm (hN a) (ρ.U_sym a)
      (fun l i => fn (algebraMap o S.R (S.ρ a l i))) (fun l i => cF u.V (y₀ (algebraMap o S.R (S.ρ a l i))))
      (fun l i => spMap_appTop_fn y₀ _) hs (ρ.U_act a)
    exact ⟨θ, hθ, fun i σ h => (ThetaGeom.comb_iff _ _ _).2 (H i σ h)⟩

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaAction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.SecComb

theorem equiv_sum {K M J : Type} [CommRing K] [AddCommGroup M] [Module K M] [Fintype J] (ρ : M ≃ₗ[K] M)
    (c : J → K) (v w : J → M) (h : ∀ i, ρ (v i) = w i) : ρ (∑ i, c i • v i) = ∑ i, c i • w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h]

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

omit [IsDomain R] in
theorem ofSec_inj {t t' : SecA A F k}
    (h : (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) = SecM.ofSec A.A t') : t = t' := by
  have h' : t.f = t'.f := congrArg Subtype.val h
  cases t; cases t'; cases h'; rfl

theorem isComb_iff {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) :
    IsComb A s b t ↔ (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) =
      ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
  have e : ∀ j, ((∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)).1 j) =
      ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun H => Subtype.ext (funext fun j => (H j).trans (e j).symm),
    fun H j => (congrFun (congrArg Subtype.val H) j).trans (e j)⟩

omit [IsDomain R] in
theorem exists_rho (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ ρ : SecM A.A A.L (k : ℤ) (TFK (R := R) F) ≃ₗ[Γ((TFK (R := R) F).left, ⊤)]
      SecM A.A A.L (k : ℤ) (TFK (R := R) F), ∀ s s' : SecA A F k,
      IsActOf A.A A.L k θ s s' ↔ ρ (SecM.ofSec A.A s) = SecM.ofSec A.A s' := by
  have hL := A.isLB
  obtain ⟨ρ, hρ⟩ := ThetaAct.exists_equiv hL θ
  refine ⟨ρ, fun s s' => ?_⟩
  rw [ThetaAct.isActOf_iff hL]
  exact ⟨fun H => ThetaAct.sv_ext hL fun y J hJ => (hρ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ hJ⟩

end GlobalTheory.SecComb

namespace GlobalTheory


open SecComb in
theorem secComb_thetaAct : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  intro R _ _ A F _ _ k J _ s b
  refine ⟨⟨SecM.toSec A.A (∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)),
    (isComb_iff A _ _ _).2 rfl⟩, fun t t' h h' => ?_, fun θ s' t t' hs h => ?_, fun θ t => ?_,
    fun I _ M r a t hr h => ?_⟩
  · exact ofSec_inj A (((isComb_iff A _ _ _).1 h).trans ((isComb_iff A _ _ _).1 h').symm)
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    have e := (congrArg ρ ((isComb_iff A _ _ _).1 h)).trans
      (equiv_sum ρ (fun l => cF R (b l)) _ _ fun i => (hρ _ _).1 (hs i))
    exact ⟨fun H => (isComb_iff A _ _ _).2 (((hρ _ _).1 H).symm.trans e),
      fun H => (hρ _ _).2 (e.trans ((isComb_iff A _ _ _).1 H).symm)⟩
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    refine ⟨SecM.toSec A.A (ρ (SecM.ofSec A.A t)), (hρ _ _).2 rfl, fun t' h => ofSec_inj A ?_⟩
    exact ((hρ _ _).1 h).symm
  · rw [isComb_iff] at h ⊢
    rw [h]
    simp only [fun i => (isComb_iff A _ _ _).1 (hr i), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have e : cF R (∑ i, M i j * a i) = ∑ i, cF R (M i j * a i) := map_sum _ _ _
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_comm _ _).trans (map_mul _ _ _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem isComb_iff_expandsF_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ k hk w₀ hw J _ s Φ b t hs
  obtain ⟨hb, hl⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨h₁, h₂⟩ := hb F k hk w₀ hw
  have h0 : U.ExpandsF F k w₀ (SecOps.secZero : SecA A F k) (0 : Fam D.toPre F k) := by
    obtain ⟨σ, hσ⟩ := (h₁ (SecOps.secZero : SecA A F k)).exists
    have h := hl F k w₀ SecOps.secZero SecOps.secZero SecOps.secZero σ σ (-1) hσ hσ (fun j => ((add_zero _).trans (mul_zero _)).symm)
    rwa [neg_one_smul, neg_add_cancel] at h
  have key : ∀ S : Finset J, ∃ u : SecA A F k,
      (∀ j, u.f j = ∑ l ∈ S, liftFun A.A _ (cF R (b l)) * (s l).f j) ∧
        U.ExpandsF F k w₀ u (∑ i ∈ S, b i • Φ i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨SecOps.secZero, fun j => by rw [Finset.sum_empty]; rfl, by rw [Finset.sum_empty]; exact h0⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, eu⟩ := ih
      refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (cF R (b a))) (s a)) u,
        fun j => ?_, ?_⟩
      · rw [Finset.sum_insert ha, ← hu j]; rfl
      · rw [Finset.sum_insert ha]
        exact hl F k w₀ (s a) u _ (Φ a) _ (b a) (hs a) eu (fun j => rfl)
  obtain ⟨u, hu, eu⟩ := key Finset.univ
  constructor
  · intro h
    obtain rfl : t = u := SecOps.sec_ext fun j => (h j).trans (hu j).symm
    exact eu
  · intro h
    obtain rfl : t = u := (h₂ _).unique h eu
    exact hu

end GlobalTheory.TestFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem partI_of_inputs : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA hM h0
  refine ⟨h0, fun E _ _ _ H D hD Xo => ?_⟩
  obtain ⟨Y, hY, hgl⟩ := hM E H D hD Xo
  refine ⟨Y, fun p W hp hW => ⟨(hY p W hp hW).1, fun i => ⟨((hY p W hp hW).2 i).1, ?_, ?_⟩⟩, hgl⟩
  · exact _root_.GlobalTheory.model_uniformisation_of_clauses h1 h2 h3 h4 h5 hE hU hP E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
  · exact _root_.GlobalTheory.LN.ArcClause.arc_clause hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
      ((hY p W hp hW).2 i).2

end GlobalTheory.LN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanishStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OnModel.theta_on_model | exact GlobalTheory.Ex.OnModel.theta_on_model | (intros; apply GlobalTheory.Ex.OnModel.theta_on_model <;> assumption)
end

