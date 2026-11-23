module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_units_trivialize_modulo_ideal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)), ⨆ a, V a = ⊤ →
    ∀ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) →
      (∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | exact GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | (intros; apply GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormulaStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_degree_one_tower_formula : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F'') (l : BC F F''), (∀ T b, l.α T b = n.α T (m.α T b)) → ∀ x : S ⊗[R] C1 F, th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | exact GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | (intros; apply GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyDimensionLowerBound
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.FirstCohomologyLowerBound

theorem dim_le (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (g n : ℕ) (hg : ringKrullDim R = g)
    (I : Ideal R) (hne : I ≠ ⊤) (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = I) : g ≤ n := by
  have hm : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
    rwa [← hI p hp.1.1 hp.1.2]
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes I _ hm
  have h2 : Submodule.spanRank I ≤ n := by
    rw [← hf]
    refine (Submodule.spanRank_span_le_card (R := R) (Set.range f)).trans (Cardinal.mk_range_le.trans ?_)
    simp
  have h3 : (IsLocalRing.maximalIdeal R).height ≤ n := by
    refine h1.trans ?_
    simpa using Cardinal.toENat.monotone' h2
  have h4 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) = ((g : ℕ∞) : WithBot ℕ∞) :=
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hg
  rw [WithBot.coe_inj.1 h4] at h3
  exact_mod_cast h3

theorem exists_ample (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  haveI := hA.proper
  obtain ⟨M, hM⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA)
  exact ⟨M, hM.isLB, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hM.isLB).2 hM⟩

theorem evc_lam' {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem triv_lam_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) :
    Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP, evc_lam' hL, lam_one_left]

theorem one_mem_locus {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB)
    (Z : Over S) (i : Z ⟶ A) (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) (T : Over S) :
    ∃ z : T ⟶ Z, z ≫ i = 1 := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine (h.2 T 1).1 ?_
  rw [triv_ev_iff hP, evc_lam' hL, MonObj.comp_one, lam_one_right]

theorem snd_smooth_proper {S : Scheme.{0}} (A T : Over S) [Smooth A.hom] [IsProper A.hom] :
    Smooth (snd A T).left ∧ IsProper (snd A T).left := by
  have h : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  exact ⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance⟩

theorem lam_triv_left {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over S} (x : T ⟶ A) (h : Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x))) :
    Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP] at h ⊢
  have e := congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) h
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc, evc_lam' hL, lam_comm] at e
  rwa [evc_lam' hL]

theorem finite_sections (hK : PositivityTheory.ObstructionTrivialLocus.KFinite) (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (Z : Over (Sp k)) (i : Z ⟶ A)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) : Set.Finite {σ : Sp k ⟶ Z.left | σ ≫ Z.hom = 𝟙 _} := by
  haveI := hA.comm
  haveI : IsClosedImmersion i.left := h.1
  have hF := hK (Sp k) A hA L hL hamp k (𝟙 _)
  refine Set.Finite.of_finite_image (f := fun σ ↦ σ ≫ i.left) ((hF.image fun x ↦ x.left).subset ?_)
    (fun a _ b _ e ↦ (cancel_mono i.left).1 e)
  rintro _ ⟨σ, hσ, rfl⟩
  let z : Over.mk (𝟙 (Sp k)) ⟶ Z := Over.homMk σ hσ
  refine ⟨z ≫ i, lam_triv_left hL _ ((h.2 _ _).2 ⟨z, rfl⟩), rfl⟩

theorem stalk_local (X : Scheme.{0}) (x : X) : IsLocalRing (X.presheaf.stalk x) := inferInstance

theorem stalk_noeth (X : Scheme.{0}) [IsLocallyNoetherian X] (x : X) : IsNoetherianRing (X.presheaf.stalk x) :=
  inferInstance

theorem core (hFew : FewEqSt) (hFB : FlatBCSt) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] [Smooth A.hom]
    [IsProper A.hom] (hfin : Module.Finite k (HO1 A.hom)) (N : LB (A ⊗ A).left) (hN : N.IsLB) (Z : Over (Sp k))
    (i : Z ⟶ A) (hi : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (y₀ : Sp R ⟶ A.left) (g : ℕ) (hdim : ringKrullDim R = g) (I : Ideal R) (hne : I ≠ ⊤)
    (hrad : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (hJ : ∀ J : Ideal R, (∃ z : Sp (R ⧸ J) ⟶ Z.left, z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ y₀) ↔ I ≤ J) :
    g ≤ Module.finrank k (HO1 A.hom) := by
  let T : Over (Sp k) := Over.mk (y₀ ≫ A.hom)
  let y : T ⟶ A := Over.homMk y₀ rfl
  have hs := snd_smooth_proper A T
  obtain ⟨f, hf⟩ := hFew R (A ⊗ T).left (snd A T).left (Module.finrank k (HO1 A.hom))
    hs.1 hs.2 (fun X' s' φ h ↦ _root_.GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite hFB k A hfin R _ X' s' φ h)
    (ev N (fst A T) (snd A T ≫ y)) (pull_isLB hN _) I hne
    (fun J ↦ (GlobalTheory.T.trivial_locus_represents_triviality A A Z N hN i hi T y (spMap (Ideal.Quotient.mk J))).trans (hJ J))
  exact dim_le R g _ hdim I hne hrad f hf

theorem first_cohomology_dimension_lower_bound : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim := by
  intro hTL hKF hFB hFew hSD k _ _ A _ g hA hsm hfin
  obtain ⟨L, hL, hamp⟩ := exists_ample k A hA
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  haveI hnoeth : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨Z, i, hi⟩ := hTL (Sp k) A A hA hnoeth (abelian₂ A L) hP (triv_lam_one A L hL)
  haveI : IsClosedImmersion i.left := hi.1
  haveI : LocallyOfFiniteType Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hcl := _root_.GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points k Z.left Z.hom (finite_sections hKF k A hA L hL hamp Z i hi)
  let e : Sp k ⟶ A.left := (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left
  have he : e ≫ A.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp k)) ⟶ A)
  let p : Sp k := IsLocalRing.closedPoint k
  obtain ⟨z, hz⟩ := one_mem_locus A L hL Z i hi (Over.mk (𝟙 (Sp k)))
  have hx : e.base p ∈ Set.range i.left := ⟨z.left.base p, by
    have : z.left ≫ i.left = e := congrArg (fun q ↦ q.left) hz
    rw [← this]; rfl⟩
  have hd := hSD k A.left A.hom e g he hsm p
  generalize (e.base p : A.left) = x at hx hd
  obtain ⟨I, hne, hrad, hJ⟩ := _root_.GlobalTheory.CompanionTheory.StalkIdeal.exists_stalk_ideal A.left Z.left i.left x hx hcl
  exact @core hFew hFB k _ A _ _ _ hfin (abelian₂ A L) hP Z i hi (A.left.presheaf.stalk x) _ (stalk_local A.left x)
    (stalk_noeth A.left x) (A.left.fromSpecStalk x) g hd I hne hrad hJ

end GlobalTheory.CompanionTheory.FirstCohomologyLowerBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_data_cohomology_base_change : ∀ (R A B C H S : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C] [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B) (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B), g ∘ₗ f = 0 → π ∘ₗ j = LinearMap.id → g ∘ₗ j = 0 → π ∘ₗ f = 0 → j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id → Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | exact GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | (intros; apply GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximalStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_reduction_zero_of_maximal : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → (∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) → b = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | exact GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | (intros; apply GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverseStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_splitting_global_generalized_inverse : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B), (∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) → ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | exact GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k) (g : ℕ)
    (hf : SmoothOfRelativeDimension g f) : topologicalKrullDim X ≤ g := by
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le fun x ↦ GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension g f x

theorem subsingleton_coh_abelian (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g n : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hn : g < n) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) n) := by
  refine GlobalTheory.subsingleton_coh_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA) _ ?_
  refine lt_of_le_of_lt ((topologicalKrullDim_subspace_le _ _).trans
    (topologicalKrullDim_le_of_smooth A.hom g hg)) ?_
  exact_mod_cast hn

theorem exact_of_subsingleton_Hs {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (n : ℕ) (hdd : dn F (n + 1) ∘ₗ dn F n = 0) (h : Subsingleton (Hs F n)) :
    Function.Exact (dn F n) (dn F (n + 1)) := by
  intro x
  constructor
  · intro hx
    have hm : (⟨x, hx⟩ : LinearMap.ker (dn F (n + 1))) ∈
        (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hdd y

theorem vanSt (hCx : CxSt) (hCmp : CmpSt) : VanSt := by
  intro R _ A _ g hA hg hR P _ _ S n hn
  letI := hR.toField
  have hsep : IsSeparated A.hom := by
    have := hA.proper
    infer_instance
  obtain ⟨e⟩ := (hCmp R A.left A.hom hsep P S).2 n
  have hs : Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) (n + 1)) :=
    subsingleton_coh_abelian R A g (n + 1) hA hg (Nat.lt_succ_of_le hn)
  exact exact_of_subsingleton_Hs _ n ((hCx R _ (OSys A.hom S)).1 n) e.toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hodge
end

