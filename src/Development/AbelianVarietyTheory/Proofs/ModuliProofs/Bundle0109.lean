module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_isPullback :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap K (DualNumber K))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro L K _ A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, h₁, h₂⟩ := exists_isGrpPullback_retraction L.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, h₁, hj, h₂⟩

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem exists_isMonHom_of_map_lattice :
    ThetaUnifAV → Out.Laws → ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hT hL P P' g u u' F hg hg' hF
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (w : HolUnif Q.A Q.L g), Q.g = g →
      ∃ (v : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : v.Λ → ℂ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        v.IsAH Hm χ ∧ (∀ (k : ℕ) θ, v.IsThetaFn Hm χ k θ → ∃ s, v.IsFnPow k s θ) ∧
        (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ ∀ z, v.ex (T z) = w.ex z := by
    rintro Q w rfl
    obtain ⟨rig, hrig⟩ := Q.rigid
    obtain ⟨v, Hm, χ, -, hAH, -, -, -, -, hsec, -⟩ := hT Q rig hrig
    obtain ⟨T, hTv⟩ := exists_linearEquiv_of_holUnif hL.mulN Q w v
    exact ⟨v, Hm, χ, T, hAH, fun k θ h => ((hsec k).2 θ h).exists, fun k s => ((hsec k).1 s).exists, hTv⟩
  obtain ⟨v, Hm, χ, T, hAH, hsec, -, hv⟩ := key P u hg
  obtain ⟨v', Hm', χ', T', hAH', -, hfn, hv'⟩ := key P' u' hg'
  let F₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀ : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hΛ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := fun l hl => by
    obtain ⟨z, rfl⟩ := T.surjective l
    rw [hF₀, ← v'.ker, hv', u'.ker]
    refine hF z ?_
    rwa [← u.ker, ← hv, v.ker]
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.isLB P'.isLB hAH hAH'
    F₀ hΛ 4
  obtain ⟨f, hf, hfe⟩ := exists_isMonHom_of_complementary hL.ample P P' v v' hsec hfn F₀ hΛ d hd
  exact ⟨f, hf, fun z => by rw [← hv', ← hF₀, hfe, hv]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.RigidifyTwist

open CechPic

theorem pull_cls_eq_zero {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (r : Z ⟶ X) (i : L.ι)
    (hi : ∀ z, r z ∈ L.U i) : CechPic.pull r (cls L hL) = 0 := by
  rw [← cls_pull hL r (pull_isLB hL r), cls_eq_zero_iff]
  refine (iso_triv_iff _).1 (iso_of_chart (pull_isLB hL r) ⟨fun _ _ => i, fun _ y _ => mem_pull.2 (hi y), ?_⟩)
  intro y p q hp hq
  rw [gm_pull_g L r (𝟙 Z) y (fun _ => i) (fun _ => i) (mem_pull.2 (hi y)) (mem_pull.2 (hi y))]
  have hy : (𝟙 Z ≫ r) y ∈ L.U i := by
    simpa using hi y
  rw [gm_self hL _ y hy]
  exact map_one _

theorem eSec_hom {S : Scheme.{0}} (A : Over S) [GrpObj A] : eSec A ≫ A.hom = 𝟙 S := by
  unfold eSec
  exact (Over.w _).trans rfl

private theorem cls_pull_tens_dual_eq_sub {S Y : Scheme.{0}} (A : Over S) (M : LB A.left) (hM : M.IsLB) (N : LB S)
    (hN : N.IsLB) (f : Y ⟶ A.left) (h : ((tens M (dual (N.pull A.hom))).pull f).IsLB) :
    cls _ h = pull f (cls M hM) - pull (f ≫ A.hom) (cls N hN) := by
  have hP := pull_isLB hN A.hom
  rw [cls_pull (isLB_tens hM (isLB_dual hP)) f h, cls_tens hM (isLB_dual hP), cls_dual hP,
    cls_pull hN A.hom, map_add, map_neg, pull_comp, sub_eq_add_neg]

private theorem pGen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) : PGen w := by
  intro Y f y j1 j2 k1 k2 h1 h2 h3 h4
  unfold gw
  have m1 : f y ∈ (L.pull F).U (fun _ => j1) := mem_pull.2 h1
  have m2 : f y ∈ (L.pull F).U (fun _ => j2) := mem_pull.2 h2
  have hV : f y ∈ ((L.pull F).div L').U (fun _ => j1, k1) ⊓ ((L.pull F).div L').U (fun _ => j2, k2) :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j1, k1) (fun _ => j2, k2))
  rw [map_mul, gm_res f y _ hV, gm_res f y _ hV, gm_div' (L.pull F) L' f y _ _ ⟨m1, h3⟩ ⟨m2, h4⟩,
    gm_pull_g L F f y _ _ m1 m2] at e
  exact e

private theorem lbIso_tens_dual_pull_eSec_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB)
    (U : S.Opens) (j : (M.pull (eSec A)).ι) (hU : U ≤ (M.pull (eSec A)).U j) :
    LBIso ((tens M (dual ((M.pull (eSec A)).pull A.hom))).pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hT := isLB_tens hM (isLB_dual (pull_isLB hN A.hom))
  have hz : ∀ z : U.toScheme, U.ι z ∈ (M.pull (eSec A)).U j := fun z => by
    exact hU z.2
  refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
  rw [cls_pull_tens_dual_eq_sub A M hM _ hN, ← morphismRestrict_ι, pull_comp, pull_cls_eq_zero hN U.ι j hz, map_zero,
    sub_zero, cls_pull hM]

theorem exists_rigidified_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left), M.IsLB → ∃ M' : LB A.left, M'.IsLB ∧ Out.Rigidified A M' ∧ (∀ p : S, ∃ U : S.Opens, p ∈ U ∧ LBIso (M'.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), φ ≫ A.hom = π ≫ x → LBIso (M'.pull φ) (M.pull φ)) ∧ (IsProper A.hom → Out.RelAmple A M → Out.RelAmple A M') := by
  intro S A _ M hM
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hP : ((M.pull (eSec A)).pull A.hom).IsLB := pull_isLB hN _
  have hT : (tens M (dual ((M.pull (eSec A)).pull A.hom))).IsLB := isLB_tens hM (isLB_dual hP)
  refine ⟨tens M (dual ((M.pull (eSec A)).pull A.hom)), hT, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hT _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, eSec_hom A, pull_id, cls_pull hM (eSec A) hN, sub_self]
  · intro p
    obtain ⟨j, hj⟩ := exists_chart hN p
    exact ⟨_, hj, lbIso_tens_dual_pull_eSec_restrict A M hM _ j le_rfl⟩
  · intro K _ x X φ π hφ
    obtain ⟨j, hj⟩ := exists_chart hN (x (Classical.arbitrary (Sp K)))
    have hx : ∀ z, x z ∈ (M.pull (eSec A)).U j := fun z => by
      rw [Subsingleton.elim z (Classical.arbitrary _)]
      exact hj
    refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, hφ, pull_comp, pull_cls_eq_zero hN x j hx, map_zero, sub_zero, cls_pull hM]
  · intro hpr hamp
    have := hpr
    refine AmpleLocal.relAmple_of_locally S A _ hT inferInstance inferInstance fun s => ?_
    obtain ⟨j, hj⟩ := exists_chart hN s
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hj
    obtain ⟨w, hw⟩ := lbIso_tens_dual_pull_eSec_restrict A M hM V j hVle
    have hpw : PGen w := pGen_of_isGen w hw
    exact ⟨V, hsV, relAmple_pull (A' := Over.mk (A.hom ∣_ V)) (isPullback_morphismRestrict A.hom V).flip hM
      (pull_isLB hT _) (w := w) hpw V hV (fun y => y.2) hamp⟩

end GlobalTheory.RigidifyTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SecFamily

theorem pushInvertible_of_laws (h : Out.Laws) (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) :
    PushInvertible P.A P.L :=
  GlobalTheory.PushInv.pushInvertible h.secBaseChange X P

theorem exists_secOn_nonvanishing : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ i)) := by
  intro h X _ P x
  obtain ⟨V, hV, θ, hθ, -, H⟩ := pushInvertible_of_laws h X P x
  exact ⟨V, θ, hV, hθ, H⟩

end GlobalTheory.SecFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsOrbitSubsetNonzeroLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem exists_forms_forall_mem_basicOpen {Γ : Type} [Finite Γ] {R : Type} [CommRing R] {N : ℕ}
    {X : Scheme.{0}} [CompactSpace X] (φ : Γ → (X ⟶ PSpace R N)) :
    ∃ (d n : ℕ) (F : Fin n → MvPolynomial (Fin (N + 1)) R), 0 < d ∧ (∀ i, (F i).IsHomogeneous d) ∧
      ∀ x : X, ∃ i, ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (F i) := by
  classical

  have orbit : ∀ x : X, ∃ e : ℕ, 0 < e ∧ ∃ f ∈ ProjSpace.grading R N e,
      Set.range (fun g => φ g x) ⊆ Proj.basicOpen (ProjSpace.grading R N) f := fun x =>
    FiniteSubsetsInAffineOpens.exists_proj_basicOpen (ProjSpace.grading R N) (Set.finite_range _)
  choose e he f hf hsub using orbit

  let U : X → Set X := fun x => {z | ∀ g, φ g z ∈ Proj.basicOpen (ProjSpace.grading R N) (f x)}
  have hU : ∀ x, U x ∈ nhds x := fun x => by
    refine IsOpen.mem_nhds ?_ fun g => hsub x ⟨g, rfl⟩
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun g =>
      (φ g).continuous.isOpen_preimage _ (Proj.basicOpen (ProjSpace.grading R N) (f x)).isOpen

  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  have hD : 0 < ∏ x ∈ t, e x := Finset.prod_pos fun x _ => he x
  have hdvd : ∀ x ∈ t, e x ∣ ∏ y ∈ t, e y := fun x hx => Finset.dvd_prod_of_mem e hx
  refine ⟨∏ x ∈ t, e x, t.card,
    fun i => f (t.equivFin.symm i) ^ ((∏ x ∈ t, e x) / e (t.equivFin.symm i)), hD, fun i => ?_, fun x => ?_⟩
  · have h1 : (f (t.equivFin.symm i)).IsHomogeneous (e (t.equivFin.symm i)) := hf _
    have h2 := h1.pow ((∏ x ∈ t, e x) / e (t.equivFin.symm i))
    rwa [Nat.mul_div_cancel' (hdvd _ (t.equivFin.symm i).2)] at h2
  · have hx : x ∈ ⋃ y ∈ t, U y := by rw [ht]; exact Set.mem_univ x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
    have hxy' : ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (f y) := hxy
    refine ⟨t.equivFin ⟨y, hy⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [Proj.basicOpen_pow]
    · exact hxy' g
    · exact Nat.div_pos (Nat.le_of_dvd hD (hdvd y hy)) (he y)

theorem exists_sections_orbit_subset_nonzeroLocus : ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ρ : Γ →* Aut X), IsProjOver s → ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
  intro Γ _ _ R _ X s ρ hs
  obtain ⟨N, j, hj, -⟩ := hs

  haveI : CompactSpace (PSpace R N) := by
    refine ⟨?_⟩
    have hcov : (Set.univ : Set (PSpace R N)) = ⋃ i, (ProjSpace.chart R N i : Set (PSpace R N)) := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact ProjSpace.exists_mem_chart R N y
    rw [hcov]
    exact isCompact_iUnion fun i => (ProjSpace.isAffineOpen_chart R N i).isCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j

  obtain ⟨d, n, F, hd, hF, hcov⟩ := exists_forms_forall_mem_basicOpen (fun g => (ρ g).asIso.hom ≫ j)
  refine ⟨(lbPow (ProjSpace.O1 R N) d).pull j, n, fun i => secPull (ProjSpace.formSec d (F i) (hF i)) j,
    pull_isLB (isLB_lbPow (ProjSpace.O1_isLB R N) d) j, fun i => ?_, fun x => ?_⟩
  · rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact (Proj.isAffineOpen_basicOpen (ProjSpace.grading R N) (F i) (hF i) hd).preimage j
  · obtain ⟨i, hi⟩ := hcov x
    refine ⟨i, fun g => ?_⟩
    rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact hi g

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem existsUnique_isMonHom_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hlaws _ _ hT P P' L L' u u' F hF
  obtain ⟨rig, hrig⟩ := P.8
  obtain ⟨rig', hrig'⟩ := P'.8
  obtain ⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩ := hT P rig hrig
  obtain ⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩ := hT P' rig' hrig'
  obtain ⟨T, hTu⟩ := exists_linearEquiv_of_holUnif hlaws.6 P u v
  obtain ⟨T', hTu'⟩ := exists_linearEquiv_of_holUnif hlaws.6 P' u' v'
  set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) :=
    T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀T : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := by
    intro l hl
    have h1 : u.ex (T.symm l) = 1 := by
      rw [← hTu, T.apply_symm_apply]
      exact (v.5 l).2 hl
    have h2 : u'.ex (F (T.symm l)) = 1 := (u'.5 _).2 (hF _ ((u.5 _).1 h1))
    refine (v'.5 _).1 ?_
    have h3 : F₀ l = T' (F (T.symm l)) := by simp [F₀]
    rw [h3, hTu']
    exact h2
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7
    hAH hAH' F₀ hF₀ 4
  obtain ⟨f, hf, hfF⟩ := exists_isMonHom_of_complementary hlaws.3 P P' v v'
    (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd
  have hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f := by
    intro z
    rw [← hTu' (F z), ← hTu z, ← hfF, hF₀T]
  refine ⟨f, ⟨hf, hfu⟩, ?_⟩
  rintro f' ⟨-, hf'⟩
  have := P.5
  have : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex P.A.left P.A.hom inferInstance
  have := P'.3
  have : IsSeparated P'.A.hom := inferInstance
  apply ComplexPoints.over_hom_ext_of_complexPoints
  intro x
  obtain ⟨z, rfl⟩ := u.3 x
  rw [← hf' z, hfu z]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidAnyBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_any_base : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL => obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym

end GlobalTheory
end

