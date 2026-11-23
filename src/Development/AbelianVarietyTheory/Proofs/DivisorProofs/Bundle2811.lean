module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
section
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_baseChange_rigid : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.BaseChange ∧
      GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro hH
  have h : GlobalTheory.Published.AbelianDeRhamStructure ∧
      GlobalTheory.Published.CrystallineDeRham :=
    GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
  obtain ⟨⟨hfree, -, hbc⟩, hcrys⟩ := h
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hbc, GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
section
namespace GlobalTheory

theorem abelianDualCrystal_of_dualAbelianScheme :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.AbelianDualCrystal :=
  fun h ↦ ⟨h, GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.toCrystallineDeRham⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
section
namespace GlobalTheory

theorem abelianDeRham_of_hodge_cube_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  by
    intro hH hC hD hP
    obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ :=
      _root_.GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses
        GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
    have hF : GlobalTheory.Published.AbelianDeRham.Free :=
      GlobalTheory.AbelianPrim.abelianDeRham_free hfree
    exact ⟨hF, hhodge, hbc,
      GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
      _root_.GlobalTheory.CubeDual.abelianDeRham_duality hC hD hP hF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfHodgeDeRham
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_hodgeDeRham (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) :
    AbelianSchemeLifts := by
  intro R _ _ I hI R₀ _ π hπ hk g A₀ _ A' _ i' h' hA hg
  haveI : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ π hπ
  obtain ⟨-, -, -, -, -, -, hA₀, hg₀⟩ := _root_.GlobalTheory.LiftSys.abelianLift_facts hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  have hG : Good A₀.hom := _root_.GlobalTheory.LiftSys.good_of_isAbelianScheme hC hH R₀ A₀ g hA₀ hg₀
  have hR : RhoBC hI hk A₀.hom := _root_.GlobalTheory.LiftSys.rhoBC_of_abelianLift hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨ad1, ad2, ad3⟩ := _root_.GlobalTheory.LiftSys.admissible_classification hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨S', ⟨P'⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom A'.left A'.hom i' h'.1 hA.smooth
  obtain ⟨hF', hc'⟩ := _root_.GlobalTheory.LiftSys.full_and_isCompl hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg S' P'
  have core1 := _root_.GlobalTheory.LiftSys.summand_of_full R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc'
  have ksup := _root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk A₀.left A₀.hom S' hR hF'
  have fil : ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
      ∀ S : Sys I π A₀.hom, S.Presents X.hom i → schemeFil (divided₂ hI) A₀ X i h.w =
        ((S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator := fun X i h hX S P ↦
    congrArg Submodule.dualAnnihilator
      (GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys hC R R₀ I hI π hπ hk A₀ hA₀.proper hA₀.geomConnected X i h hX S P)
  refine ⟨⟨fun X i h hX ↦ ?_, fun F hF ↦ ?_⟩, fun X Y i j h k hX hY e ↦ ?_⟩
  · obtain ⟨S, ⟨P⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨hc, hs⟩ := core1 S
    obtain ⟨F, hF, e⟩ := ad1 (S.K hI) hc fun c ↦ by rw [hs]; exact ksup c
    exact ⟨F, hF, (fil X i h hX S P).trans e⟩
  · obtain ⟨K, hc, hs, e⟩ := ad2 F hF
    obtain ⟨S, rfl⟩ := _root_.GlobalTheory.LiftSys.exists_sys_of_summand R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc' K hc
      (Submodule.ext fun c ↦ (hs c).trans (ksup c).symm)
    obtain ⟨X, s, i, h1, h2, ⟨P⟩⟩ := GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem R R₀ I hI π hπ hk A₀.left A₀.hom S
    obtain ⟨h, hX⟩ := _root_.GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk A₀.left A₀.hom S X s i h1 h2 P
    exact ⟨Over.mk s, i, h, hX, (fil (Over.mk s) i h hX S P).trans e⟩
  · obtain ⟨S, ⟨P⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨T, ⟨Q⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom Y.left Y.hom j k hY
    have hK : T.K hI = S.K hI := ad3 _ _ (core1 T).1 (core1 S).1
      ((fil Y j k hY T Q).symm.trans (e.symm.trans (fil X i h hX S P)))
    have hT : T.Full hI := (_root_.GlobalTheory.LiftSys.K_inf_eq_and_full R R₀ I hI π hπ hk A₀.left A₀.hom hG.const S' T).2 hF'
    obtain ⟨f, hf, hij⟩ := _root_.GlobalTheory.LiftSys.Glue.presents_hom R R₀ I hI π hπ hk A₀.left A₀.hom T S X.left X.hom i Y.left Y.hom j h Q P
      (_root_.GlobalTheory.LiftSys.sysHom_of_K_eq R R₀ I hI π hπ hk A₀.left A₀.hom hG hR T S hT hK)
    haveI := hX
    have hn : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
    haveI : IsIso (Over.homMk f hf : X ⟶ Y) :=
      GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hn X Y A₀ A₀ i j h k inferInstance
        (Over.homMk f hf) (𝟙 A₀) (by simpa using hij) inferInstance
    exact ⟨asIso (Over.homMk f hf : X ⟶ Y), hij⟩

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyAnyRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

def semiToLin {S R : Type} [CommRing S] [CommRing R] [Algebra S R] {M N : Type} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N] (f : M →ₛₗ[algebraMap S R] N) :
    M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by simp [f.map_smulₛₗ, algebraMap_smul]

theorem fp_of_tensor_equiv {S R M N : Type} [CommRing S] [CommRing R] [Algebra S R] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] {g : ℕ} (e : R ⊗[S] M ≃ₗ[R] N) (h : FP S M g) : FP R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange, h3]

theorem wedge_of_isBaseChange {S R M N M₂ N₂ : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
    [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower S R N₂]
    {φ : M →ₗ[S] N} {ψ : M₂ →ₗ[S] N₂} (hφ : IsBaseChange R φ) (hψ : IsBaseChange R ψ)
    (cM : M →ₗ[S] M →ₗ[S] M₂) (cN : N →ₗ[R] N →ₗ[R] N₂) (hc : ∀ m m', ψ (cM m m') = cN (φ m) (φ m'))
    (eM : ⋀[S]^2 M ≃ₗ[S] M₂) (heM : ∀ a b, eM (exteriorPower.ιMulti S 2 ![a, b]) = cM a b) :
    ∃ e : ⋀[R]^2 N ≃ₗ[R] N₂, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cN a b := by
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hφ 2
  let e : ⋀[R]^2 N ≃ₗ[R] N₂ := hE.equiv.symm ≪≫ₗ eM.baseChange S R _ _ ≪≫ₗ hψ.equiv
  refine ⟨e, ?_⟩
  have key : ∀ m m', e (exteriorPower.ιMulti R 2 ![φ m, φ m']) = cN (φ m) (φ m') := by
    intro m m'
    have h1 : exteriorPower.ιMulti R 2 ![φ m, φ m'] =
        GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m']) := by
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti]
      congr 1
      funext k
      fin_cases k <;> rfl
    have h2 : hE.equiv.symm (GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m'])) =
        1 ⊗ₜ exteriorPower.ιMulti S 2 ![m, m'] := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [h1]
    change hψ.equiv (eM.baseChange S R _ _ (hE.equiv.symm _)) = _
    rw [h2, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, heM, hc]
  let iw := exteriorPower.ιMulti R 2 (M := N)
  have u0 : ∀ a b x : N, (![x, b] : Fin 2 → N) = Function.update ![a, b] 0 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have u1 : ∀ a b x : N, (![a, x] : Fin 2 → N) = Function.update ![a, b] 1 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have add0 : ∀ a a' b : N, iw ![a + a', b] = iw ![a, b] + iw ![a', b] := by
    intro a a' b
    have := iw.map_update_add ![a, b] 0 a a'
    rwa [← u0 a b (a + a'), ← u0 a b a, ← u0 a b a'] at this
  have add1 : ∀ a b b' : N, iw ![a, b + b'] = iw ![a, b] + iw ![a, b'] := by
    intro a b b'
    have := iw.map_update_add ![a, b] 1 b b'
    rwa [← u1 a b (b + b'), ← u1 a b b, ← u1 a b b'] at this
  have smul0 : ∀ (r : R) (a b : N), iw ![r • a, b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 0 r a
    rwa [← u0 a b (r • a), ← u0 a b a] at this
  have smul1 : ∀ (r : R) (a b : N), iw ![a, r • b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 1 r b
    rwa [← u1 a b (r • b), ← u1 a b b] at this
  have zero0 : ∀ b : N, iw ![0, b] = 0 := fun b => by
    simpa using smul0 0 0 b
  have zero1 : ∀ a : N, iw ![a, 0] = 0 := fun a => by
    simpa using smul1 0 a 0
  intro a b
  induction a using hφ.inductionOn with
  | add x y hx hy => simp only [iw] at add0; rw [add0, map_add (f := _), hx, hy, map_add (f := _), LinearMap.add_apply]
  | smul r x hx => simp only [iw] at smul0; rw [smul0, map_smul, hx, map_smul, LinearMap.smul_apply]
  | tmul m =>
    induction b using hφ.inductionOn with
    | add x y hx hy => simp only [iw] at add1; rw [add1, map_add (f := _), hx, hy, map_add (f := _)]
    | smul r x hx => simp only [iw] at smul1; rw [smul1, map_smul, hx, map_smul]
    | tmul m' => exact key m m'

theorem tensor_equiv_of_tower {S R R' M N P : Type} [CommRing S] [CommRing R] [CommRing R'] [Algebra S R]
    [Algebra R R'] [Algebra S R'] [IsScalarTower S R R'] [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R' P]
    (φ : M →ₛₗ[algebraMap S R] N) (χ : N →ₛₗ[algebraMap R R'] P) (θ : M →ₛₗ[algebraMap S R'] P)
    (hθ : ∀ m, χ (φ m) = θ m) (e1 : R ⊗[S] M ≃ₗ[R] N) (he1 : ∀ m, e1 (1 ⊗ₜ m) = φ m)
    (e2 : R' ⊗[S] M ≃ₗ[R'] P) (he2 : ∀ m, e2 (1 ⊗ₜ m) = θ m) :
    ∃ e : R' ⊗[R] N ≃ₗ[R'] P, ∀ c, e (1 ⊗ₜ c) = χ c := by
  refine ⟨(e1.symm.baseChange R R' _ _) ≪≫ₗ AlgebraTensorModule.cancelBaseChange S R R' R' M ≪≫ₗ e2,
    fun c => ?_⟩
  obtain ⟨x, rfl⟩ := e1.surjective c
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have h1 : e1 (r ⊗ₜ m) = r • φ m := by
      rw [← he1, ← e1.map_smul, smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (algebraMap R R' r) ⊗ₜ[S] m = (algebraMap R R' r) • ((1 : R') ⊗ₜ[S] m) := by
      rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      AlgebraTensorModule.cancelBaseChange_tmul]
    rw [Algebra.smul_def, _root_.mul_one, h2, e2.map_smul, he2, h1, χ.map_smulₛₗ, hθ]
  | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]

theorem oStr_of_noetherian : OStr := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hfg, hB, hBg, hpb⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hFP, hW, hBC1, hBC2⟩ := _root_.GlobalTheory.AbCohRing.oStr_noetherian S B g hB hBg
  have hAB : IsPullback φ A.hom B.hom (spMap (algebraMap S R)) := hpb.1
  obtain ⟨e1, he1⟩ := hBC1 R A.left A.hom φ hAB
  obtain ⟨e2, he2⟩ := hBC2 R A.left A.hom φ hAB
  have hp1 : IsBaseChange R (semiToLin (pullHO1 hAB.w)) := IsBaseChange.of_equiv e1 he1
  have hp2 : IsBaseChange R (semiToLin (pullHO2 hAB.w)) := IsBaseChange.of_equiv e2 he2
  have hcomp := _root_.GlobalTheory.AbCoh.pull_comp_cup_id
  refine ⟨fp_of_tensor_equiv e1 hFP, ?_, ?_, ?_⟩
  · obtain ⟨eM, heM⟩ := hW
    exact wedge_of_isBaseChange hp1 hp2 (cup _) (cup _)
      ((hcomp.2.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w).1) eM heM
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC1 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO1 hAB.w) (pullHO1 h.w) (pullHO1 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).1) e1 he1 e3 he3
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC2 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO2 hAB.w) (pullHO2 h.w) (pullHO2 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).2.1) e2 he2 e3 he3

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.PhaseQuad

open GlobalTheory.RootEx

section General
variable {V k : Type*} [AddCommGroup V] [CommRing k] (O : Subring k) (S : Set V)

def Aff (f : V → k) : Prop := ∃ a : V → k, (∀ v l, f (v + l) = f v + a l) ∧ ∀ l ∈ S, a l ∈ O

def Quad (f : V → k) : Prop := ∀ v, ∀ l ∈ S, ∀ l' ∈ S, f (v + l + l') + f v - (f (v + l) + f (v + l')) ∈ O

variable {O S}

theorem Aff.const (c : k) : Aff O S fun _ => c := ⟨fun _ => 0, by simp, fun _ _ => zero_mem _⟩

theorem Aff.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Aff O S (f i)) :
    Aff O S fun v => ∑ i ∈ s, f i v := by
  choose a ha hO using h
  exact ⟨fun l => ∑ i ∈ s, a i l, fun v l => by simp only [ha, Finset.sum_add_distrib],
    fun l hl => sum_mem fun i _ => hO i l hl⟩

theorem Aff.ite (p : Prop) [Decidable p] {f : V → k} (h : Aff O S f) : Aff O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using Aff.const 0

theorem Aff.quad {f : V → k} (h : Aff O S f) : Quad O S f := by
  obtain ⟨a, ha, -⟩ := h
  intro v l _ l' _
  have : f (v + l + l') + f v - (f (v + l) + f (v + l')) = 0 := by
    rw [ha (v + l), ha v l']; ring
  rw [this]; exact zero_mem _

theorem Aff.mul {f g : V → k} (hf : Aff O S f) (hg : Aff O S g) : Quad O S fun v => f v * g v := by
  obtain ⟨a, ha, haO⟩ := hf
  obtain ⟨b, hb, hbO⟩ := hg
  intro v l hl l' hl'
  have : f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) =
      a l * b l' + a l' * b l := by
    rw [ha (v + l), ha v l', ha v l, hb (v + l), hb v l', hb v l]; ring
  show f (v + l + l') * g (v + l + l') + f v * g v - (f (v + l) * g (v + l) + f (v + l') * g (v + l')) ∈ O
  rw [this]
  exact add_mem (mul_mem (haO l hl) (hbO l' hl')) (mul_mem (haO l' hl') (hbO l hl))

theorem Quad.add {f g : V → k} (hf : Quad O S f) (hg : Quad O S g) : Quad O S fun v => f v + g v := by
  intro v l hl l' hl'
  convert add_mem (hf v l hl l' hl') (hg v l hl l' hl') using 1
  ring

theorem Quad.sum {ι : Type*} (s : Finset ι) {f : ι → V → k} (h : ∀ i, Quad O S (f i)) :
    Quad O S fun v => ∑ i ∈ s, f i v := by
  intro v l hl l' hl'
  convert sum_mem (t := s) fun i _ => h i v l hl l' hl' using 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem Quad.ite (p : Prop) [Decidable p] {f : V → k} (h : Quad O S f) : Quad O S fun v => if p then f v else 0 := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using (Aff.const 0).quad

end General

section Phase
variable {k : Type*} [Field k] {G : Grid k} (O : Subring k)

def intVars (G : Grid k) : Set (Vars G) := {e | ∀ j r, e j r ∈ O}

theorem aff_stepPt (j : Fin (G.m - 1)) (x₀ : Matrix (Fin (topRank G (j + 1))) (Fin (topRank G j)) k) (r s) :
    Aff O (intVars O G) fun e : Vars G => stepPt x₀ (e j) r s := by
  by_cases h : Free ((G.m - 2 - j) / 2 + 1) (r, s) ∨ Kept (r, s)
  · refine ⟨fun l => l j ⟨(r, s), h⟩, fun v l => ?_, fun l hl => hl j _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_pos h, Pi.add_apply, add_assoc]
  · refine ⟨fun _ => 0, fun v l => ?_, fun _ _ => zero_mem _⟩
    simp only [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]

theorem aff_rowVar (x : ColArgs G) (j : ℕ) (s) : Aff O (intVars O G) fun e : Vars G => rowVar x e j s := by
  by_cases h : j < G.m - 1
  · simp only [rowVar, dif_pos h]
    exact Aff.sum _ fun l => Aff.ite _ (aff_stepPt O ⟨j, h⟩ (x j) _ _)
  · simp only [rowVar, dif_neg h]
    exact Aff.const _

theorem quad_phase (x : ColArgs G) : Quad O (intVars O G) fun e : Vars G => phase x e := by
  unfold phase
  refine Quad.sum _ fun j => Quad.add ?_ (Quad.ite _ (Quad.sum _ fun r => ?_))
  · exact (Aff.sum _ fun i => aff_stepPt O j (x j) _ _).quad
  · exact (aff_rowVar O x _ r).mul (aff_stepPt O j (x j) _ _)

end Phase

theorem psi_phase_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  intro k _ _ _ _ G ψ hψ ϖ hϖ n x v l l' hl hl'
  have hint : ∀ e ∈ varLat G ϖ n, e ∈ intVars 𝒪[k] G := fun e he j r => by
    have h1 : valuation k ((ϖ ^ n : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val]
      exact pow_mem hϖ.mem n
    exact (he j r).trans h1
  have hq := quad_phase 𝒪[k] x v l (hint l hl) l' (hint l' hl')
  have h1 : ψ (-(phase x (v + l + l') + phase x v - (phase x (v + l) + phase x (v + l')))) = 1 :=
    (hψ 1).2 le_rfl _ (by rw [Valuation.map_neg, map_one]; exact hq)
  rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← one_mul (ψ (-phase x (v + l) + -phase x (v + l'))), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  ring

end GlobalTheory.UnfoldLoss.PhaseQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem crystallineCechDeRhamComparison_bijective_complexAbelian :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  intro A _ hA
  have := hA.smooth
  have := hA.proper
  exact GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne (str A)
    inferInstance inferInstance inferInstance

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinearStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  first | (exact @GlobalTheory.Katz.rig_pull_natural_semi) | (exact GlobalTheory.Katz.rig_pull_natural_semi) | (intros; apply GlobalTheory.Katz.rig_pull_natural_semi  <;> assumption)
end

