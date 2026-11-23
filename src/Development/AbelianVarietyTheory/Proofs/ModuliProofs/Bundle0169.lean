module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem CechPic.lam_pull_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x y : T' ⟶ G') :
    lam (pull φ c) x y = lam c (pushHom h T' x) (pushHom h T' y) := by
  rw [lam, lam, ← map_mul, ← map_one (pushHom h T')]
  simp only [← pull_comp]
  rfl

theorem adjoint_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  intro hG S _ A _ _ L u v hA hL hamp hu hv hd
  have := hA.smooth
  have : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hp : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : (cubeLB A ![fst A A ≫ u, snd A A] L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB A ![fst A A, snd A A ≫ v] L).IsLB := LB.isLB_linComb hL _ _
  have hN := LB.isLB_div h₂ h₁
  refine _root_.GlobalTheory.seesaw_reduced_of_dense hG S A L hA hL hamp A.left (A ⊗ A).left A.hom (snd A A).left (fst A A).left _ hp hN
    ((hd.preimage A.hom.isOpenMap).mono ?_) (lift (𝟙 A) (1 : A ⟶ A)).left ?_ ?_
  · rintro a ⟨K, _, x, G, _, _, φ, L', u', v', ⟨q, hq⟩, h, hL', hiso, hu', hv', H⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h.1 a q hq.symm
    let U : Over.mk ((G ⊗ G).hom ≫ x) ⟶ A ⊗ A := lift (pushHom h _ (fst G G)) (pushHom h _ (snd G G))
    have e₁ : U.left ≫ (fst A A).left = (fst G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have e₂ : U.left ≫ (snd A A).left = (snd G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have P : IsPullback U.left (fst G G).left (fst A A).left φ := by
      have B := (IsPullback.of_hasPullback G.hom G.hom).flip.paste_horiz h.1
      refine IsPullback.of_right ?_ e₁ hp
      rw [e₂, h.1.w]
      exact B
    have push : ∀ {w' : G ⟶ G} {w : A ⟶ A}, w'.left ≫ φ = φ ≫ w.left → ∀ y : G ⊗ G ⟶ G,
        pushHom h _ (y ≫ w') = pushHom h _ y ≫ w := fun hw y => Over.OverMorphism.ext (by
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
    refine ⟨G.left.residueField z, inferInstance, G.left.fromSpecResidueField z ≫ φ,
      pullback (fst G G).left (G.left.fromSpecResidueField z), pullback.fst _ _ ≫ U.left,
      pullback.snd _ _, ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩,
      (IsPullback.of_hasPullback _ _).paste_horiz P, ?_⟩
    · rw [← hz]
      exact congrArg φ (Scheme.fromSpecResidueField_apply z _)
    · have h₁' : (cubeLB G ![fst G G ≫ u', snd G G] L').IsLB := LB.isLB_linComb hL' _ _
      have h₂' : (cubeLB G ![fst G G, snd G G ≫ v'] L').IsLB := LB.isLB_linComb hL' _ _
      have H' := (cls_eq_iff h₁' h₂').2 H
      rw [cls_cube_two hL', cls_cube_two hL', (cls_eq_iff hL' (pull_isLB hL φ)).2 hiso, cls_pull hL,
        lam_pull_of_isGrpPullback h, lam_pull_of_isGrpPullback h, push hu', push hv'] at H'
      have j : pull U.left (cls _ h₂ - cls _ h₁) = 0 := by
        rw [cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
          lift_snd, lift_fst_assoc, lift_snd_assoc]
        exact sub_eq_zero.2 H'.symm
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁]
      exact (pull_comp _ _ _).trans ((congrArg _ j).trans (map_zero _))
  · rw [← Over.comp_left, lift_fst, Over.id_left]
  · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
      lift_snd, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, lam_one_right, lam_one_right, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem card_torsion_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) :=
  fun k _ _ B _ g N hB hg hN => GlobalTheory.abMulN_holds k B g N hB hg hN

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromC_sharpClass_fibre_of_charZero : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (c : SiegPre h (N' ^ 2) (b.ζ : o) s), c.Principal → IsSharp W a bas t c → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (SharpClass (b := b) W a bas em) t x := by
  first | exact @GlobalTheory.SharpFrom.fromC_sharpClass | exact GlobalTheory.SharpFrom.fromC_sharpClass | (intros; apply GlobalTheory.SharpFrom.fromC_sharpClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SeesawGlobal

theorem isPullback_tensor {S : Scheme.{0}} (T A : Over S) :
    IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem exists_closed_triv :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (T : Over (Sp K)) (N : LB (T ⊗ P.A).left), N.IsLB → (∃ t : (N.pull (lift (𝟙 T) (1 : T ⟶ P.A)).left).Gen, t.IsGen) → ∃ (Z : Scheme.{0}) (i : Z ⟶ T.left), IsClosedImmersion i ∧ ∀ (T' : Over (Sp K)) (h : T' ⟶ T), (∃ t : (N.pull (h ▷ P.A).left).Gen, t.IsGen) ↔ ∃ u : T'.left ⟶ Z, u ≫ i = h.left := by
  intro hL _ K _ _ P T N hN h0
  have hproj : GlobalTheory.AbLaw.IsProjBy P.A.hom := by
    obtain ⟨n, -, m, s, h₁, h₂⟩ := GlobalTheory.AbLaw.polAV_veryAmpleBy hL.polBaseChange (Sp K) P K (𝟙 _) P.A.left
      (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hL.globalFns K T P.A P.isAb hproj N hN
  refine ⟨H.left, j.left, hj, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (hH T' h).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
    exact ⟨y.left, congrArg (·.left) hy⟩
  · rintro ⟨u, hu⟩
    have hw : u ≫ H.hom = T'.hom := by rw [← Over.w j, ← Category.assoc, hu, Over.w h]
    have hloc := (hH T' h).2 ⟨Over.homMk u hw, Over.OverMorphism.ext hu⟩
    refine GlobalTheory.exists_gen_of_local_of_section (T' ⊗ P.A).left T'.left (fst T' P.A).left
      (lift (𝟙 T') (1 : T' ⟶ P.A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 T') (1 : T' ⟶ P.A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ P.A P.isAb _ _ T'.hom _ _ (isPullback_tensor T' P.A))
      hloc ?_
    refine GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _ (GlobalTheory.AbLaw.CubeOpen.triv_comp h.left ?_ h0)
    have e : h ≫ lift (𝟙 T) (1 : T ⟶ P.A) = lift (𝟙 T') (1 : T' ⟶ P.A) ≫ h ▷ P.A := by
      ext <;> simp
    exact congrArg (·.left) e

end GlobalTheory.SeesawGlobal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.HilbFn

theorem exists_forms_basis {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    ∃ G : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → MvPolynomial σ K, (∀ i, (G i).IsHomogeneous e) ∧
      ∀ F : MvPolynomial σ K, F.IsHomogeneous e → ∃! a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
        F - ∑ i, a i • G i ∈ I := by
  classical
  have hQ : ∀ x, x ∈ GlobalTheory.quotPiece I e ↔
      ∃ y, y ∈ MvPolynomial.homogeneousSubmodule σ K e ∧ Ideal.Quotient.mkₐ K I y = x := by
    intro x
    rw [GlobalTheory.quotPiece_natCast, Submodule.mem_map]
    rfl
  have : Module.Finite K (GlobalTheory.quotPiece I e) := by
    rw [GlobalTheory.quotPiece_natCast]
    exact Module.Finite.map _ _
  let b := Module.finBasis K (GlobalTheory.quotPiece I e)
  have hlift : ∀ i, ∃ G : MvPolynomial σ K, G.IsHomogeneous e ∧
      Ideal.Quotient.mkₐ K I G = (b i : MvPolynomial σ K ⧸ I) := fun i =>
    (hQ _).1 (b i).2
  choose G hG hGb using hlift
  have hsum : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      Ideal.Quotient.mkₐ K I (∑ i, a i • G i) =
        ((∑ i, a i • b i : GlobalTheory.quotPiece I e) : MvPolynomial σ K ⧸ I) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hGb, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨G, hG, fun F hF => ?_⟩
  have hF' : Ideal.Quotient.mkₐ K I F ∈ GlobalTheory.quotPiece I e := (hQ _).2 ⟨F, hF, rfl⟩
  have hiff : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      F - ∑ i, a i • G i ∈ I ↔ (∑ i, a i • b i) = (⟨_, hF'⟩ : GlobalTheory.quotPiece I e) := by
    intro a
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk K, hsum,
      Subtype.ext_iff, eq_comm]
  refine ⟨fun i => b.repr ⟨_, hF'⟩ i, (hiff _).2 (b.sum_repr _), fun a ha => ?_⟩
  funext i
  rw [← (hiff a).1 ha, b.repr_sum_self]

theorem dimDeg_add {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    dimDeg I e + Module.finrank K (GlobalTheory.quotPiece I e) =
      Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  classical
  let H := MvPolynomial.homogeneousSubmodule σ K e
  let f : H →ₗ[K] MvPolynomial σ K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap.comp H.subtype
  have hr : LinearMap.range f = GlobalTheory.quotPiece I e := by
    rw [GlobalTheory.quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker f = (I.restrictScalars K).comap H.subtype := by
    ext x
    simp [f, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk] at hrk
  have hm : Module.finrank K ((I.restrictScalars K).comap H.subtype) =
      Module.finrank K ↥(H ⊓ I.restrictScalars K) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  unfold dimDeg
  rw [← hm, add_comm]
  exact hrk

variable {K σ : Type} [Field K] {X : Scheme.{0}}

def toPw (M : LB X) (e : ℕ) (t : (lbPow M e).Sec) : (AbLaw.pw M e).Sec where
  f := fun k => resG X (show M.U k ≤ (lbPow M e).U (fun _ => k) from
    fun _ hy => Set.mem_iInter.2 fun _ => hy) (t.f fun _ => k)
  compat := fun (i j : M.ι) => by
    have h := congrArg (resG X (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
      inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy)))
      (t.compat (fun _ => i) (fun _ => j))
    rw [map_mul] at h
    refine (AbLaw.rs_rs _ _ _).trans (((AbLaw.rs_rs _ _ _).symm.trans h).trans ?_)
    congr 1
    · have hu : res (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
          inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy))
          ((lbPow M e).g (fun _ => i) (fun _ => j)) = M.g i j ^ (e : ℤ) := by
        first
          | (change res _ (∏ _k : PUnit, _) = _
             rw [Fintype.prod_unique, map_zpow])
          | refine (congrArg (res _) (@Fintype.prod_unique PUnit _ _ _ _ _)).trans ((map_zpow _ _ _).trans ?_)
          | refine (congrArg (res _) (Fintype.prod_unique _)).trans ((map_zpow _ _ _).trans ?_)
        congr 1
        ext
        exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_self _ _)
      exact congrArg Units.val hu
    · exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_rs _ _ _).symm

theorem eventually_surj [Finite σ] [Nonempty σ] (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec) (hM : M.IsLB)
    (h : VAmp p M th) : ∀ᶠ e : ℕ in Filter.atTop, ∀ t : (lbPow M e).Sec, ∃ F : MvPolynomial σ K,
      F.IsHomogeneous e ∧ ∀ j, t.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F := by
  obtain ⟨m, ε, hε⟩ := h.exists_veryAmpleBy
  obtain ⟨t₀, ht⟩ := (AbLaw.serre_h1Zero_and_sections_polynomial).2 K X p M m (fun i => th (ε i)) hM hε
  refine Filter.eventually_atTop.2 ⟨t₀, fun e he t => ?_⟩
  obtain ⟨F, hF, hFe⟩ := ht e he (toPw M e t)
  refine ⟨MvPolynomial.rename ε F, hF.rename_isHomogeneous, fun j => ?_⟩
  have hj := hFe (j PUnit.unit)
  unfold toPw at hj
  unfold AbLaw.cst at hj
  have hrs : ∀ {U V : X.Opens} (hUV : V ≤ U), resG X hUV = AbLaw.rs X hUV := fun _ => rfl
  have hA : (lbPow M e).U j ≤ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit
  have hj' := congrArg (AbLaw.rs X hA) hj
  simp only [hrs] at hj' ⊢
  erw [AbLaw.rs_rs, AbLaw.rs_self] at hj'
  rw [hj', MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂_rename, MvPolynomial.coe_eval₂Hom]
  congr 1
  ext a
  simp only [RingHom.comp_apply, AbLaw.rs_rs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertFunction_idealOf : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  intro K σ _ _ _ X p M th hM h
  classical
  obtain ⟨hhom, -, hsec⟩ := GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power K σ X p M th hM h
  have hI : (idealOf p M th (𝟙 X)).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K) := by
    intro i r hr
    convert hhom r hr i using 1
    exact MvPolynomial.decomposition.decompose'_apply r i
  refine ⟨GlobalTheory.idealHilbertPoly (idealOf p M th (𝟙 X)), ?_⟩
  filter_upwards [GlobalTheory.eventually_finrank_quotPiece hI, eventually_surj p M th hM h] with e he hsurj
  refine ⟨Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e), ?_, he, dimDeg_add _ e⟩
  obtain ⟨G, hG, hGu⟩ := exists_forms_basis (idealOf p M th (𝟙 X)) e
  choose s hs1 hs2 hs3 using fun i => hsec e (G i) (hG i)
  have lin : ∀ (R : Type) [CommRing R] (φ : K →+* R) (v : σ → R)
      (a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K),
      MvPolynomial.eval₂ φ v (∑ i, a i • G i) = ∑ i, φ (a i) * MvPolynomial.eval₂ φ v (G i) := by
    intro R _ φ v a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPolynomial.coe_eval₂Hom, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hsumG : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K,
      (∑ i, a i • G i).IsHomogeneous e := by
    intro a
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (hG i))
  have hzero : ∀ D : MvPolynomial σ K, D.IsHomogeneous e →
      ((∀ j : (lbPow M e).ι, MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) D = 0) ↔
        D ∈ idealOf p M th (𝟙 X)) := by
    intro D hD
    obtain ⟨τ, hτ1, hτ2, -⟩ := hsec e D hD
    rw [← hτ2]
    exact forall_congr' fun j => by rw [hτ1 j]; exact Iff.rfl
  refine ⟨s, fun t => ?_⟩
  obtain ⟨F, hF, hFt⟩ := hsurj t
  obtain ⟨a, ha, hau⟩ := hGu F hF
  refine ⟨a, fun j => ?_, fun a' ha' => hau a' ?_⟩
  · have h0 := (hzero _ (hF.sub (hsumG a))).2 ha j
    rw [MvPolynomial.eval₂_sub, sub_eq_zero] at h0
    rw [hFt j, h0, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl
  · refine (hzero _ (hF.sub (hsumG a'))).1 fun j => ?_
    rw [MvPolynomial.eval₂_sub, sub_eq_zero, ← hFt j, ha' j, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl

end GlobalTheory.ZV.HilbFn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibres
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimDense

theorem exists_gen_cube_eSec {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (u : A ⟶ A) [IsMonHom u] : ∃ c : ((cubeLB A ![𝟙 A, u] L).pull (eSec A)).Gen, c.IsGen := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  have key : ∀ I, η[A] ≫ psum A ![𝟙 A, u] I = η[A] := fun I => by
    refine (psum_hom (preHom (G := A) η[A]) _ I).trans ?_
    have : (fun i => preHom (G := A) η[A] (![𝟙 A, u] i)) = fun i => (1 : (A ⟶ A) →* (𝟙_ (Over S) ⟶ A)) (![𝟙 A, u] i) := by
      funext i
      fin_cases i
      · exact (Category.comp_id _).trans e₁.symm
      · exact (IsMonHom.one_hom u).trans e₁.symm
    rw [this, ← psum_hom]
    exact e₁
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun _ : ULift.{0} (Finset (Fin 2)) => eSec A)
    (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ k => (Fintype.prod_empty _).trans (by
      have : ∑ I : ULift.{0} (Finset (Fin 2)), (-1 : ℤ) ^ (2 - I.down.card) = 0 := by decide
      have e := congrArg Additive.toMul (map_sum (zmultiplesHom (Additive U) (Additive.ofMul (k (eSec A))))
        (fun I : ULift.{0} (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)) Finset.univ)
      rw [this, map_zero, toMul_sum] at e
      exact e)) (LB.oneGen L (Y := (𝟙_ (Over S)).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact gen_chartPull (chartPullOut L _ _ (eSec A) _ fun I => congrArg (fun z => z.left) (key I.down).symm) t ht

end GlobalTheory.PrimDense

namespace GlobalTheory

theorem lbIso_cube_of_dense : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  intro hG S _ A _ _ L u hA hL hamp hrig hu hd
  have hM : (cubeLB A ![𝟙 A, u] L).IsLB := DVR.linComb_isLB _ hL _ _
  refine _root_.GlobalTheory.seesaw_reduced_of_dense hG S A L hA hL hamp S A.left (𝟙 _) (𝟙 _) A.hom (LB.div (cubeLB A ![𝟙 A, u] L) L)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (LB.isLB_div hM hL) (hd.mono ?_) (eSec A) (Over.w η[A]) ?_
  · rintro p ⟨K, _, x, G, _, _, φ, L', u', hp, h, hL', H, hu', H'⟩
    refine ⟨K, inferInstance, x, G.left, φ, G.hom, hp, h.1, ?_⟩
    have i : LBIso (cubeLB G ![𝟙 G, u'] L') ((cubeLB A ![𝟙 A, u] L).pull φ) := by
      obtain ⟨w, hw⟩ := H
      refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ _ fun I => ?_) (iso_linComb ((isGen_iff w).1 hw) _ _)
      refine psum_push h _ _ (Over.homMk φ h.1.w) (fun i => ?_) I.down
      fin_cases i
      exacts [Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm), Over.OverMorphism.ext hu']
    have a' : (cubeLB G ![𝟙 G, u'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    obtain ⟨w, hw⟩ := LBIso.trans (LB.isLB_pull hL φ) hL' (LB.isLB_pull hM φ) H.symm
      (LBIso.trans hL' a' (LB.isLB_pull hM φ) H' i)
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw
  · obtain ⟨c, hc⟩ := hrig
    obtain ⟨c', hc'⟩ := PrimDense.exists_gen_cube_eSec hL u
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ c hc c' hc'
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModel_oneModel_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  first | exact @GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | exact GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | (intros; apply GlobalTheory.Models.System.levelStructureConditions_and_splitFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelObject_fibre_from_complex_charZero : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  first | exact @GlobalTheory.PELFrom.fromC_of_isPEL | exact GlobalTheory.PELFrom.fromC_of_isPEL | (intros; apply GlobalTheory.PELFrom.fromC_of_isPEL <;> assumption)
end

