module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaLocal

open Out ThetaPtExist

theorem exists_isThetaPtOver {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (th : LB.Sec (LPow P.A P.L 1 T))
    (hth : IsGenSec P.A P.L 1 th)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPtOver P k x v := by
  have hL := P.isLB
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T ⟶ P.A).left) (ε' := fun _ => (k : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T).left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th
  choose U hU using hU
  choose s₂ hs₂ using fun i => exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _)
    ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  choose w hw using fun i => exists_isValueAt hL (s₂ i) 1 τ hτ
  exact ⟨w, th, s₁, α, τ, U, s₂, w, 1, hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => (_root_.one_mul _).symm⟩

theorem exists_isThetaPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : Odd k)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} (x : I → (T ⟶ P.A))
    (t : SecM P.A P.L 1 T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPt P k x v := by
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  obtain ⟨th, hth⟩ := exists_isGenSec_of_retract P.isLB (overResι (T := T) ⊤) h hi t ht
  obtain ⟨w, hw⟩ := exists_isThetaPtOver P k α₀ hα₀ (fun i => overResι (T := T) ⊤ ≫ x i) th hth fun i => by
    obtain ⟨θ, hθ⟩ := hU i
    exact GlobalLift.exists_symLift_pull P.isLB _ hθ
  refine ⟨fun i => h.left.appTop.hom (w i), hk, hu, fun _ => ⟨⊤, trivial, ?_⟩⟩
  convert hw using 2 with i
  have q := congrArg (fun q => q.left.appTop.hom (w i)) hi
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
  exact q

theorem exists_generator {R M K : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton K] (b : K → M)
    (hb : Submodule.span R (Set.range b) = ⊤) : ∃ t : M, ∀ s, ∃ r : R, r • t = s := by
  rcases isEmpty_or_nonempty K with h | ⟨⟨i⟩⟩
  · refine ⟨0, fun s => ⟨0, ?_⟩⟩
    have : s ∈ Submodule.span R (Set.range b) := hb ▸ Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    rw [this, zero_smul]
  · have e : Set.range b = {b i} := by
      ext m
      exact ⟨fun ⟨j, hj⟩ => by rw [← hj, Subsingleton.elim j i]; rfl, fun hm => ⟨i, hm.symm⟩⟩
    exact ⟨b i, fun s => Submodule.mem_span_singleton.1 (by rw [← e, hb]; exact Submodule.mem_top)⟩

theorem exists_affine_isThetaPt (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {I : Type} [Finite I] (y : I → (baseOver S ⟶ P.A))
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : S) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S), IsOpenImmersion x ∧ p ∈ Set.range x ∧
      ∃ v, IsThetaPt P k (T := Over.mk x)
        (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl p
  choose V hV θ hθ using fun i => (sym S P (k ^ 2) hk.pow (baseOver S) (y i) (hy i)).1 p
  let O : S.Opens := V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(S, W) ⟶ S := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  have hl : ∀ U : S.Opens, O ≤ U → ∃ t : Sp Γ(S, W) ⟶ U.toScheme, t ≫ U.ι = x₀ := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι x₀ (by
      rw [hx₀, Scheme.Opens.range_ι]; exact hWO.trans hU), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t, ht⟩ := hl V₀ inf_le_left
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  refine ⟨Γ(S, W), inferInstance, t ≫ (overRes (T := baseOver S) V₀).hom, ?_, ?_, ?_⟩
  · rw [ex]; exact inferInstanceAs (IsOpenImmersion hW'.fromSpec)
  · rw [ex, hx₀]; exact hpW
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := exists_generator _ hsp
  refine exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map (baseAt t).hom.appTop.hom
  · obtain ⟨u, hu'⟩ := hl (V i) (inf_le_right.trans fun q hq => Set.mem_iInter.1 hq i)
    let r : baseAt t ⟶ overRes (T := baseOver S) (V i) := Over.homMk u
      (((congrArg (u ≫ ·) (Category.comp_id _)).trans hu').trans ex.symm)
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r (hθ i)
    have e : r ≫ overResι (V i) = (Over.homMk (baseAt t).hom (by simp) : baseAt t ⟶ baseOver S) :=
      Over.OverMorphism.ext (hu'.trans ex.symm)
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r n : ℕ}
    {y : Fin r → (T ⟶ A)} (hy : ∀ i, y i ^ n = 1) (a : Fin r → ℕ) : linComb y a ^ n = 1 := by
  rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem exists_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  intro h₁ h₂ o _ g N' J b S s t hN p
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN.pos.ne'⟩
  have hu : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
    rw [map_natCast, map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  haveI := t.ab.comm
  obtain ⟨R, _, x, hx, hp, v, hv⟩ := exists_affine_isThetaPt h₁.globalFns h₂.secBaseChangeAny t.pol N' hN hu t.lab
    (fun a => linComb_pow_eq_one t.torsion _) p
  refine ⟨R, inferInstance, x, fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v a), hx, hp, ?_⟩
  unfold TObj.HasTh
  convert hv using 2 with a
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (v a)

end GlobalTheory.ThetaLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open Topology TopologicalSpace

namespace GlobalTheory.TorsionDense

open RationalPoint

theorem nonempty_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (hG : IsSemiAbelian G) : Nonempty (TorusExtension G) := by
  obtain ⟨E⟩ := hG.fibres k (𝟙 _)
  let e : (Over.pullback (𝟙 (Sp k))).mapMon.obj (Mon.mk G) ≅ Mon.mk G :=
    (Functor.mapMonNatIso (Over.pullbackId (X := Sp k)) ≪≫ Functor.mapMonIdIso).app (Mon.mk G)
  let e' : (Over.pullback (𝟙 (Sp k))).obj G ≅ G := (Mon.forget _).mapIso e
  have : IsMonHom e'.hom := by
    change IsMonHom e.hom.hom
    infer_instance
  exact ⟨torusExtOfIso e' E⟩

theorem noetherianSpace_zariski {k : Type} [Field k] (X : Over (Sp k)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : @NoetherianSpace _ (zariski X) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  letI := zariski X
  exact (IsInducing.induced pt).noetherianSpace

theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k] {N₀ N : Over (Sp k)}
    [GrpObj N₀] [GrpObj N] [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] (ν : N₀ ⟶ N)
    [IsMonHom ν] [IsOpenImmersion ν.left] [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] :
    Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  letI := zariski N
  haveI := separatelyContinuousMul N
  haveI := noetherianSpace_zariski N
  have : LocallyOfFiniteType N₀.hom := by rw [← ν.w]; infer_instance
  let φ : (𝟙_ (Over (Sp k)) ⟶ N₀) →* (𝟙_ (Over (Sp k)) ⟶ N) :=
    MonoidHom.mk' (fun x => x ≫ ν) fun x y => MonObj.mul_comp x y ν
  have ho : IsOpen (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)) := by
    refine isOpen_induced_iff.2 ⟨Set.range ν.left, ν.left.isOpenMap.isOpen_range, ?_⟩
    ext y
    rw [Set.mem_preimage, ← Set.image_univ, pt_mem_image_iff ν isClosed_univ]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  have hfin : (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)).Finite := Set.finite_range φ
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set (𝟙_ (Over (Sp k)) ⟶ N))).elim_finite_subcover
    (fun g : 𝟙_ (Over (Sp k)) ⟶ N => (fun y => g * y) ⁻¹' (φ.range : Set _))
    (fun g => ho.preimage (continuous_const_mul g))
    (fun y _ => Set.mem_iUnion.2 ⟨y⁻¹, Set.mem_preimage.2 (by rw [inv_mul_cancel]; exact φ.range.one_mem)⟩)
  refine Set.finite_univ_iff.1 (Set.Finite.subset ?_ ht)
  exact t.finite_toSet.biUnion fun g _ => hfin.preimage (mul_right_injective g).injOn

theorem finite_of_isClosed_abelian
    (hno : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
      ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) →
      Finite (𝟙_ (Over (Sp k)) ⟶ A)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine hno k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
    (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

theorem exists_pow_stable {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (l : ℕ)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ^ (l ^ (a + 1)) = x ^ (l ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ^ n = z} := fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ n)
      (hpow n) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    simp only [MonObj.comp_pow, Category.comp_id, Set.mem_setOf_eq]
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl (l ^ a)⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y ^ l, K.pow_mem hy l, by rw [← pow_mul, ← pow_succ']⟩
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ^ (l ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

theorem eq_one_of_finite_range {k : Type} [Field k] [IsAlgClosed k] {G G' : Over (Sp k)} [GrpObj G]
    [GrpObj G'] [IsIntegral G.left] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom]
    (f : G ⟶ G') [IsMonHom f]
    (h : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f).Finite) : f = 1 := by
  let e : 𝟙_ (Over (Sp k)) ⟶ G' := 1
  let S : Set G'.left := ⋃ y ∈ (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f) \ {e}, {pt y}
  have hS : IsClosed S := (h.subset Set.diff_subset).isClosed_biUnion fun y _ => isClosed_pt y
  have hsub : Set.range f.left ⊆ {pt e} ∪ S := by
    refine ReducedSubgroup.range_subset_of_points f ((isClosed_pt e).union hS) fun x => ?_
    rw [range_left_subset_iff]
    by_cases hx : x ≫ f = e
    · exact Or.inl (by rw [hx]; rfl)
    · exact Or.inr (Set.mem_biUnion (x := x ≫ f) ⟨⟨x, rfl⟩, hx⟩ rfl)
  have heS : pt e ∉ S := by
    intro he
    obtain ⟨y, hy, hey⟩ := Set.mem_iUnion₂.1 he
    exact hy.2 (pt_injective hey).symm
  have hc : _root_.IsPreconnected (Set.range f.left) := isPreconnected_range f.left.continuous
  have he : pt e ∈ Set.range f.left := ⟨pt (1 : 𝟙_ (Over (Sp k)) ⟶ G), by
    rw [← pt_comp, MonObj.one_comp]⟩
  have hsub' : Set.range f.left ⊆ {pt e} := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hc _ _ (isClosed_pt e) hS hsub
      (by rw [Set.singleton_inter_eq_empty.2 heS, Set.inter_empty]) with h1 | h1
    · exact h1
    · exact absurd (h1 he) heS
  have : Subsingleton (𝟙_ (Over (Sp k))).left := inferInstanceAs (Subsingleton (Sp k))
  have : IsClosedImmersion e.left := isClosedImmersion_of_comp_eq_id _ _ e.w
  obtain ⟨t, ht⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset f.left e.left
    (hsub'.trans (by rintro _ rfl; exact ⟨_, rfl⟩))
  have ht' : t = G.hom := by
    rw [← f.w, ← ht, Category.assoc, e.w]
    exact (Category.comp_id _).symm
  have : f = toUnit G ≫ e := Over.OverMorphism.ext (by rw [← ht, ht']; rfl)
  rw [this, MonObj.comp_one]

theorem eq_one_of_torsion_comp_eq_one : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (l : ℕ), l.Prime → (l : k) ≠ 0 → ∀ f : G ⟶ G', IsMonHom f → (∀ (x : 𝟙_ (Over (Sp k)) ⟶ G), x ^ l = 1 → ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, ∀ a : ℕ, y ^ (l ^ a) = 1 → y ≫ f = 1) → f = 1 := by
  intro k _ _ G G' _ _ hG hG' l hl hlk f hf htor
  replace htor := htor 1 (one_pow l)
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := hG'.comm
  have := hG'.smooth
  have := hG'.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G') :=
    MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y f
  obtain ⟨a, ha⟩ := exists_pow_stable G l φ.ker (f.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G')})
    ((isClosed_pt _).preimage f.left.continuous) fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G' f hf inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one
      (finite_of_isClosed_abelian _root_.GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion) k G' l inferInstance inferInstance
      (nonempty_torusExtension G' hG') hl hlk _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro _ ⟨g, rfl⟩ hg
      obtain ⟨y, hy, hyg⟩ := ha (g ^ l) (by rw [MonoidHom.mem_ker, map_pow, hg])
      have h1 : φ (g / y) = 1 := htor (g / y) (a + 1) (by
        rw [div_pow, hyg, ← pow_mul, ← pow_succ', div_self'])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range f hfin

end GlobalTheory.TorsionDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
section
namespace GlobalTheory

theorem homExtension_semiAbelian_dvr : GlobalTheory.LN.HomExtSt :=
  GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.card_torsion_abelianVariety)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KCriterion

theorem mono_of_unramified_of_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := ⟨fun z => by
    let κ : Type := (pullback f f).residueField z
    let y : Sp (AlgebraicClosure κ) ⟶ pullback f f :=
      spMap (algebraMap κ (AlgebraicClosure κ)) ≫ (pullback f f).fromSpecResidueField z
    have e := h _ (y ≫ pullback.fst f f) (y ≫ pullback.snd f f)
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : (y ≫ pullback.fst f f) ≫ pullback.diagonal f = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e]
    exact ⟨(y ≫ pullback.fst f f) (IsLocalRing.closedPoint _),
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) e').trans (Scheme.fromSpecResidueField_apply z _)⟩⟩
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem triv_of_inK_local {S : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {K : Type} [CommRing K]
    [IsLocalRing K] {t : Sp K ⟶ S} {x : Over.mk t ⟶ A} (hx : InK A M x) : Triv (Out.translDiff A M x) := by
  obtain ⟨V, hp, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  have := exists_isGen_translDiff_comp A M x (𝟙 _) V (fun q => hV.ge trivial) c hc
  rwa [Category.id_comp] at this

theorem kTriv_of_points_of_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  intro hL R _ A _ _ hA hP M hM hK
  obtain ⟨hO, -, hT⟩ := TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns R A hA hP M (pw M 0) hM hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ A), InK A M x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hT _ rfl T x).trans (hH T x)
  have := hA.proper
  have hft : LocallyOfFiniteType H.hom := by rw [← Over.w j]; infer_instance
  have hpt : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    exact fun y => (hK k).1 (y ≫ j) (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
  have htan : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R)
      (y : Over.mk (TangentCrit.dualBase k ≫ t) ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    have e : TangentCrit.dualBase k ≫ Spec.map φ = spMap (algebraMap R (DualNumber k)) :=
      (Spec.map_comp _ _).symm
    rw [e]
    intro y
    refine (hK k).2 (y ≫ j) ?_ (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
    rw [← Category.assoc]
    exact hpt k _ _
  have hext : ∀ {T : Scheme.{0}} {t : T ⟶ Sp R}, (∀ y : Over.mk t ⟶ H, y ≫ j = 1) →
      ∀ w w' : T ⟶ H.left, w ≫ H.hom = t → w' ≫ H.hom = t → w = w' := fun h w w' e e' =>
    (cancel_mono j.left).1 (congrArg (fun q => q.left)
      ((h (Over.homMk w e)).trans (h (Over.homMk w' e')).symm))
  have hu : FormallyUnramified H.hom :=
    TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw =>
      hext (htan k (TangentCrit.dualPt k ≫ w ≫ H.hom)) _ _ hw (by simp only [Category.assoc])
  have hm : Mono H.hom := mono_of_unramified_of_geometric_points H.hom fun k _ _ y y' e =>
    hext (hpt k (y' ≫ H.hom)) _ _ e rfl
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  obtain ⟨y', hy'⟩ := (hrep T 1).1 (inK_one hM T)
  have : y = y' := Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w y').symm))
  rw [this, hy']

end GlobalTheory.KCriterion
end

