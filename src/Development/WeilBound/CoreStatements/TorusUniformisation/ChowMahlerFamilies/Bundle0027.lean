module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StratumGenericTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.StratumGenericTorsion

noncomputable def rk {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (τ : TorusExtension G) : ℕ :=
  letI := τ.addCommGroup; Module.finrank ℤ τ.X

theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] {K K' : Type} [Field K] [Field K'] (x : Sp K ⟶ S)
    (τ : TorusExtension ((Over.pullback x).obj G)) (e : K →+* K') :
    ∃ τ' : TorusExtension ((Over.pullback (spMap e ≫ x)).obj G), rk τ' = rk τ := by
  haveI : IsMonHom (pullCompIso (spMap e) x G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso (spMap e) x G).inv)
  exact ⟨torusExtOfIso (pullCompIso (spMap e) x G).symm
    (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC (spMap e) τ), rfl⟩

theorem card_field (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ)
    (hG : IsSemiAbelian G) (dG : SmoothOfRelativeDimension g G.hom) (h2 : ((2 : ℕ) : k) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ 2 = 1} * 2 ^ rk E = 2 ^ (2 * g) := by
  rw [← GlobalTheory.card_torsion_mul_card_toric_torsion k G E g 2 hG dG h2]
  congr 1
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  have hk := E.isKernel
  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X
  obtain ⟨-, hcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e 2 h2
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  refine hcard.symm.trans ?_
  refine Nat.card_eq_of_bijective
    (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · rintro ⟨x, hx, t, rfl⟩
    have hx₁ : i t ^ 2 = 1 := hx
    exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩

theorem card_point {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (k : Type) [Field k] [IsAlgClosed k] (h2 : ((2 : ℕ) : k) ≠ 0)
    (t : Sp k ⟶ S) (E : TorusExtension ((Over.pullback t).obj G)) :
    Nat.card {x : Over.mk t ⟶ G // x ^ 2 = 1} * 2 ^ rk E = 2 ^ (2 * g) := by
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) dG
  rw [← card_field k _ E g (IsSemiAbelian.pullback t G hG) hg' h2]
  congr 1
  let e := GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ 2 = 1 ↔ e x ^ 2 = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem exists_points {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S)
    (τ : TorusExtension ((Over.pullback x).obj G)) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), FiniteDimensional K K' ∧
      ∀ y : Sp K' ⟶ S, y = spMap (algebraMap K K') ≫ x →
        ∃ (τ' : TorusExtension ((Over.pullback y).obj G)) (m : ℕ) (P : Fin m → (Over.mk y ⟶ G)),
          Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ m * 2 ^ rk τ' = 2 ^ (2 * g) := by
  let F := AlgebraicClosure K
  haveI := hG.smooth
  obtain ⟨τF, hτF⟩ := exists_ext G x τ (algebraMap K F)
  have hc := card_point G hG g dG F (by exact_mod_cast (two_ne_zero : (2 : F) ≠ 0)) _ τF
  rw [hτF] at hc
  have hne : Nat.card {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc
    exact (pow_ne_zero _ two_ne_zero) hc.symm
  haveI := Nat.finite_of_card_ne_zero hne
  let u := (Finite.equivFin {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1}).symm
  choose T hT using fun j => GlobalTheory.TorsionRat.exists_finset_over G x (u j).1
  let s : Set F := ⋃ j, (T j : Set F)
  haveI : Finite s := (Set.finite_iUnion fun j => (T j).finite_toSet).to_subtype
  let L := IntermediateField.adjoin K s
  refine ⟨L, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  rintro y rfl
  obtain ⟨τ', hτ'⟩ := exists_ext G x τ (algebraMap K L)
  choose P hP using fun j =>
    hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))
  let c₀ : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ Over.mk (spMap (algebraMap K L) ≫ x) :=
    Over.homMk (spMap (algebraMap L F)) (by
      change spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x = spMap (algebraMap K F) ≫ x
      rw [← Category.assoc, GlobalTheory.TorsionRat.sp_comp]
      rfl)
  have hc₀ : ∀ j, c₀ ≫ P j = (u j).1 := fun j => Over.OverMorphism.ext (hP j)
  refine ⟨τ', _, P, fun a b h => u.injective (Subtype.ext ?_), fun j => ?_, ?_⟩
  · rw [← hc₀, ← hc₀, h]
  · refine GlobalTheory.TorsionRat.comp_injective (algebraMap L F) c₀ rfl ?_
    rw [MonObj.comp_pow, hc₀, (u j).2, MonObj.comp_one]
  · rw [hτ']
    exact hc

end PositivityTheory.Xgn.StratumGenericTorsion

open PositivityTheory.Xgn.StratumGenericTorsion in
theorem PositivityTheory.Xgn.stratum_generic_torsion_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) := by
  intro S G _ hG g dG L _ _ z
  obtain ⟨L₁, _, _, h₁, ⟨τ₁⟩⟩ := exists_finite_torusExtension_fibre S G hG L z
  haveI : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap L L₁).injective
  obtain ⟨K, _, _, h₂, H⟩ := exists_points G hG g dG L₁ _ τ₁
  letI : Algebra L K := ((algebraMap L₁ K).comp (algebraMap L L₁)).toAlgebra
  haveI : IsScalarTower L L₁ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K, inferInstance, inferInstance, Module.Finite.trans L₁ K, ?_⟩
  exact H _ (by rw [← Category.assoc, GlobalTheory.TorsionRat.sp_comp])
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionRankBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.ToricTorsionRankBounds

theorem card_toric_torsion (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (N : ℕ) (hN : (N : k) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
      N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  have hk := E.isKernel
  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X
  obtain ⟨-, hcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e N hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  rw [← hcard]
  refine (Nat.card_eq_of_bijective
    (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
  · intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · rintro ⟨x, hx, t, rfl⟩
    have hx₁ : i t ^ N = 1 := hx
    exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩

theorem bound_algClosed (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (g N : ℕ) (hG : IsSemiAbelian G) (hg : SmoothOfRelativeDimension g G.hom)
    (hN : (N : k) ≠ 0) (m : ℕ) (P : Fin m → (𝟙_ (Over (Sp k)) ⟶ G)) (hP : Function.Injective P)
    (hP' : ∀ i, P i ^ N = 1) :
    m * N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ ≤ N ^ (2 * g) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have h := GlobalTheory.card_torsion_mul_card_toric_torsion k G E g N hG hg hN
  rw [card_toric_torsion k G E N hN] at h
  have hne : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact pow_ne_zero _ hN0 h.symm
  haveI := Nat.finite_of_card_ne_zero hne
  have hm : m ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} := by
    have := Nat.card_le_card_of_injective
      (fun i : Fin m => (⟨P i, hP' i⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1}))
      (fun a b hab => hP (congrArg Subtype.val hab))
    simpa using this
  rw [← h]
  exact Nat.mul_le_mul_right _ hm

end PositivityTheory.Xgn.ToricTorsionRankBounds

theorem PositivityTheory.Xgn.two_torsion_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  intro S G _ hG g hg k _ h2 x Gk _ ψ hψ τ m Q hQ hQ2
  let Ω := AlgebraicClosure k
  let f : Sp Ω ⟶ Sp k := spMap (algebraMap k Ω)
  haveI : Flat f := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  haveI : Surjective f := ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  haveI : Epi f := Flat.epi_of_flat_of_surjective f
  have hp := isGrpPullback_pullback G (f ≫ x)
  obtain ⟨e, he, -⟩ := grpPullback_iso ((isGrpPullback_pullback Gk f).comp hψ) hp
  haveI := he
  let E : TorusExtension ((Over.pullback (f ≫ x)).obj G) :=
    torusExtOfIso e (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC f τ)
  have hg' : SmoothOfRelativeDimension g ((Over.pullback (f ≫ x)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h2' : ((2 : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).2 h2
  have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    intro a b hab
    have e : a.left ≫ pullback.fst G.hom (f ≫ x) = b.left ≫ pullback.fst G.hom (f ≫ x) :=
      congrArg (fun z => z.left) hab
    exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w a).trans (Over.w b).symm))
  let U : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ f ≫ x) ⟶ Over.mk x :=
    Over.homMk f (Category.id_comp (f ≫ x)).symm
  let P : Fin m → (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback (f ≫ x)).obj G) := fun i =>
    Over.homMk (hp.1.lift (U ≫ Q i).left (𝟙_ (Over (Sp Ω))).hom (Over.w (U ≫ Q i))) (hp.1.lift_snd _ _ _)
  have hP : ∀ i, pushHom hp (𝟙_ (Over (Sp Ω))) (P i) = preHom U (Q i) := fun i =>
    Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  refine PositivityTheory.Xgn.ToricTorsionRankBounds.bound_algClosed Ω _ E g 2 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f ≫ x) G hG) hg' h2' m P ?_ ?_
  · intro a b hab
    have h1 : preHom U (Q a) = preHom U (Q b) := by rw [← hP, ← hP, hab]
    have h3 : f ≫ (Q a).left = f ≫ (Q b).left := congrArg (fun z => z.left) h1
    exact hQ (Over.OverMorphism.ext ((cancel_epi f).1 h3))
  · intro i
    apply hinj
    rw [map_pow, hP, ← map_pow, hQ2, map_one, map_one]
end

