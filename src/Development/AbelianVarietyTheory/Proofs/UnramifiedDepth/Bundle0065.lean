module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingKernelLeOfSaturatedSubmodule
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.PairCount

theorem pair_kernel_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a' : ZMod d), ¬ X.big g a' → ∀ U' : Fin X.n → I (1 - g) → C, X.SatIn (1 - g) a' U' → ∀ (N : ℕ) (ψ : Fin N → J g → C), (∀ ν κ, V.Ge 0 (ψ ν κ)) → (∀ ν κ, (X.G g).ty (Sum.inr κ) ≠ a' → ψ ν κ = 0) → IndepMod V ψ → (∀ ν b, V.MM (∑ κ : J g, ∑ k : I (1 - g), ψ ν κ * X.pair g κ k * U' b k)) → N ≤ X.j := by
  intro C _ V d _ I J _ _ X g a' hs U' hU N ψ _ hp hind hk
  obtain ⟨s, hsi, hs1⟩ := X.pair_onto g
  have h := GlobalTheory.RowKernel.card_add_le (V := V) (fun k : I (1 - g) => (X.G (1 - g)).ty (Sum.inl k) = a')
    (fun ν k => ∑ κ, ψ ν κ * X.pair g κ k) U' ?_ ?_ hU.1 (fun μ k hk => hU.2 μ k hk) ?_
  · have h2 := X.rk_big (1 - g) a' ((X.big_compl g a').2 hs)
    have h3 : N + X.n ≤ X.n + X.j := by
      rw [← h2]
      convert h
    omega
  · intro c hc hm
    refine hind c hc fun κ' => ?_
    have e : ∑ ν, c ν * ψ ν κ' = ∑ k, (∑ ν, c ν * ∑ κ, ψ ν κ * X.pair g κ k) * s k κ' := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have e1 : ψ ν κ' = ∑ κ, ψ ν κ * ∑ k, X.pair g κ k * s k κ' := by
        simp [hs1]
      rw [e1]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => by ring
    rw [e]
    exact GlobalTheory.RowKernel.mm_sum fun k _ => GlobalTheory.RowKernel.mm_mul_int (hm k) (hsi k κ')
  · intro ν k hk'
    refine Finset.sum_eq_zero fun κ _ => ?_
    by_cases hκ : (X.G g).ty (Sum.inr κ) = a'
    · rw [X.pair_type g κ k (fun h => hk' (h ▸ hκ)), mul_zero]
    · rw [hp ν κ hκ, zero_mul]
  · intro ν μ
    have h := hk ν μ
    rw [Finset.sum_comm] at h
    simpa only [Finset.sum_mul] using h

end GlobalTheory.PairCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickening
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

theorem iRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  rintro R _ _ I D A G _ _ U k S _ _ χ z ⟨w, hw, hz⟩
  have t : Out.thickMap R I k G ≫ (Out.fstG I (k + 1) G).left = (Out.fstG I k G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) :=
    Over.mk (w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X).hom)
  let τ : Z ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X := Over.homMk w rfl
  let r : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left := (τ ≫ (U.gt k).i).left
  have hr : r ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans hz
  have c : r ≫ (U.gt k).pG.left = r ≫ (Out.fstG I k G).left ≫ G.hom ≫ eSec D.toPre.P.A :=
    (CharAgree.comp_q_eq_one_iff (U.gt k) (τ ≫ (U.gt k).i)).1 (by
      rw [Category.assoc, (U.gt k).isKernel.w, ← Category.assoc]
      exact congrArg (· ≫ _) (toUnit_unique _ _))
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1 + 1)))) :=
    Over.mk ((r ≫ Out.thickMap R I k G) ≫ (Out.thickObj R I (k + 1) G).hom)
  let a : Z' ⟶ Out.thickObj R I (k + 1) G := Over.homMk (r ≫ Out.thickMap R I k G) rfl
  have c' : a.left ≫ (U.gt (k + 1)).pG.left =
      a.left ≫ (Out.fstG I (k + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q k)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  let τ' := (U.gt (k + 1)).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U.gt (k + 1)) a).2 c')
  have hτ : τ' ≫ (U.gt (k + 1)).i = a := (U.gt (k + 1)).isKernel.lift_fst _ _ _
  refine ⟨τ'.left, fun x => ?_, ?_⟩
  · refine Eq.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ?_) (hw x)
    apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of S)).sheaf ⊤
    intro y hy
    choose J hJ using fun ψ : Spec (CommRingCat.of S) ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart D.toPre.P.isLB (ψ y)
    have k₀ := (TorusCoord.val_torus_point_and_translate R I D.toPre k G (U.gt k) Z τ 1 y J hJ x).1
    have k₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre (k + 1) G (U.gt (k + 1)) Z' τ' 1 y J hJ x).1
    rw [hτ] at k₁
    have e := congrArg Units.val (k₁.symm.trans ((Geo.Tor.val_pull hJ _ (Out.thickMap R I k G) r).symm.trans
      ((Geo.Tor.val_corr hJ (U.gt_t k x) r).trans k₀)))
    exact (Geo.Tor.gm_val _ _ ⊤ trivial _).symm.trans (e.trans (Geo.Tor.gm_val _ _ ⊤ trivial _))
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ.left ≫ (Out.fstG I (k + 1) G).left) hτ).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) t).trans hr)

end GlobalTheory.ChF
end

