module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocPt

theorem main : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ _ f hf

  have hord : GlobalTheory.OrdLoc.ordIdeal D U.r.hom ≤ GlobalTheory.OrdLoc.IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hdiv : (l : U.R) ∣ GlobalTheory.OrdLoc.del D U.r.hom :=
    ⟨GlobalTheory.OrdLoc.dd D U.r.hom 0 * GlobalTheory.OrdLoc.dd D U.r.hom 1, by unfold GlobalTheory.OrdLoc.del; ring⟩
  have hsat : ∀ a, GlobalTheory.OrdLoc.del D U.r.hom * a ∈ GlobalTheory.OrdLoc.IY D U → a ∈ GlobalTheory.OrdLoc.IY D U := by
    rintro a ⟨n, hn⟩
    exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩
  obtain ⟨B', _, _, _, _, _, _, _, _, f', q, hJ, hqf, hkill⟩ :=
    GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal U.R (GlobalTheory.OrdLoc.IY D U) (GlobalTheory.OrdLoc.del D U.r.hom) hdiv hsat B f hf
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  obtain ⟨hnat, -, hdel⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D f' U.r.hom
  have hzero : GlobalTheory.OrdLoc.ordIdeal D (push f' U.r.hom) = ⊥ := by
    rw [← hnat, Ideal.map_eq_bot_iff_le_ker]
    exact hord.trans hJ
  have hmult' : HasMult D.η (push f' U.r.hom) := fun g => U.r.hasMult g
  have hcont' : ∀ a b, QCont l fun g => (push f' U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B' f').1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  obtain ⟨h, ρ, κ, x, y, z, hρ, hκc, hκI, hz, hρM, hx, hy, hσd⟩ :=
    GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot D B' (push f' U.r.hom) hmult' hcont' hzero
  obtain ⟨⟨hσ, hcl⟩, -⟩ := _root_.GlobalTheory.OrdLoc.fr_isFr D
  obtain ⟨-, -, hφ, -, -⟩ := _root_.GlobalTheory.OrdLoc.hl_basic D
  obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩⟩ := hσd hσ
  have hdel' : f' (GlobalTheory.OrdLoc.del D U.r.hom) = (l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 *
      GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1 := hdel
  have hcr := _root_.GlobalTheory.tri_crys_push hP D.HL.subtype hφ q D.e D.e_pos κ hκc hκI x y z ρ hz hρM hx hy ⟨_, hσ⟩ hcl
    (fun b hb => hkill b (by
      have hb' : ((((κ 0 / κ 1) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv0]
      linear_combination ((l : B') * (v0 : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1) * hb'))
    (fun b hb => hkill b (by
      have hb' : ((((κ 1 / κ 2) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv1]
      linear_combination ((l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 * (v1 : B')) * hb'))
  have hmult : HasMult D.η (push f U.r.hom) := fun g => U.r.hasMult g
  have hcont : ∀ a b, QCont l fun g => (push f U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  have hqf' : (q : B' →+* B).comp (f' : U.R →+* B') = (f : U.R →+* B) := RingHom.ext hqf
  refine GlobalTheory.T.isLCrystalline_conjBy_invariant D B (push f U.r.hom) (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) hmult hcont
    ⟨(Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ, fun g => ?_, hcr⟩
  have e1 : GG.map (q : B' →+* B) (conjBy h (push f' U.r.hom) (g : GQ l)) =
      conjBy (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) (push f U.r.hom) (g : GQ l) := by
    simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      GG.map_map, hqf']
    congr 2 <;> simp [GG.ofGL, GG.map, SemidirectProduct.map_inl]
  rw [MonoidHom.comp_apply, hρ g, ← e1]
  rfl

end GlobalTheory.OrdLocPt
