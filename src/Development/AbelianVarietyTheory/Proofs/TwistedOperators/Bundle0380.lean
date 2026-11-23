module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0371
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix
open scoped Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeilLevelStab

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho GlobalTheory.Mem.CoefInv

variable {D : D7}

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem actO_one_mul (S T : HSp D) (k k' : GA D T) (x : WO S T) :
    actO S T 1 (k * k') x = actO S T 1 k (actO S T 1 k' x) := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, Matrix.mul_assoc]

theorem actO_nsmul (S T : HSp D) (g : GA D S) (h : GA D T) (c : ℕ) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x :=
  map_nsmul (GlobalTheory.LatLevel.actHom S T g h) c x

def MovesMod (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) (k : GA D T) : Prop :=
  ∀ x ∈ L, ∃ l ∈ L, actO S T 1 k x = x + c • l

theorem movesMod_one (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : MovesMod S T L c 1 :=
  fun x _ => ⟨0, zero_mem _, by rw [actO_one_one, smul_zero, add_zero]⟩

theorem movesMod_mul {S T : HSp D} {L : AddSubgroup (WO S T)} {c : ℕ} {k k' : GA D T}
    (hk : MovesMod S T L c k) (hk' : MovesMod S T L c k') : MovesMod S T L c (k * k') := by
  intro x hx
  obtain ⟨l', hl', e'⟩ := hk' x hx
  obtain ⟨l, hl, e⟩ := hk x hx
  obtain ⟨l'', hl'', e''⟩ := hk l' hl'
  refine ⟨l + (l' + c • l''), add_mem hl (add_mem hl' (AddSubgroup.nsmul_mem _ hl'' c)), ?_⟩
  rw [actO_one_mul, e', GlobalTheory.LatNhds.actO_add, actO_nsmul, e, e'']
  simp only [smul_add]
  abel

def stabK (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : Subgroup (GA D T) where
  carrier := {k | MovesMod S T L c k ∧ MovesMod S T L c k⁻¹}
  one_mem' := ⟨movesMod_one S T L c, by rw [inv_one]; exact movesMod_one S T L c⟩
  mul_mem' := fun ha hb => ⟨movesMod_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact movesMod_mul hb.2 ha.2⟩
  inv_mem' := fun ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isOpen_stabK (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (c : ℕ) (hc : 0 < c) :
    IsOpen ((stabK S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) c : Subgroup (GA D T)) : Set (GA D T)) := by
  have h := eventually_mod ΛS ΛT hS hT c hc
  have ht : Filter.Tendsto (fun k : GA D T => ((1 : GA D S), k)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const (y := (1 : GA D S))).prodMk continuous_id).tendsto (1 : GA D T)
    exact this
  have ti : Filter.Tendsto (fun k : GA D T => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D T)).tendsto 1
    rwa [inv_one] at this
  have h1 := ht.eventually h
  have h2 := ti.eventually h1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [h1, h2] with k hk hk'
  exact ⟨hk, hk'⟩

theorem exists_level_stab_of_selfDual (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧
      (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 →
        actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
        actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧
          ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hLdef
  obtain ⟨n, hn, hnU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  obtain ⟨hdual, happrox, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  refine ⟨L.map (nsmulAddMonoidHom n), stabK S T L (2 * n * n), ?_,
    isOpen_stabK S T ΛS ΛT hS hT (2 * n * n) (by positivity), ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hnU u hu
  · intro x
    obtain ⟨ρ, hρ, u, hu, hf⟩ := happrox (x - realIdem D • x) (fin_part x)
    refine ⟨ρ, hρ, ?_⟩
    rintro _ ⟨l, hl, rfl⟩ -
    have hnl : n • l ∈ L := AddSubgroup.nsmul_mem _ hl n
    have e : x - ρ = (realIdem D • x + (x - realIdem D • x - ρ - u)) + u := by abel
    show ψ (symplO S T (x - ρ) (n • l)) = 1
    rw [e, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      symplO_real_fin S T (real_part x) (latO_fin hnl), symplO_real_fin S T hf (latO_fin hnl), zero_add, zero_add]
    exact (hdual u (latO_fin hu)).1 hu _ hnl
  · rintro k ⟨hk, -⟩ - _ ⟨l, hl, rfl⟩ -
    obtain ⟨l', hl', e⟩ := hk l hl
    have hm : l + (2 * n * n) • l' ∈ L := add_mem hl (AddSubgroup.nsmul_mem _ hl' _)
    have e2 : actO S T 1 k (n • l) = n • (l + (2 * n * n) • l') := by rw [actO_nsmul, e]
    refine ⟨⟨_, hm, e2.symm⟩, ?_⟩
    show (actO S T 1 k (n • l)).map (infPart D) = 0
    rw [e2]
    exact latO_fin (AddSubgroup.nsmul_mem _ hm n)
  · rintro k ⟨hk, -⟩ hkf w hw
    have hw' : ∀ l ∈ L, ψ (symplO S T (n • w) l) = 1 := fun l hl => by
      rw [symplO_nsmul]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))
    have hff : (n • w - realIdem D • (n • w)).map (infPart D) = 0 := fin_part _
    have hfL : n • w - realIdem D • (n • w) ∈ L := GlobalTheory.LatVac.mem_of_char hψ hS hT hff fun u hu => by
      rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_real_fin S T (real_part _) (latO_fin hu), sub_zero]
      exact hw' u hu
    obtain ⟨l, hl, e⟩ := hk _ hfL
    have hreal := actO_real (one_mem (GfC S)) hkf (real_part (n • w))
    have e1 : actO S T 1 k w = w + 2 • (n • l) := by
      refine nsmul_cancel hn ?_
      rw [← actO_nsmul, show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel,
        GlobalTheory.LatNhds.actO_add, hreal, e, ← add_assoc, ← show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel]
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      ring
    have hd : actO S T 1 k w - w = 2 • (n • l) := by rw [e1, add_sub_cancel_left]
    refine ⟨⟨2 • l, AddSubgroup.nsmul_mem _ hl 2, ?_⟩, ?_, ?_⟩
    · rw [hd]
      exact smul_comm n 2 l
    · rw [hd]
      exact latO_fin (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl n) 2)
    · rw [hd, two_nsmul, symplOH_add_right, symplOH_add_self]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))

theorem exists_level_stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  intro D ψ S T hψ U hU
  exact exists_level_stab_of_selfDual ψ S T hψ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) U hU

end GlobalTheory.WeilLevelStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLiftKer
section
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerLat

theorem ex_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (n : ℕ) (w : Fin g → ℂ) :
    F.ex i P (n • w) = F.ex i P w ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have := (F.ex_ker i P hP 0).2 (zero_mem _)
    exact this
  | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]

theorem exists_lift_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → Formalism.L2.Pj.IsHkIsog p (F.u i P) (F.u j P') C ψ ψp →
  ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
    (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ (∀ z, F.ex j P' (h z) = ψp (F.ex i P z)) ∧
    (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ ∃ b, gam a = (p ^ 2) • b) ∧
    ∀ c ∈ C, ∃ a, c = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  have hker : ψp.ker = C := hI.2.2.2.2.2.1
  have hp0 : ((p : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨gam, h, h1, h2, h3, h4, fun a => ?_, fun c hc => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ← h4, map_smul, ← h2, F.ex_ker j P' hP']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hP'.2.1 ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hp0, one_smul]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [hb, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hp0, one_smul]
  · obtain ⟨w, rfl⟩ := F.ex_onto i P hP c
    have e1 : F.ex i P ((p ^ 2) • w) = 1 := by rw [ex_nsmul F i P hP, hC _ hc]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 e1
    refine ⟨a, congrArg _ ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hp0, one_smul]

end GlobalTheory.HeckeKerLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem isAbelianScheme_fib {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : IsAbelianScheme (Fib Xo x) :=
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem exists_fibPtsEquiv {K : Type} [Field K] (x : Sp K ⟶ Xo.X) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Fib Xo x) ≃* (Over.mk x ⟶ Xo.univ.t.G),
      (∀ u, fibPt _ (ρ u) = u.left) ∧
      ∀ (g : Xo.univ.t.G ⟶ Xo.univ.t.G) u, ρ (u ≫ (Over.pullback x).map g) = ρ u ≫ g := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv (isGrpPullback_pullback Xo.univ.t.G x) (𝟙_ (Over (Sp K))) x
    (Category.id_comp _)
  refine ⟨ρ, fun u => ?_, fun g u => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ]
    · rw [fibPt, pullback.lift_snd]
      exact (Over.w u).symm
  · have A : ((Over.pullback x).map g).left ≫ pullback.fst _ x = pullback.fst _ x ≫ g.left :=
      pullback.lift_fst _ _ _
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) A

theorem exists_hkWith_of_hkRelFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  intro E _ _ _ H Dw l Xo c P p i ⟨hP, hco, hp, hpP, hpM⟩ Ω _ _ _ y C z ⟨ψ, ψp, h, hLie, hTr⟩
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM C.2 h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib y.x
  have hB := isAbelianScheme_fib z.x
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv y.x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv z.x
  let f : Fib Xo y.x ⟶ Fib Xo z.x := Over.homMk ψ h0
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo y.x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C.1 := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    refine ρ.injective ?_
    rw [map_pow, map_one]
    refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => C.2.2.2.1 hx a ?_
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
    rw [sq, Nat.cast_mul]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo y.x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo y.x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo y.x) ^ m) (𝟙 _) ≫ μ[Fib Xo y.x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo y.x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨f, π, ⟨hom, homπ, hπ, ?_, lin, fun a => ?_⟩, hLie, hTr⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

end GlobalTheory.HkIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalMatrixChartSplitIdempotentCompletion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HatLocalChart

open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨b, hb, x, rfl⟩ := ha'
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, w, hw, rfl⟩ := hz
      apply AddSubgroup.subset_closure
      refine ⟨b * c, fun v => ?_, x • w, L.smul_mem x hw, ?_⟩
      · have hbv := hb v
        simp only [Formalism.MainNotions.StandardLattice.intAf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Set.mem_setOf_eq] at hbv
        exact mul_mem hbv (hc v)
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a₁ a₂ _ _ h₁ h₂ => rw [add_smul]; exact add_mem h₁ h₂
  | neg a _ h => rw [neg_smul]; exact neg_mem h


set_option maxHeartbeats 1000000 in
theorem exists_chart : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D e v π s n L he h1 h2 h3 hfg hspan
  have hπ1 : π (finPart D e) = 1 := by
    have h := h2 1
    rw [map_one, mul_one] at h
    rw [← h, h1 1]
  have heint : finPart D e ∈ intAE D := by
    have h := (h3 1).2 (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at h
  have hπint : ∀ x ∈ intAE D, π x ∈ Formalism.UG.Ov D.host.F v := fun x hx =>
    (h3 x).1 (GlobalTheory.SplitLatBasis.mul_mem_intAE D heint hx)
  have hone : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) w ∈ w.adicCompletionIntegers D.host.F :=
    fun w => one_mem (w.adicCompletionIntegers D.host.F)
  obtain ⟨g, hg⟩ := hfg
  let O := v.adicCompletionIntegers D.host.F
  let gen : ↥(g : Set (Fin n → D.host.E)) → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (j : Fin n → D.host.E) i
  let N : Submodule O (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    Submodule.span O (Set.range fun j i => π (gen j i))

  have hL : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, a w ∈ w.adicCompletionIntegers D.host.F) →
      ∀ x ∈ L, (fun i => π (a ⊗ₜ[D.host.F] x i)) ∈ N := by
    intro a ha x hx
    have haE : a ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, by simp⟩
    rw [← hg] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hx' : (fun i => π (a ⊗ₜ[D.host.F] x i)) =
          (⟨π (a ⊗ₜ[D.host.F] (1 : D.host.E)), hπint _ haE⟩ : O) • (fun i => π (gen ⟨x, hx⟩ i)) := by
        funext i
        show π (a ⊗ₜ[D.host.F] x i) = π (a ⊗ₜ[D.host.F] (1 : D.host.E)) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx']
      exact N.smul_mem _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    | zero =>
      convert N.zero_mem using 1 <;> ext i <;> simp
    | add x y _ _ hx hy =>
      convert N.add_mem hx hy using 1
      funext i
      simp [TensorProduct.tmul_add]
    | smul c x _ hx =>
      have hc : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      convert N.smul_mem (⟨π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)), hπint _ hc⟩ : O) hx using 1
      funext i
      show π (a ⊗ₜ[D.host.F] ((c : D.host.E) * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * π (a ⊗ₜ[D.host.F] x i)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hz : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), (fun i => π (z i)) ∈ N := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact hL a ha x hx
    | zero =>
      convert N.zero_mem using 1 <;> ext i <;> simp
    | add z₁ z₂ _ _ h₁ h₂ =>
      convert N.add_mem h₁ h₂ using 1 <;> ext i <;> simp
    | neg z _ h =>
      convert N.neg_mem h using 1 <;> ext i <;> simp
  have hgen : ∀ j, gen j ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := fun j =>
    AddSubgroup.subset_closure ⟨1, hone, j, hg ▸ Submodule.subset_span j.2, rfl⟩
  have hiff : ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔ (fun j => π (y j)) ∈ N := by
    intro y
    constructor
    · intro hy
      convert hz _ hy using 1
      funext j
      show π (y j) = π (finPart D e * y j)
      rw [map_mul, hπ1, one_mul]
    · intro hy
      have hs := GlobalTheory.SplitLatBasis.section_mem O π (fun a => finPart D (s a)) (finPart D e) (intAE D)
        (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) h1 h2 (fun x hx => (h3 x).2 hx)
        (fun a ha y hy => smul_mem_hat D L ha hy) gen hgen _ hy
      convert hs using 1
      funext j
      exact (h2 (y j)).symm
  have hfin : N.FG := Submodule.fg_span (Set.finite_range _)
  have htop : Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
      (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)) = ⊤ := by
    set S := Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    have hΦ : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)),
        (fun i => π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL 1 hone x hx)
      | zero =>
        convert S.zero_mem using 1 <;> ext i <;> simp
      | add x y _ _ hx hy =>
        convert S.add_mem hx hy using 1
        funext i
        simp [TensorProduct.tmul_add]
      | smul c x _ hx =>
        convert S.smul_mem (π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c)) hx using 1
        funext i
        show π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [Submodule.eq_top_iff']
    intro w
    rw [pi_eq_sum_univ w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    convert hΦ (fun j => if i = j then 1 else 0) (by rw [hspan]; trivial) using 1
    funext j
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [TensorProduct.tmul_zero, map_zero]
  haveI : Submodule.IsLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := Submodule.IsLattice.of_fg _ hfin
  haveI : Submodule.IsFullLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := ⟨htop⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_matrix_of_isLattice (R := O) N
  refine ⟨B, fun y => (hiff y).trans ((hB _).trans (forall_congr' fun i => ?_))⟩
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact r.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end GlobalTheory.HatLocalChart
end
end

