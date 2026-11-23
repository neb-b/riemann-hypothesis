module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section
namespace GlobalTheory.BaseVec

theorem coeff_conj_of_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

section Levels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem baseLevelDatum_level_eq (P' : LevelP R.Pg D.R.r ℂ) : (R.dat0 P').P = P' := by
  simp [LevCh.dat0, datY]

theorem mem_levS (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    x ∈ levS _ (R.βY 0) (R.dat0 P') ↔ x ∈ GfC (Yc D 0) ∧ finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) ∈ P'.H := by
  show x ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P') ∧
      rTup (R.βY 0) (R.dat0 P') (finE (Yc D 0) x) ∈ (R.dat0 P').P.H) ↔ _
  rw [baseLevelDatum_level_eq]
  rfl

theorem principalRowLevelCharacter_trivial (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    levChi _ (R.βY 0) (R.dat0 P') x = ((ext1 P'.H P'.chi (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x)) : ℂˣ) : ℂ) := by
  simp [levChi, levFn, LevCh.dat0, datY]
  rfl

theorem conj_mem_principal {x y : GA D (Yc D 0)} (hx : x ∈ levS _ (R.βY 0) (R.dat0 R.triv)) (hy1 : y ∈ GfC (Yc D 0))
    (hy2 : finE (Yc D 0) y ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    y⁻¹ * x * y ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS] at hx ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hyi := Subgroup.inv_mem _ hy2
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hy1) hx1) hy1, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyi hx2) hy2
  · rw [map_mul, map_mul, map_inv, rTup_mul (Subgroup.mul_mem _ hyi hx2) hy2, rTup_mul hyi hx2, rTup_inv hy2]
    have : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) = 1 := Subgroup.mem_bot.1 hx3
    rw [this, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem lift_div_principal {g0 : G0 R.Pg D.R.r} {κ κ' : GA D (Yc D 0)}
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hκ' : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ') :
    κ⁻¹ * κ' ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS]
  have hi := Subgroup.inv_mem _ hκ.2.1
  refine ⟨(GfC _).mul_mem ((GfC _).inv_mem hκ.1) hκ'.1, ?_, ?_⟩
  · rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hi hκ'.2.1
  · refine Subgroup.mem_bot.2 ?_
    rw [map_mul, map_inv, rTup_mul hi hκ'.2.1, rTup_inv hκ.2.1, hκ.2.2, hκ'.2.2]
    exact inv_mul_cancel g0

end Levels


open Formalism.IndefR.principalLevelFrame in
theorem exists_base_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hne n PY π v hvS hv0 hvT hgood
  classical
  have hL := GlobalTheory.DimFull.liftsY' hC
  have hex : ∀ g : G, ∃ κ : Formalism.AUTREP.GAf D.host.E n,
      IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ κ) := by
    intro g
    obtain ⟨κ, hκ⟩ := hL (R.eG g)
    obtain ⟨h, rfl⟩ := PY.onto κ hκ.1
    exact ⟨h, hκ⟩
  choose k hk using hex
  set J0 := PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv) with hJ0
  have hvfix : ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c v = v := fun c hc => by
    simpa using hvT c hc
  set Ws : Submodule ℂ (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
    Submodule.span ℂ (Set.range fun g => Formalism.L2.NG.rt D.host.E n (k g) v) with hWs
  have hfix : ∀ w ∈ Ws, ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c w = w := by
    intro w hw c hc
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have hc' : (k g)⁻¹ * c * k g ∈ J0 := by
        rw [hJ0, Set.mem_preimage]
        rw [map_mul, map_mul, map_inv]
        exact GlobalTheory.BaseVec.conj_mem_principal R hc (hk g).1 (hk g).2.1
      rw [rt_rt, show c * k g = k g * ((k g)⁻¹ * c * k g) by group, ← rt_rt, hvfix _ hc']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hprod : ∀ g h, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) (Formalism.L2.NG.rt D.host.E n (k h) w) =
      Formalism.L2.NG.rt D.host.E n (k (g * h)) w := by
    intro g h w hw
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * h)) (PY.ψ (k g * k h)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul]; exact (GfC _).mul_mem (hk g).1 (hk h).1
      · rw [map_mul, map_mul]; exact Subgroup.mul_mem _ (hk g).2.1 (hk h).2.1
      · rw [map_mul, map_mul, rTup_mul (hk g).2.1 (hk h).2.1, (hk g).2.2, (hk h).2.2]
        exact (map_mul R.eG g h).symm
    have hc : (k (g * h))⁻¹ * (k g * k h) ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk (g * h)) hl
    rw [rt_rt, show k g * k h = k (g * h) * ((k (g * h))⁻¹ * (k g * k h)) by group, ← rt_rt, hfix w hw _ hc]
  have hk1 : k 1 ∈ J0 := by
    rw [hJ0, Set.mem_preimage, GlobalTheory.BaseVec.mem_levS]
    refine ⟨(hk 1).1, (hk 1).2.1, Subgroup.mem_bot.2 ?_⟩
    rw [(hk 1).2.2]
    exact map_one R.eG
  have hvWs : v ∈ Ws := by
    have : Formalism.L2.NG.rt D.host.E n (k 1) v ∈ Ws := Submodule.subset_span ⟨1, rfl⟩
    rwa [hvfix _ hk1] at this
  have hstab : ∀ g, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) w ∈ Ws := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hprod g h v hvWs]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ws.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Ws.smul_mem a hx
  let ρ : Representation ℂ G Ws :=
    { toFun := fun g => (Formalism.L2.NG.rt D.host.E n (k g)).restrict (fun w hw => hstab g w hw)
      map_one' := LinearMap.ext fun w => Subtype.ext (hfix w w.2 _ hk1)
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (hprod g h w w.2).symm }
  haveI : FiniteDimensional ℂ Ws := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hX : ∀ χ ∈ A.X, IsAbsIrrChar χ := hOk.irr
  have hcen : ∀ g h : G, RealDat.eC (A := A) D.what₂.embLL (g * h * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL h := fun g h => by
    unfold RealDat.eC
    rw [GlobalTheory.BaseVec.coeff_conj_of_central _ (fun b => idemOf_central A.X hX b) g h]
  have hgoodv : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) v = v := hgood k hk
  have hgoodW : ∀ w ∈ Ws, ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      simp only [hprod _ h v hvWs]
      conv_rhs => rw [← hgoodv]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, hprod h _ v hvWs]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcen, show h * (h⁻¹ * g * h⁻¹⁻¹) = g * h by group]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      simp only [map_smul]
      simp only [smul_comm _ a, ← Finset.smul_sum, hx]
  have hbot : (⊤ : Submodule ℂ Ws) ≠ ⊥ := by
    intro h
    have h0 : (⟨v, hvWs⟩ : Ws) ∈ (⊥ : Submodule ℂ Ws) := h ▸ Submodule.mem_top
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h0))
  obtain ⟨u, -, hu0, hu⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A.X F.P0 F.ψ0 ρ ⊤ hX hne (fun _ => le_top) hbot
    (fun u _ => Subtype.ext (by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hgoodW u u.2))
  refine ⟨(u : Formalism.AUTREP.GAf D.host.E n → ℂ), ?_, fun h => hu0 (Subtype.ext h), ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact π.stable _ _ hvS)) u.2
  · intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.BaseVec.mem_levS R _ (PY.ψ κ)).1 hκ
    have hgP : R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))) ∈ F.P0 := h3
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (R.eG (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) (PY.ψ κ) :=
      ⟨h1, h2, (MulEquiv.apply_symm_apply R.eG _).symm⟩
    have hc : (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk _) hl
    have e1 : Formalism.L2.NG.rt D.host.E n κ (u : _ → ℂ) =
        Formalism.L2.NG.rt D.host.E n (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) u := by
      conv_lhs => rw [show κ = k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))) *
        ((k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ) by group]
      rw [← rt_rt, hfix u u.2 _ hc]
    have e2 := congrArg Subtype.val (hu ⟨_, hgP⟩)
    rw [e1]
    refine e2.trans ?_
    show _ = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ) • _
    rw [GlobalTheory.BaseVec.principalRowLevelCharacter_trivial, Submodule.coe_smul]
    congr 1
    exact ((congrArg (fun u : ℂˣ => (u : ℂ)) (extendOne_of_mem (R.levR F false).chi h3)).trans rfl).symm

end GlobalTheory.BaseVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundFamilyOfIsCompact
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma le_fintype_sum_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.exists_bound_smooth_data : ∀ {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) →
    ContDiffOn ℝ ∞ ρ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ K, |ρ v| ≤ C ∧
      (∀ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ ≤ C) ∧
      (∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ ≤ C) ∧
      ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ ≤ C := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ
  let F : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => |ρ v|
    + ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖
    + ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖
    + ∑ a, ∑ b, ∑ i, ∑ j,
        ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖
  have hFc : ContinuousOn F K := by
    intro v hv
    have hvU : v ∈ U := hKU hv
    have hρv : ContDiffAt ℝ ∞ ρ v := hρ.contDiffAt (hU.mem_nhds hvU)
    have h1 : ContinuousAt ρ v := hρv.continuousAt
    have h2 : ∀ b, ContinuousAt
        (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x (_root_.GlobalTheory.GoodMetric.coordVec b)) v :=
      fun b => continuousAt_dbar_ofReal_of_contDiffAt_one (hρv.of_le (by simp)) _
    have h3 : ∀ a i j, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) i j) v := fun a i j =>
      ((hG₀ v hvU).1.conn (j := 0) (hG₀ v hvU).2 (by simp)
        (_root_.GlobalTheory.GoodMetric.coordVec a) i j).continuousAt
    have h4 : ∀ a b i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G₀ x
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j) v :=
      fun a b i j =>
      ((hG₀ v hvU).1.curv (j := 0) (hG₀ v hvU).2
        (by rw [zero_add]; exact WithTop.coe_le_coe.2 le_top)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j).continuousAt
    apply ContinuousAt.continuousWithinAt
    simp only [F]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFc
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  have hFv : F v ≤ max C 0 := ((le_abs_self _).trans (hC v hv)).trans (le_max_left _ _)
  have hA : 0 ≤ |ρ v| := abs_nonneg _
  have hB : 0 ≤ ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v
      (_root_.GlobalTheory.GoodMetric.coordVec b)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC3 : 0 ≤ ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  have hD : 0 ≤ ∑ a, ∑ b, ∑ i, ∑ j,
      ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [F] at hFv
  refine ⟨by linarith, fun b => ?_, fun a i j => ?_, fun a b i j => ?_⟩
  · have := le_fintype_sum_of_nonneg
      (fun b => ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖)
      (fun _ => norm_nonneg _) b
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun a => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun b => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) b
    have e4 := le_fintype_sum_of_nonneg
      (fun a => ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_eval_regular_at_fieldPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z),
      ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k,
        (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧
        ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u →
          ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  intro F _ Y Z _ k _ w
  set z := w (IsLocalRing.closedPoint k) with hz
  let ι := algebraMap (Z.presheaf.stalk z) Z.functionField
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  let e : Z.presheaf.stalk z ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let s : Z.presheaf.stalk z →+* k := (Scheme.stalkClosedPointTo (R := .of k) w).hom
  haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w
  have he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a := fun a => e.symm_apply_eq.2 rfl
  refine ⟨s.comp e.symm.toRingHom, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩
    change s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _
    rw [he]
    constructor
    · intro h0
      exact ⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [← hι hba]
      exact (hb.map s).ne_zero
  · intro q _ u ⟨a, ha⟩
    subst ha
    have hm := functionFieldMap_algebraMap q z a
    refine ⟨⟨_, hm.symm⟩, ?_⟩
    have h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) =
        ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩ := Subtype.ext hm
    change s (e.symm _) = _
    rw [h1, he]
    have hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z) := by
      conv_lhs => rw [← spMap_stalkClosedPointTo w]
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
      congr 1
      rw [spMap, spMap, ← Spec.map_comp]
      rfl
    have hv := val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a
    exact hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamilyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU (E := E) (n := n), ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  first | exact @GlobalTheory.BCT.exists_finU_of_loc | exact GlobalTheory.BCT.exists_finU_of_loc | (intros; apply GlobalTheory.BCT.exists_finU_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamilyStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_spherical_vector_of_satake_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ), (∀ w ∉ S, GlobalTheory.LFun.HasSatGL w (π.locRep w) (B w)) → ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), act (.fin (locGL E a w k)) φ = φ := by
  first | exact @GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | exact GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | (intros; apply GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat <;> assumption)
end

