module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0104
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountCos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcBridgeB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0034

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinIdxAt
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

set_option maxHeartbeats 1000000 in
theorem finIdx_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    (ProdE.CPL M δ u u' w hA L U hL hU).relIndex (ProdE.AP M δ u u' w p) ≠ 0 ∧
      (ProdE.AP M δ u u' w p).relIndex (ProdE.CPL M δ u u' w hA L U hL hU) ≠ 0 := by
  classical
  obtain ⟨c0, hc00, hc0O, hcong⟩ := cong_at M δ u u' w hA L U hL hU
  set Lp := lOf δ M p L U with hLpd
  set Lpi := lOf δ M p L⁻¹ U⁻¹ with hLpid
  set Up := ρOf δ M p L U with hUpd
  set Upi := ρOf δ M p L⁻¹ U⁻¹ with hUpid
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by rw [hLpd, hLpid, ← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hLL' : Lpi * Lp = 1 := ProdE.lp_inv M δ hA L U hL hU
  have hUU : Up * Upi = 1 := ProdE.up_inv M δ hA L U hL hU
  have hUU' : Upi * Up = 1 := by rw [hUpd, hUpid, ← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  have hRO : ∀ {x : (D.s.atP p).Ep}, x ∈ (M p).R → x ∈ (D.s.atP p).O := fun hx => R_sub_O M δ hA hx
  refine ⟨?_, ?_⟩
  · haveI := finite_quot M δ hA c0 hc00 hc0O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.AP M δ u u' w p =>
        ((fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) - ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p))
        i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    have hki := (k⁻¹).2
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.AP M δ u u' w p) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.2
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a' : ProdE.MP p) - 1 =
        ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) by rw [Matrix.mul_sub, ha]]
      exact entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show (b' : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
        ((b' : ProdE.MP p) - (b : ProdE.MP p)) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) by rw [Matrix.sub_mul, hb]]
      exact entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2
  · set c1 := s2 * (s1 * c0) * (s3 * s4) with hc1d
    have hc1O : c1 ∈ 𝒪[(D.s.atP p).Fp] := Subring.mul_mem _ (Subring.mul_mem _ hs2O (Subring.mul_mem _ hs1O hc0O))
      (Subring.mul_mem _ hs3O hs4O)
    have hc10 : c1 ≠ 0 := mul_ne_zero (mul_ne_zero hs20 (mul_ne_zero hs10 hc00)) (mul_ne_zero hs30 hs40)
    haveI := finite_quot M δ hA c1 hc10 hc1O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.CPL M δ u u' w hA L U hL hU =>
        ((fun i j => (QuotientAddGroup.mk (⟨(Lp * ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) * Lpi) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨(Upi * ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) * Up) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : EntIn (latS (D.s.atP p) c1) (Lp * (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p)) * Lpi) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : EntIn (latS (D.s.atP p) c1) (Upi * (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) * Up) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have hki := (k⁻¹).2
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.CPL M δ u u' w hA L U hL hU) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.1
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq1 : ((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1 =
          Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) * (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) *
            Lp := by
        rw [show Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) *
            (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) * Lp =
            (Lpi * Lp) * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (Lpi * Lp) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) *
              (Lpi * Lp) by simp only [Matrix.mul_assoc], hLL', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.mul_sub, ha]
      rw [eq1]
      exact entIn_sandwich hs2 hs1 (entIn_latS_of_eq (t := s3 * s4) rfl (Subring.mul_mem _ hs3O hs4O)
        (entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1))
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq2 : ((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
          Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) * (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) *
            Upi := by
        rw [show Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) *
            (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) * Upi =
            (Up * Upi) * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * (Up * Upi) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) *
              (Up * Upi) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.sub_mul, hb]
      rw [eq2]
      exact entIn_sandwich hs3 hs4 (entIn_latS_of_eq (t := s2 * s1) (by rw [hc1d]; ring)
        (Subring.mul_mem _ hs2O hs1O) (entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2))

end Fin2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairOfU
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}

def uLo (X : MP p) (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_lower p h1 h2]; exact isUnit_one)

def uUpU (X : MP p) (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_upper p h1 h2]; exact isUnit_one)

def pairOfU (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (x : UP p) (hx : πa x = 1) :
    Formalism.L2.SG.Pf.Coef.CellPair a :=
  ⟨(((x : GG p).1 : GLp p).val, (((x : GG p).2.unop : GLp p)).val),
    by
      obtain ⟨h1, h2⟩ := (hker x).1 hx
      exact ⟨fun i => (h1 i i).2 rfl, fun i j hij => (h1 i j).1 hij, fun i j hij hb => h2 i j hij hb⟩,
    fun i => (x.2.2 i i).2 rfl, fun i j hij => (x.2.2 i j).1 hij⟩

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountHoldsAll
section
namespace Formalism.L2.SG.Pf.PCount

theorem partnerCount_holds_all {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : PartnerIsomorphismCount Zd :=
  partnerCount_of_iso Zd (Formalism.L2.SG.LsDatumA.integralClosureRank_and_residueTrdegLe D) (intGenP_holds Zd) BI.integralIsomorphism_holds

end Formalism.L2.SG.Pf.PCount
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolAct
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAct

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def sbs {D : Formalism.BasicNotions.D7} (b : MatR D) : MatR D := Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS

def LiftData (γ : TermDef.Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsLoUni (a' : MatR D) ∧ IsUpUni b ∧ (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') ∧
    Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b ∧
    ν ∈ NLam γ.lam (lf D F0) ∧ m ∈ NLam γ.lam F' ∧
    (∀ c, ν (frame (lf D F0) c) = ∑ d, (a' : MatR D).conjTranspose d c • frame (lf D F0) d) ∧
    (∀ c, m (frame F' c) = ∑ d, sbs b d c • frame F' d) ∧
    F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') ∧
    TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F₂ ∧
    ∀ c, frame F₂ c = ν⁻¹ (m (frame F' c))

def MoveCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a' : GLR D) (b : MatR D), IsLoUni (a' : MatR D) → IsUpUni b →
      (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') →
      Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b →
      ∃ ν m F₂, LiftData u u' F0 what₂ γ F' a' b ν m F₂

def OntoCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F'),
      TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'' →
      ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V), LiftData u u' F0 what₂ γ F' a' b ν m F''

def FibreCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (x₁ x₂ : GLR D), (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L → (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L →
      LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁ → LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂ →
      (CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ ↔ x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L)

end Formalism.L2.SG.Pf.ZsVolAct

end
end

