module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanAtMono
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountableConjSub

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
section
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameNormal

open MeasureTheory

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem oo_map_mulLeft {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [CompleteSpace V] (Ph : G → V) (Ph' : G → V') (γ s s' : G) (a b : ℂ)
    (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (hA : ∀ x, Ph (s * x) = a • A (Ph x))
    (hB : ∀ x, Ph' (s' * x) = b • B (Ph' x)) :
    Formalism.L2.SG.TermOp.OO (μ.map (fun x => s * x)) Set.univ Ph Ph' (s * γ * s'⁻¹) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((Formalism.L2.SG.TermOp.OO μ Set.univ Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by
  classical
  have hEF : ∀ F : V' →L[ℂ] V,
      (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv) F =
        (A.toContinuousLinearEquiv : V →L[ℂ] V).comp
          (F.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V')) := by
    intro F
    ext ξ
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  have hmap : ∀ f : G → (V' →L[ℂ] V),
      ∫ x, f x ∂(μ.map fun x => s * x) = ∫ x, f (s * x) ∂μ :=
    fun f => (MeasurableEquiv.mulLeft s).measurableEmbedding.integral_map f
  have hpt : ∀ x, Formalism.L2.SG.TermOp.rk1 (Ph (s * x)) (Ph' ((s * γ * s'⁻¹)⁻¹ * (s * x))) =
      (a * conj b) • (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv)
        (Formalism.L2.SG.TermOp.rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    have h1 : (s * γ * s'⁻¹)⁻¹ * (s * x) = s' * (γ⁻¹ * x) := by group
    rw [h1, hA, hB, hEF, Formalism.L2.SG.RealObj.InfCut.rank_one_smul_isometry]
  unfold Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, Measure.restrict_univ, hmap]
  simp_rw [hpt]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm, hEF]

end Gen

end ClassFrameNormal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftAtSomeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ w, s.1.toTerm.atPt w

def LiftDecompC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹

def DFrameAtS (sc : ℝ) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h h'

def LiftGPosC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) v

def FormTranspC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         Formalism.L2.SG.TermOp.OO
          ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).map (fun x => g * x))
          Set.univ (X.Wu u) (X.Wu u') s.1.pt.1)

def PhaseTieC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
        (X.psiInfU u g * conj (X.psiInfU u' g')) =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CplxNF
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfRat : NFRat := by
  intro D X u u' Λ Λ' q hrel hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : ∀ w : D.what₂.Word, 0 < (σ ((Tu D w : ℕ) : D.host.E)).re := by
    intro w
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D w
  obtain ⟨j, hj, c, hN⟩ := Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (VS D).V σ (nfH (VS D)) D.R.rS
    (nfF (lf D (X.Fu u)).fl (nf_T_ne D u)) (nfF (frq X q).fl (nf_T_ne D u')) (fun x => p_starConj D σ x)
    (hpos u) (hpos u') (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u') _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ((nf_G _ _ _ _).trans hG)
  obtain ⟨-, -, -, -, ⟨h1, h2⟩, ⟨-, h3⟩⟩ := nf_gen _ _ _ _ j hj c hN
  exact ⟨h1, h2, h3⟩

theorem cplxNF : CplxNF := cplxNF_of nfRat

end PI.SchurPlaces
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal.PgLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_F {D : D7} (X : HidaSetting D) : Module.finrank ℚ X.B.I.F = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  omega

theorem one_factor (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (1 / 4) := by
  have hk0 : 0 ≤ k := by linarith
  have hkb : 2 * k ≤ k * b := by nlinarith
  have hkb2 : 2 ≤ k * b := by linarith
  have h7 : (2:ℝ) ^ 7 ≤ (k * b) ^ 7 := by gcongr
  have h9 : (k * b) * 2 ^ 7 ≤ (k * b) * (k * b) ^ 7 := mul_le_mul_of_nonneg_left h7 (by linarith)
  have h8 : (k * b) ^ 8 = (k * b) * (k * b) ^ 7 := by ring
  have hg12 : 12 * (f : ℝ) ≤ g := by nlinarith
  have hgpos : 0 < g := by nlinarith
  have hx : 1 + 3 / g ≤ Real.exp (3 / g) := by
    have := Real.add_one_le_exp (3 / g)
    linarith
  have h0 : 0 ≤ 1 + 3 / g := by positivity
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by gcongr
    _ = Real.exp (f * (3 / g)) := (Real.exp_nat_mul _ f).symm
    _ ≤ Real.exp (1 / 4) := by
        apply Real.exp_le_exp.mpr
        have he : (f : ℝ) * (3 / g) = 3 * f / g := by ring
        rw [he, div_le_iff₀ hgpos]
        linarith

theorem exp_quarter_mul_exp_quarter_le_two : Real.exp (1 / 4) * Real.exp (1 / 4) ≤ 2 := by
  rw [← Real.exp_add]
  have h : Real.exp (1 / 4 + 1 / 4) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 4 + 1 / 4)
  nlinarith

theorem pgLeC_of (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) : PgLeC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y hH => ?_⟩
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' hS hRC Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := exp_quarter_mul_exp_quarter_le_two

end Formalism.L2.SG.KappaOffDiagonal.PgLe
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HaarPushforward
section
noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.CovariantRepresentation

namespace Formalism.L2.SG.HaarPushforward

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]

theorem pushHaar_inv (R Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (hR : IsClosed (R : Set G)) (hΓ : Γ ≤ R)
    (hcov : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) :
    ∃ ν : Measure G, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (R : Set G)ᶜ = 0 ∧ (∀ K : Set G, IsCompact K → ν K < ⊤) ∧
      (∀ r ∈ R, ν.map (fun x => r * x) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  let μ : Measure R := Measure.haar
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  let Γ' : Subgroup R := Γ.subgroupOf R
  let ι : Γ' → Γ := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have hι : Function.Injective ι := by
    intro a b e
    simp only [ι, Subtype.mk.injEq] at e
    exact Subtype.ext (Subtype.ext e)
  haveI : Countable Γ' := hι.countable
  haveI : DiscreteTopology Γ' :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hι
  obtain ⟨K, hK, hKc⟩ := hcov
  have hinv : μ.map (fun x => x⁻¹) = μ :=
    haar_map_inv_of_lattice μ Γ' (hce.isCompact_preimage hK) (fun x => by
      obtain ⟨s, hs, hsK⟩ := hKc x.1 x.2
      exact ⟨⟨s, hΓ hs⟩, Subgroup.mem_subgroupOf.2 hs, hsK⟩)
  refine ⟨μ.map Subtype.val, hemb.sigmaFinite_map, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h
    exact (NeZero.ne μ) h
  · rw [hemb.map_apply]
    have e : (Subtype.val ⁻¹' ((R : Set G)ᶜ) : Set R) = ∅ := by
      ext x
      exact ⟨fun hx => (hx x.2).elim, fun h => h.elim⟩
    rw [e, measure_empty]
  · intro K hK
    rw [hemb.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro r hr
    have hm : Measurable (fun x : G => r * x) := (continuous_const.mul continuous_id).measurable
    have hm' : Measurable (fun y : R => (⟨r, hr⟩ : R) * y) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm hemb.measurable]
    have e : (fun x : G => r * x) ∘ Subtype.val = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [e, ← Measure.map_map hemb.measurable hm', map_mul_left_eq_self]
  · rw [Measure.map_map continuous_inv.measurable hemb.measurable]
    have e : (fun x : G => x⁻¹) ∘ Subtype.val = Subtype.val ∘ (fun y : R => y⁻¹) := rfl
    rw [e, ← Measure.map_map hemb.measurable continuous_inv.measurable, hinv]

end Core

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

end Formalism.L2.SG.HaarPushforward
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Cut

variable {D : Formalism.BasicNotions.D7}

def LocOrbSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (p : PlF D) (τ : Option ((M p).Cls D.R.rS)),
    HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ) ∧
    Summable (fun O => ‖fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖) ∧
    (τ ≠ none → HasSum (gL M δ (D.mem u).A.T (D.mem u').A.T p w τ)
      (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ / Pf.autP M p τ) ∧
    Summable (fun O => ‖gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖))

def LocUnram (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∃ S : Finset (PlF D), ∀ p ∉ S, Pf.autP M p (θ0 p) = 1 ∧
    ∀ (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)),
      fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0) ∧
      gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0)

def ThRestricted (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → Pf.Restricted θ0 (thT M δ γ)

def ThSome (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p, thT M δ γ p ≠ none

def ScalKind (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ γ' : TermDef.Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), EligAt γ w → EligAt γ' w' →
    Corank.TermScal D γ γ' → kind w = kind w'

def EligFinite (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w}.Finite

def AtPtG (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), γ.atPt w →
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0

def PartnerTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def CoefProd (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ w =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p)) *
        ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ)

def PartnerCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
        (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def DnInDens (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ (zT γ)).Nonempty

def NormRepElig (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2

def CutAt (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  LocOrbSum M δ u u' ∧ ScalKind u u' F0 what₂ ∧
    CoefProd M δ u u' F0 what₂ ∧ PartnerCount M δ u u' F0 what₂ ∧ FiberCount M δ L u u' F0 what₂ ∧
    NormRepElig u u' F0 what₂ ∧ ThSome M δ u u' F0 what₂ ∧
    ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS), LocUnram M δ u u' θ0 ∧ ThRestricted M δ u u' F0 what₂ θ0

end Cut

end Formalism.L2.SG.LsDatumB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShiftCore
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.CovariantRepresentation

theorem shiftCore : ShiftCore := by
  intro G _ _ _ _ _ _ μ _ _ R Γ _ V _ _ f Ω h ν _ hΓR hK hn hσ hne hcon hfin hleft hinv hconj hf hΩ hfi
  by_cases hV : CompleteSpace V
  · exact Formalism.L2.SG.MeasureShiftInvariance.shift_general μ R Γ f Ω h ν hΓR hK hn hσ hne hcon hfin hleft hinv hconj
      hf hΩ hfi
  · rw [integral_of_not_completeSpace hV, integral_of_not_completeSpace hV]

end Formalism.L2.SG.CovariantRepresentation
end
end

