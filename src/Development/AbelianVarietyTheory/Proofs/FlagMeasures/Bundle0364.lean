module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPart
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.OrthLoc

variable {D : D7}

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x y z : Vp D p) :
    LocFacts₂ Z.M p (x + y) z = LocFacts₂ Z.M p x z + LocFacts₂ Z.M p y z := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x z : Vp D p) :
    LocFacts₂ Z.M p (c • x) z = c * LocFacts₂ Z.M p x z := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def orthP (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule (D.s.atP p).Ep (Vp D p) where
  carrier := {v | ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0}
  zero_mem' := by intro u _; simp [LocFacts₂]
  add_mem' := by intro a b ha hb u hu; rw [localForm_add_left, ha u hu, hb u hu, add_zero]
  smul_mem' := by intro c a ha u hu; rw [localForm_smul_left, ha u hu, mul_zero]

theorem span_orth_le (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ≤ orthP Z p U := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩ u hu
  have ha' : (VS D).hT u a = 0 := by
    have ha2 : a ∈ orth (VS D) U := ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at ha2
    exact ha2 u hu
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, ha']

theorem mem_localLattice_inf_orthogonal : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V),
    (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) →
    (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) →
      (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) →
    ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ →
      (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  intro D Z U hdec huniq Λ hΛ p t ht horth
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) U) hΛ.fg
  have hmem : t ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) : Set (Vp D p)) := by
    rw [hsat]
    refine ⟨ht, ?_⟩
    have htop : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) = ⊤ := by
      apply top_unique
      rw [← span_baseChange_eq_top p]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
      rw [map_add]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
    have ht' : t ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) := htop ▸ Submodule.mem_top
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ht'
    have hβ0 : β = 0 := by
      apply huniq p β hβ
      have e : β = t - α := by rw [← hαβ]; abel
      have hto : t ∈ orthP Z p U := horth
      have h2 := (orthP Z p U).sub_mem hto (span_orth_le Z p U hα)
      rw [← e] at h2
      exact h2
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exact hmem

end GlobalTheory.Unfold.OrthLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetric
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalSymm

open Formalism.L2.SG.NGCut

theorem scal_symm : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  intro D X Y u u' t t' hG hG' hs hsc
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t : TauC Y u u', t.G ≠ 0 → Gval (lf D (X.Fu u)) t.frame ≠ 0 := fun t h =>
    (Formalism.L2.SG.Pf.SatGram.gterm_G Y t) ▸ h
  have hlat : ∀ t : TauC Y u u', Submodule.IsFullLattice D.host.E t.lam := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : TauC Y u u', IsLift t.lam (lf D (X.Fu u)) := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : TauC Y u u', IsLift t.lam t.frame := fun t => t.rep.2.2.2.2.1
  obtain ⟨⟨hlam, hlam'⟩, -, hIS⟩ := (show Formalism.L2.SG.TermOp.scalT t t' from hsc)
  have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at h1'
  rw [if_pos ⟨hlam, hlam'⟩] at h1'
  have hth := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
    (hGv t hG)).1 h1'
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
  have hsym := CorankRelation.Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
    (hGv t hG) (hGv t' hG') (CorankRelation.frame_mem_iff t t') hth
  have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
  rw [hinv] at hsym
  have hs' : s0 t.lam (lf D (X.Fu u)) t'.frame t.frame (t.lin * t'.lin⁻¹) D.R.k = 1 :=
    (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' hG')).2 hsym
  have hback : ∀ y : (VS D).V, (t'.lin * t.lin⁻¹) ((t.lin * t'.lin⁻¹) y) = y := fun y => by
    show t'.lin (t.lin.symm (t.lin (t'.lin.symm y))) = y
    simp
  refine ⟨?_, ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    exact hs'
  · show Formalism.L2.SG.TermOp.scalT t' t
    refine ⟨⟨hlam.symm, hlam'.symm⟩, ?_, ?_⟩
    · rw [← hlam]; exact hs'
    · rw [← hlam]
      intro y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' hd hd' al al'
      have hd1 : y1 - y2 ∈ Xsp (lf D (X.Fu u)) := by
        have := (Xsp (lf D (X.Fu u))).neg_mem hd
        simpa using this
      have hd2 : y2'' - (t'.lin * t.lin⁻¹) y1' ∈ Xsp t'.frame := by
        have h := (CorankRelation.frame_mem_iff t t' _).1 hd'
        rw [map_sub, hback] at h
        have := (Xsp t'.frame).neg_mem h
        simpa using this
      exact (hIS y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al').symm

end GlobalTheory.ScalSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepKernel

theorem deep_kernel_bound_of_ptBound : PtBound →
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  intro hP hF Cg n₀ B d p q b c x _ hn hq hC hc hx
  obtain ⟨-, -, -, -, -, hqn, hrk, hmin, -, -, -, -, h, -, hgap, h40, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn hC
  have hD : IsDSData B d := hC.1
  have hg : 1 ≤ B.g := hC.2.2.2.2.2.2.2.2.2.1
  have hS := _root_.GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn hC
  have hfin := hF B Cg n₀ d p q b hn hC
  have hloc : LocDec B h := (hP B d p q h hD hC.2.1 hgap (by rw [hmin]; exact h120)).2.2.2.2.2.2
  obtain ⟨Rφ, hR, T, -, hT2, hT3, -, -, hT6, hT7, hT8, hT9⟩ :=
    _root_.GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame B d h hD hS hg (fun v => by rw [hrk v]; exact h120) hloc h40 hfin
  choose Fr hFr using fun i => _root_.GlobalTheory.SmoothRepsType.repsExist B d hD hS hg (T i) (hT2 i) (hT7 i)
  obtain ⟨y, Fc, hy, hsp, hFc, hk, -⟩ := GlobalTheory.KernelExpansion.kernelB B d h hD (by omega) hloc h32 hfin Rφ hR
  have hw := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hD 0).1
  have e := GlobalTheory.Dec.kerDiag_basis_indep B B.D y (fun i => T i (B.tens B.w)) Fc (fun i => Fr i (B.tens B.w))
    hy hT8 (hsp.trans hT9.symm) (fun i => ⟨hFc i, (hFr i 0 _ hw).1⟩) x
  have e2 : (kern B.I (phe B d) x x).re = ‖vv B Fr (B.tens B.w) x‖ ^ 2 := by
    rw [hk, EuclideanSpace.norm_sq_eq, Complex.re_sum]
    simp only [vv]
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e2]
  exact _root_.GlobalTheory.DeepFamilyGap.deep_bound_family B Cg n₀ d p q b c x B.D T Fr hn hq hC hc hx hFr hT3 hT6

end GlobalTheory.DeepKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryExtensionRationalIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

theorem form_ext_left {D : D7} (Z : LocDat D) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (w w' : Vp D p)
    (h : ∀ x, (locH Z p).h (g (baseChange₂ D p x)) w' = (locH Z p).h (baseChange₂ D p x) w) (x : Vp D p) :
    (locH Z p).h (g x) w' = (locH Z p).h x w := by

  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by
    rw [span_baseChange_eq_top p]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    exact h z
  | zero =>
    rw [map_zero, (locH Z p).h_zero_left, (locH Z p).h_zero_left]
  | add y y' _ _ hy hy' =>
    rw [map_add (f := _), (locH Z p).h_add_left, (locH Z p).h_add_left, hy, hy']
  | smul a y _ hy =>
    rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, hy]

theorem exists_ext_unitary : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, GlobalTheory.LocOver.Ext p ρ g ∧ Formalism.MainNotions.S.LocNG.IsUnitary (locH Z p) g := by
  intro D Z p ρ hρ

  obtain ⟨g, hg⟩ := GlobalTheory.HL.RatExt.exists_equiv (D.s.atP p).ιE
    ((VS D).frame.equivFun.symm.trans (ρ.trans (VS D).frame.equivFun))
  have hext : GlobalTheory.LocOver.Ext p ρ g := by
    intro x
    have h1 := hg ((VS D).frame.equivFun x)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ

  have hA : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) =
      (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hext a, hext b]
    show LocFacts₂ Z.M p _ _ = LocFacts₂ Z.M p _ _
    rw [baseChangeAt_form Z.M p (Z.hcj p), baseChangeAt_form Z.M p (Z.hcj p)]
    exact congrArg _ (hρ' b a)

  have hB : ∀ b x, (locH Z p).h (g x) (g (baseChange₂ D p b)) = (locH Z p).h x (baseChange₂ D p b) :=
    fun b x => form_ext_left Z p g (baseChange₂ D p b) (g (baseChange₂ D p b)) (fun a => hA a b) x
  have hC : ∀ a y, (locH Z p).h (g (baseChange₂ D p a)) (g y) = (locH Z p).h (baseChange₂ D p a) y := by
    intro a y
    rw [(locH Z p).h_herm (g y) (g (baseChange₂ D p a)), (locH Z p).h_herm y (baseChange₂ D p a), hB]
  refine ⟨g, hext, ?_⟩
  intro x y
  exact form_ext_left Z p g y (g y) (fun a => hC a y) x

end GlobalTheory.LocOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealEqOfLocalSpansEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Sloc.OneDim

theorem nV_pos (D : D7) : 0 < nV D := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  show 0 < (D.sp.Y 0).rank
  rw [h]
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
  omega

def lineMap (D : D7) : D.host.E →ₗ[𝓞 D.host.E] (VS D).V :=
  (LinearMap.toSpanSingleton D.host.E (VS D).V ((VS D).frame ⟨0, nV_pos D⟩)).restrictScalars (𝓞 D.host.E)

theorem lineMap_injective (D : D7) : Function.Injective (lineMap D) := by
  intro a b h
  have h' : a • (VS D).frame ⟨0, nV_pos D⟩ = b • (VS D).frame ⟨0, nV_pos D⟩ := h
  exact smul_left_injective D.host.E ((VS D).frame.ne_zero _) h'

theorem localLattice_map (D : D7) (Z : LocDat D) (p : PlF D) (K : Submodule (𝓞 D.host.E) D.host.E) :
    lattice₂ D Z.M p (K.map (lineMap D)) =
      (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (K : Set D.host.E))).map
        ((LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1)).restrictScalars (Z.M p).L.O) := by
  have key : ∀ k : D.host.E, baseChange₂ D p (lineMap D k) =
      LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1) ((D.s.atP p).ιE k) := by
    intro k
    have h1 : lineMap D k = k • (VS D).frame ⟨0, nV_pos D⟩ := rfl
    rw [h1, baseChange_smul₂, baseChangeAt_frame, LinearMap.toSpanSingleton_apply]
  unfold Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(D.s.atP p).ιE k, ⟨k, hk, rfl⟩, (key k).symm⟩
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨lineMap D k, ⟨k, hk, rfl⟩, key k⟩

private theorem le_of_locP_eq_forall_heightOneSpectrum {D : D7} {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B) : A ≤ B := by
  intro x hx
  by_contra hxB
  let c : Ideal (𝓞 D.host.E) := B.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V x)
  have hc : c ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 D.host.E) ∈ c := htop ▸ Submodule.mem_top
    apply hxB
    simpa [c, LinearMap.toSpanSingleton_apply] using h1
  obtain ⟨M, hM, hcM⟩ := Ideal.exists_le_maximal c hc
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) :=
    ⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.E)).ne'⟩
  have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A :=
    show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ A from ⟨1, P.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rw [h P] at hxA
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ B := hxA
  exact hs (hcM (show s ∈ c by simpa [c, LinearMap.toSpanSingleton_apply] using hsx))

end GlobalTheory.Sloc.OneDim


open GlobalTheory.Sloc.OneDim in
theorem GlobalTheory.Sloc.fg_eq_of_completions : ∀ (D : D7) (Z : LocDat D) (I J : Submodule (𝓞 D.host.E) D.host.E), I.FG → J.FG → (∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (I : Set D.host.E)) = Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (J : Set D.host.E))) → I = J := by
  intro D Z I J hI hJ hloc
  have hlat : ∀ p : PlF D, lattice₂ D Z.M p (I.map (lineMap D)) = lattice₂ D Z.M p (J.map (lineMap D)) := by
    intro p
    rw [localLattice_map, localLattice_map, hloc p]
  have hEq := Formalism.L2.SG.Pf.locEqC_holds D Z
  unfold Formalism.L2.SG.Pf.LocEqC at hEq
  have hP : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (I.map (lineMap D)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (J.map (lineMap D)) := by
    intro P
    let p : PlF D := ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
      fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩
    exact (hEq p _ _ (hI.map _) (hJ.map _)).1 (hlat p) P rfl
  have hAB : I.map (lineMap D) = J.map (lineMap D) :=
    le_antisymm (OneDim.le_of_locP_eq_forall_heightOneSpectrum hP) (OneDim.le_of_locP_eq_forall_heightOneSpectrum fun P => (hP P).symm)
  exact Submodule.map_injective_of_injective (lineMap_injective D) hAB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairGramInvariantUnchangedIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

private theorem sum_castLE_lemma {M : Type} [AddCommMonoid M] {l N : ℕ} (h : l ≤ N) (g : Fin N → M)
    (hg : ∀ a : Fin N, l ≤ (a : ℕ) → g a = 0) :
    ∑ a, g a = ∑ a : Fin l, g (Fin.castLE h a) := by
  symm
  calc ∑ a : Fin l, g (Fin.castLE h a) = ∑ x ∈ Finset.univ.map (Fin.castLEEmb h), g x :=
        (Finset.sum_map Finset.univ (Fin.castLEEmb h) g).symm
    _ = ∑ a, g a := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        apply hg
        by_contra hlt
        exact ha (Finset.mem_map.2 ⟨⟨(a : ℕ), Nat.lt_of_not_le hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadMinorE_unitri_both {E : Type} [Field E] {N : ℕ} (Z U U' : Matrix (Fin N) (Fin N) E)
    (hU : IsUpUni U) (hU' : IsUpUni U') (l : ℕ) :
    leadMinorE (U.transpose * Z * U') l = leadMinorE Z l := by
  have hz : ∀ i j : Fin N, j < i → U i j = 0 := fun i j hij => (hU i j).1 hij
  have hz' : ∀ i j : Fin N, j < i → U' i j = 0 := fun i j hij => (hU' i j).1 hij
  unfold leadMinorE
  by_cases h : l ≤ N
  · rw [dite_eq_left h, dite_eq_left h]
    have key : (U.transpose * Z * U').submatrix (Fin.castLE h) (Fin.castLE h) =
        (U.submatrix (Fin.castLE h) (Fin.castLE h)).transpose * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          U'.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [sum_castLE_lemma h]
      · refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [sum_castLE_lemma h]
        intro a ha
        have hi := i.isLt
        rw [hz a (Fin.castLE h i) (by rw [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
      · intro b hb
        have hj := j.isLt
        rw [hz' b (Fin.castLE h j) (by rw [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
    have t1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have t2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU' (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have d1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t1]
      exact Finset.prod_eq_one (fun a _ => (hU (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    have d2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t2]
      exact Finset.prod_eq_one (fun a _ => (hU' (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, d1, d2, one_mul, mul_one]
  · rw [dite_eq_right h, dite_eq_right h]

theorem gval_eq_of_movesTo : ∀ (D : D7) {T T' : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F F0' F' ρ U U' h
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hiso : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  have hstar : IsUpUni (U.map star) := by
    refine fun i j => ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [Matrix.map_apply, (hU i j).1 hij, star_zero]
    · rw [Matrix.map_apply, (hU i j).2 hij, star_one]
  have hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl = (U.map star).transpose * Formalism.MainNotions.S.Zhat F0.fl F0'.fl * U' := by
    ext a b
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← hiso (F.fl.fvec a) (F'.fl.fvec b), hF a, hF' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, frame, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    ring
  show Formalism.MainNotions.S.Gflag F.fl F'.fl = Formalism.MainNotions.S.Gflag F0.fl F0'.fl
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [hZ, leadMinorE_unitri_both _ _ _ hstar hU', leadMinorE_unitri_both _ _ _ hstar hU']

end GlobalTheory.HL
end

