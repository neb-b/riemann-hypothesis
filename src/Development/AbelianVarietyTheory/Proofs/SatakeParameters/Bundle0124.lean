module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlace
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.SatakeUnitDeterminantBasis

theorem detB : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  intro D Dx Tw E u μ O w T idl hp i hi c τ
  have hb := T.B_bas i hi c τ
  rw [O.dt_lat, hp.2.2.2.2]
  exact _root_.GlobalTheory.DetBasisNorm.norm_det_eq_nrmId D _ (E.lam w) τ _ _ _ _ (O.lattice_integral_coordinates i) hb.1 hb.2.1 hb.2.2

end GlobalTheory.SatakeUnitDeterminantBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
section
namespace GlobalTheory.Hk3

theorem locVac_span_classes_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]
  set Λ := HoweDuality.intMat L n' n with hΛdef

  have hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤
      fun c => Submodule.span ℂ {ρ c.out s} := by
    intro c
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, rfl⟩
    have hm : -c.out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])
    have := hshift s hvac c.out _ hm
    rw [add_neg_cancel_left] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine iSupIndep.mono ?_ hle
  by_cases hs : s = 0
  · have hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥ := by
      funext c; rw [hs, map_zero, Submodule.span_singleton_eq_bot]
    rw [hb, iSupIndep_def]
    intro i
    exact disjoint_bot_left
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)
  refine LinearIndependent.iSupIndep_span_singleton ?_
  rw [linearIndependent_iff']
  intro I C hC y hy
  have hind := eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L))
    (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') =>
      ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
    (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
    (by
      intro y _ y' _ hyy
      by_contra hcon
      push_neg at hcon
      apply hyy
      have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
      rw [hΛ] at hm
      rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
      exact hm)
    C hC
  exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LenSmulTup
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem len_smul_tup : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L → ∀ v, len X v j ((X.Lv.lev j c).smul γ L) = len X v j L - ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det := by
  intro p _ X j c γ L hL v
  exact Formalism.L2.G.Pend.len_smul X j c γ L hL v

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftsOpMatMem
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHeckeCore

open Formalism.DivisionValues Formalism.IndefR Formalism.L2.Theta GlobalTheory.HeckeRational GlobalTheory.SplitHeckeAdj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (t i a b) :
    (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degR t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k D.sp.X'.rank with hk' | hk'
  · exact rows_dcOp_mem_cmMax R hf.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degR t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem lifts_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (j t i a b) :
    (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degL j t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k (Vc D j).rank with hk' | hk'
  · exact lifts_dcOp_mem_cmMax R hf.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degL j t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem hecke_okH_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (_F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, (A.fam.R t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.R t).op) ∧ ∀ j t, (A.fam.L j t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.L j t).op := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ hl hf hm
  obtain ⟨gramR, c0R, c0L, tie⟩ := hf.tie
  have honto : ∀ t PP, Bridge.SplitOff PP ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) → ∃ P, R.pl P = PP :=
    fun t PP hP => hf.pl_onto PP (splitOff_mono Set.subset_union_left hP)
  have hS : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
    fun t PP hP => hP.elim (fun h1 => Or.inl (hf.Sb h1)) Or.inr
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · obtain ⟨c, hc⟩ := hl.βX
    rw [one_pow] at hc
    have h := side_adj_comm D.sp.X' R.βX R.ΛX (R.datXt t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      R.cX.coef.ρ (fun γ => hm.cX.2.1 γ) D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres (A.heckeR t)
      (R.B.R t).hecke (hf.degR t)
    exact ⟨⟨rows_opMat_mem R hf t, h.1⟩, h.2⟩
  · obtain ⟨c, hc⟩ := hl.βV j
    rw [one_pow] at hc
    have h := side_adj_comm (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      (R.cV j).coef.ρ (fun γ => (hm.cV j).2.1 γ) D.what₂.embLL (A.MtCSD j t) (R.B.L j t).pres (A.heckeL j t)
      (R.B.L j t).hecke (hf.degL j t)
    exact ⟨⟨lifts_opMat_mem R hf j t, h.1⟩, h.2⟩

end GlobalTheory.SplitHeckeCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
section
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.MainNotions.G Matrix

def homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) : Submodule W (Matrix (Fin k') (Fin k) Qq) where
  carrier := {x | ∀ z ∈ A, x *ᵥ z ∈ B}
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem
  add_mem' := fun hx hy z hz => by rw [Matrix.add_mulVec]; exact B.add_mem (hx z hz) (hy z hz)
  smul_mem' := fun c x hx z hz => by
    rw [Matrix.smul_mulVec]
    exact B.smul_mem c (hx z hz)

theorem mem_homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) (x : Matrix (Fin k') (Fin k) Qq) :
    x ∈ homLat W A B ↔ ∀ z ∈ A, x *ᵥ z ∈ B := Iff.rfl

end GlobalTheory.VolAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLamCTypeNormOne
section
noncomputable section

namespace GlobalTheory.TwU.RatNorm

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem frob_pow_int (X : Sys p) (v : X.Pl) (k : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ k) (algebraMap _ _ x) = algebraMap _ _ y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ]
    show (X.G.P.σ v ^ k) ((X.G.P.σ v) (algebraMap _ _ x)) = _
    rw [hy, hz]

theorem norm_twG_int_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    ‖twG X E v s (algebraMap _ _ x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := frob_pow_int X v s.val x
  have h := E.int (X.G.P.j v y)
  unfold twG
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hy, (X.G.P.setting v).ι_comp]
  exact h

theorem norm_twG_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    ‖twG X E v s (algebraMap _ _ (u : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_int_le X E v s (u : X.G.P.W v)
  have h2 := norm_twG_int_le X E v s ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have h3 : twG X E v s (algebraMap _ _ (u : X.G.P.W v)) * twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg (twG X E v s (algebraMap _ _ (u : X.G.P.W v))),
    norm_nonneg (twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) {y : X.G.P.Qq v} (hy : y ≠ 0) :
    ‖twG X E v s y‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p y := by
  haveI := (X.G.P.setting v).frac_alt
  have hp := (X.G.P.setting v).p_unif
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  rw [ordP_eq hp n u, map_mul, map_zpow₀, map_natCast, norm_mul, norm_twG_unit, one_mul, norm_zpow]

theorem zpow_sum_fin {ι : Type*} (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (f : ι → ℤ) :
    r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hr, ih]

theorem norm_lamC_type_normOne : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
    LamPos X E pos lam ρ → ∀ (e : D.what₂.Tau → ℤ) (z : D.host.E), z * D.host.conj z = 1 →
    ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ)‖ =
      ‖(p : ℂ_[p])‖ ^ (∑ v : X.Pl, (∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩)) *
        ordP (X.G.P.W v) p (ρ v z)) := by
  intro D p _ X E pos lam ρ hL e z hz
  have hp0 : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hmem : ∀ τ, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hprod : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => zpow_mem (hmem τ) _
  have h1 : TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) = ∏ τ, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ z) ^ e τ := by
    have e1 : (⟨∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ, hprod⟩ : TaylorLogMetric.Qbar) = ∏ τ, (⟨TaylorLogMetric.embT D τ z, hmem τ⟩ : TaylorLogMetric.Qbar) ^ e τ := by
      apply Subtype.ext
      push_cast
      rfl
    unfold TaylorLogMetric.lamC
    rw [dite_eq_left hprod, e1, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [dite_eq_left (hmem τ), map_zpow₀]
  have hρ : ∀ v, ρ v z * ρ v (D.host.conj z) = 1 := fun v => by rw [← map_mul, hz, map_one]
  have hρ0 : ∀ v, ρ v z ≠ 0 := fun v h => by have := hρ v; rw [h, zero_mul] at this; exact zero_ne_one this
  have hf : ∀ v s, ‖TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) z)‖ ^ e (pos ⟨v, s⟩) =
      ‖(p : ℂ_[p])‖ ^ ((if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩) * ordP (X.G.P.W v) p (ρ v z)) := by
    intro v s
    by_cases hs : IsOddPos s
    · rw [LamPos.odd X E pos lam ρ hL v s hs, if_pos hs, eq_inv_of_mul_eq_one_right (hρ v), map_inv₀, norm_inv, norm_twG X E v s (hρ0 v),
        inv_zpow', ← zpow_mul]
      congr 1
      ring
    · rw [LamPos.even X E pos lam ρ hL v s hs, if_neg hs, norm_twG X E v s (hρ0 v), ← zpow_mul]
      congr 1
      ring
  rw [h1, norm_prod]
  simp_rw [norm_zpow]
  rw [← Equiv.prod_comp pos, Fintype.prod_sigma]
  simp_rw [hf, Finset.sum_mul]
  rw [zpow_sum_fin _ _ hp0]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [zpow_sum_fin _ _ hp0]

end GlobalTheory.TwU.RatNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsAdjointIntertwinerEqJointEigenspaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem parts_of_adjoint_lift : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  intro X E I _ _ _ _ _ _ Θ op h C Ec lab hint hn hn' hc htop hh hne
  have hcomm : Formalism.L2.Col.PairComm h := by
    intro i j
    refine GlobalTheory.EigTransfer.linearMap_ext_of_iSup_eq_top Ec htop (h i * h j) (h j * h i) fun c w hw => ?_
    simp only [Module.End.mul_apply, hh c w hw, map_smul, smul_smul, mul_comm]
  have hup : ∀ c, (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigAt op (lab c) := by
    rintro c _ ⟨w, hw, rfl⟩
    exact Formalism.L2.Col.mem_eigAt_of_forall_apply fun i =>
      _root_.GlobalTheory.HkUp.eigen_up_along_adjoint Θ op h hint hn hn' i (lab c i) w (hh c w hw i)
  have hiff : ∀ (Q : (I → ℂ) → Prop) c, Ec c ≠ ⊥ →
      ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c)) := by
    intro Q c hcne
    constructor
    · intro hle
      by_contra hq
      obtain ⟨w, hw, hw0⟩ := hne c hcne
      have hm : LinearMap.adjoint Θ w ∈ (Ec c).map (LinearMap.adjoint Θ) := ⟨w, hw, rfl⟩
      have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx
      exact hw0 ((Submodule.disjoint_def.1 hd) _
        (Formalism.L2.Col.eigAt_le_eigSum (C := fun x => ¬ Q x) hq (hup c hm)) (hle hm))
    · intro hq
      exact (hup c).trans (Formalism.L2.Col.eigAt_le_eigSum hq)
  refine ⟨hcomm, fun Q => ⟨fun c hcne => hiff Q c hcne, ?_⟩⟩
  have hle : ∀ P : (I → ℂ) → Prop, (⨆ (c : C) (_ : P (lab c)), Ec c) ≤ Formalism.L2.Col.eigSum h P := fun P =>
    iSup₂_le fun c hq w hw => Formalism.L2.Col.eigAt_le_eigSum hq
      (Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hh c w hw i)
  have hsup : (⨆ (c : C) (_ : Q (lab c)), Ec c) ⊔ (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun c => ?_
    by_cases hq : Q (lab c)
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c hq le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun c (_ : ¬ Q (lab c)) => Ec c) c hq le_rfl)
  have hd : Disjoint (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (Formalism.L2.Col.eigSum h Q) :=
    (Formalism.L2.Col.disjoint_eigSum hcomm (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx).mono_left
      (hle fun x => ¬ Q x)
  have hQ : (⨆ (c : C) (_ : Q (lab c)), Ec c) = Formalism.L2.Col.eigSum h Q := by
    have := sup_inf_assoc_of_le (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (hle Q)
    rw [hsup, top_inf_eq, hd.eq_bot, sup_bot_eq] at this
    exact this.symm
  rw [← hQ]
  apply le_antisymm
  · refine iSup₂_le fun c hcq => ?_
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c ((hiff Q c hcq.1).1 hcq.2) le_rfl
  · refine iSup₂_le fun c hq => ?_
    by_cases hb : Ec c = ⊥
    · rw [hb]; exact bot_le
    · exact le_iSup₂_of_le (f := fun c (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q) => Ec c)
        c ⟨hb, (hiff Q c hb).2 hq⟩ le_rfl

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PendTThFLtOfKapLawLt
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU

theorem pendT_ThF_lt_of_kapLawLt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; KapLawLt X ℂ_[p] (thFOf X pos F) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La') ∧ ∀ v, ∀ j < X.mm, XiEx X ℂ_[p] (thFOf X pos F) v j → XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j := by
  intro p _ X _ E hfin hst g hLT T pos F
  intro hK
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  have h1 : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La' := by
    rintro j hj ⟨c, L⟩ La' hL hL'
    change thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin (thFOf X pos F)) j (c, L) La' = _
    rw [thN_eq]
    generalize delt X hfin j c L = δ
    have hL2 : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul δ⁻¹ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ δ⁻¹ L).2 hL
    have := hK j hj c _ La' δ hL2 hL'
    rw [lsmul_lsmul_inv] at this
    exact this.symm
  refine ⟨h1, ?_⟩
  rintro v j hj ⟨Ξ, u, u', hu, hu', hΞ⟩
  refine ⟨Ξ, u, u', hu, hu', fun La La' hL hL' => ?_⟩
  rw [h1 j hj La La' hL hL']
  exact hΞ La La' hL hL'

end GlobalTheory.TwU
end
end

