module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableBcWeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnipotentFrameCorrespondsUnderIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.NUTransport

section Lin
variable {E V W : Type} [CommRing E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

abbrev As {r : ℕ} (f : Fin (r + 1) → V) (j : ℕ) : Submodule E V := Submodule.span E (f '' {i | (i : ℕ) < j})

theorem As_mono {r : ℕ} (f : Fin (r + 1) → V) {i j : ℕ} (h : i ≤ j) : (As (E := E) f i) ≤ As (E := E) f j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem As_zero {r : ℕ} (f : Fin (r + 1) → V) : (As (E := E) f 0) = ⊥ := by
  simp [As]

theorem unip_iff (e : V ≃ₗ[E] W) (g : V ≃ₗ[E] V) (A B : Submodule E V) :
    ((∀ x, ((e.symm.trans g).trans e) x ∈ A.map (e : V →ₗ[E] W) ↔ x ∈ A.map (e : V →ₗ[E] W)) ∧
      ∀ x ∈ A.map (e : V →ₗ[E] W), ((e.symm.trans g).trans e) x - x ∈ B.map (e : V →ₗ[E] W)) ↔
    ((∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B) := by
  simp only [Submodule.mem_map_equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_sub]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => by simpa using h1 (e v), fun v hv => by simpa using h2 (e v) (by simpa using hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 _, fun x hx => h2 _ hx⟩

variable {r : ℕ} (g : V ≃ₗ[E] V) (f : Fin (r + 1) → V)

theorem step (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m + 1 ≤ r) : ∀ v ∈ As (E := E) f (m + 1), g v - v ∈ As (E := E) f m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := lt_of_lt_of_le hi hm
    have hc : i = (⟨i, hi'⟩ : Fin r).castSucc := Fin.ext rfl
    have := hN ⟨i, hi'⟩
    rw [← hc] at this
    exact As_mono f (Nat.lt_succ_iff.mp hi) this
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), add_sub_add_comm]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ a hx

theorem fwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) : ∀ v ∈ As (E := E) f m, g v ∈ As (E := E) f m := by
  intro v hv
  cases m with
  | zero => rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m =>
    have h := step g f hN m hm v hv
    have : g v = v + (g v - v) := by abel
    rw [this]; exact Submodule.add_mem _ hv (As_mono f (Nat.le_succ m) h)

theorem bwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a) :
    ∀ m : ℕ, m ≤ r → ∀ v ∈ As (E := E) f m, g.symm v ∈ As (E := E) f m := by
  intro m
  induction m with
  | zero => intro _ v hv; rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m ih =>
    intro hm v hv
    have h := step g f hN m hm v hv
    have h2 := ih (Nat.le_of_succ_le hm) _ h
    have : g.symm v = v - g.symm (g v - v) := by simp
    rw [this]; exact Submodule.sub_mem _ hv (As_mono f (Nat.le_succ m) h2)

theorem iff_of (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) (v : V) : g v ∈ As (E := E) f m ↔ v ∈ As (E := E) f m :=
  ⟨fun h => by simpa using bwd g f hN m hm _ h, fun h => fwd g f hN m hm v h⟩

end Lin

section Loc
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem X_eq (f : Fin (r + 1) → V) : H.X f = As (E := E) f r := by
  unfold HermSp.X As
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.castSucc, a.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, congrArg f (Fin.ext rfl)⟩

theorem flag_eq (f : Fin (r + 1) → V) (a : Fin r) :
    Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a}) = As (E := E) f a := by
  unfold As
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b.castSucc, (Fin.lt_def.mp hb : (b : ℕ) < a), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < r := lt_trans hi a.isLt
    exact ⟨⟨i, hi'⟩, Fin.lt_def.mpr hi, congrArg f (Fin.ext rfl)⟩

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)

theorem spanTo_eq (f : Fin (r + 1) → V) (j : ℕ) :
    S.spanTo (fun a => c.e (f a)) j = (As (E := E) f j).map (c.e : V →ₗ[E] S.V) := by
  unfold Frames.spanTo As
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem perp_eq (A : Submodule E V) :
    perp M.L S.Hm (A.map (c.e : V →ₗ[E] S.V)) = (H.perp A).map (c.e : V →ₗ[E] S.V) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  ext x
  rw [Submodule.mem_map_equiv]
  show (∀ y ∈ A.map (c.e : V →ₗ[E] S.V), hf M.L S.Hm x y = 0) ↔ ∀ y ∈ A, H.h (c.e.symm x) y = 0
  constructor
  · intro hx y hy
    rw [← hh, LinearEquiv.apply_symm_apply]
    exact hx _ (Submodule.mem_map_of_mem hy)
  · intro hx y hy
    rw [Submodule.mem_map_equiv] at hy
    have := hx _ hy
    rwa [← hh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this

end Loc

end GlobalTheory.HL.NUTransport

namespace GlobalTheory.HL.NUTransport

section Main
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem mem_unipOn_iff {n : ℕ} (A B : Submodule E (Fin n → E)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := Iff.rfl

theorem mem_hperp_iff (A : Submodule E V) (v : V) : v ∈ H.perp A ↔ ∀ x ∈ A, H.h v x = 0 := Iff.rfl

theorem mem_NU_iff_mem_Nof {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)
    (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) :
    g ∈ NU H f ↔ (c.e.symm.trans g).trans c.e ∈ S.Nof (fun a => c.e (f a)) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  have hU : (c.e.symm.trans g).trans c.e ∈ isomG M.L S.Hm ↔ LocNG.IsUnitary H g := by
    show (∀ x y, hf M.L S.Hm _ _ = hf M.L S.Hm x y) ↔ ∀ x y, H.h (g x) (g y) = H.h x y
    constructor
    · intro h x y
      have := h (c.e x) (c.e y)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hh] at this
      exact this
    · intro h x y
      have h1 := hh (g (c.e.symm x)) (g (c.e.symm y))
      have h2 := hh (c.e.symm x) (c.e.symm y)
      simp only [LinearEquiv.apply_symm_apply] at h2
      simp only [LinearEquiv.trans_apply]
      rw [h1, h2, h]
  have hN : ∀ n, n ∈ S.Nof (fun a => c.e (f a)) ↔ n ∈ isomG M.L S.Hm ∧
      (∀ j : Fin r, n ∈ unipOn (S.spanTo (fun a => c.e (f a)) ((j : ℕ) + 1)) (S.spanTo (fun a => c.e (f a)) j)) ∧
      n ∈ unipOn (perp M.L S.Hm (S.spanTo (fun a => c.e (f a)) r)) (S.spanTo (fun a => c.e (f a)) r) := by
    intro n
    simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, and_assoc]
  rw [hN, hU]
  simp only [spanTo_eq c f, perp_eq c, mem_unipOn_iff, unip_iff]
  show (LocNG.IsUnitary H g ∧ (∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
      ∀ v ∈ H.perp (H.X f), g v - v ∈ H.X f) ↔ _
  simp only [flag_eq, X_eq]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨hu, fun j => ⟨iff_of g f hfl _ j.isLt, step g f hfl j j.isLt⟩, ⟨fun v => ?_, hp⟩⟩
    rw [mem_hperp_iff, mem_hperp_iff]
    constructor
    · intro h x hx
      have := h (g x) ((iff_of g f hfl r le_rfl x).2 hx)
      rwa [hu] at this
    · intro h x hx
      have h1 := h (g.symm x) (bwd g f hfl r le_rfl x hx)
      rw [← hu v (g.symm x), LinearEquiv.apply_symm_apply] at h1
      exact h1
  · rintro ⟨hu, hj, -, hp⟩
    refine ⟨hu, fun a => (hj a).2 _ (Submodule.subset_span ⟨a.castSucc, ?_, rfl⟩), hp⟩
    show (a : ℕ) < (a : ℕ) + 1
    omega

end Main

end GlobalTheory.HL.NUTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRationalUnipotentOfLocalExtension
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocReflect

variable {D : D7}

theorem mem_of_baseChange_mem_span (p : PlF D) (W : Submodule D.host.E (VS D).V) {y : (VS D).V}
    (hy : baseChange₂ D p y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V))) : y ∈ W := by
  by_contra hyW
  obtain ⟨φ, hφy, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyW inferInstance
  let ψ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun v => ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * v i
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  have hψ : ∀ x, ψ (baseChange₂ D p x) = (D.s.atP p).ιE (φ x) := by
    intro x
    show ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * (D.s.atP p).ιE ((VS D).frame.repr x i) = _
    conv_rhs => rw [← (VS D).frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hle : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V)) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    show ψ (baseChange₂ D p w) = 0
    rw [hψ]
    have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
    rw [hφW, Submodule.mem_bot] at this
    rw [this, map_zero]
  have h0 : ψ (baseChange₂ D p y) = 0 := hle hy
  rw [hψ] at h0
  exact hφy ((map_eq_zero_iff _ (RingHom.injective (D.s.atP p).ιE)).1 h0)

theorem span_scaled_le (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (S : Set (Fin D.R.rS)) :
    Submodule.span (D.s.atP p).Ep ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' S) ≤
      Submodule.span (D.s.atP p).Ep
        (baseChange₂ D p '' ((Submodule.span D.host.E (F.fl.e '' S) : Submodule D.host.E (VS D).V) : Set (VS D).V)) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  show frFac Z.δ p b.castSucc • baseChange₂ D p (frame F b.castSucc) ∈ _
  rw [GlobalTheory.LocExt.frame_castSucc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩)

theorem mem_nrat_of_ext : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p),
    GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  intro D Z p T F γ g hE hN
  obtain ⟨hU, hfl, hperp⟩ := hN
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply RingHom.injective (D.s.atP p).ιE
    show (D.s.atP p).ιE (brS (VS D) (γ y) (γ x)) = (D.s.atP p).ιE (brS (VS D) y x)
    rw [← baseChangeAt_form Z.M p (Z.hcj p), ← baseChangeAt_form Z.M p (Z.hcj p), ← hE, ← hE]
    exact hU (baseChange₂ D p y) (baseChange₂ D p x)
  · intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : a.1 < j + 1 := ha
      have h1 := hfl a
      have e : g (scaled Z p (frame F) a.castSucc) - scaled Z p (frame F) a.castSucc =
          frFac Z.δ p a.castSucc • baseChange₂ D p (γ (F.fl.e a) - F.fl.e a) := by
        simp only [scaled, GlobalTheory.LocExt.frame_castSucc, map_smul, hE (F.fl.e a), map_sub, smul_sub]
      rw [e] at h1
      obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a.castSucc
      have h2 := Submodule.smul_mem _ ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) (span_scaled_le Z p F {b | b < a} h1)
      rw [← hu, smul_smul, Units.inv_mul, one_smul] at h2
      have h3 := mem_of_baseChange_mem_span p _ h2
      exact GlobalTheory.FlagChange.Xa_mono F.fl (Nat.lt_succ_iff.1 ha') h3
    | zero => simp
    | add x y _ _ ihx ihy =>
      have e : γ (x + y) - (x + y) = (γ x - x) + (γ y - y) := by rw [map_add (f := _)]; abel
      rw [e]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
      rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ ih
  · intro x hx
    have hb : baseChange₂ D p x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨a, rfl⟩ := hu
        show (locH Z p).h (baseChange₂ D p x) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) = 0
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]
        have h0 : (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0 := by
          show LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0
          rw [baseChangeAt_form Z.M p (Z.hcj p), GlobalTheory.LocExt.frame_castSucc]
          show (D.s.atP p).ιE ((VS D).hT (F.fl.e a) x) = 0
          rw [GlobalTheory.FlagChange.mem_orth_X.1 hx (F.fl.e a) (GlobalTheory.FlagChange.e_mem_X F.fl a), map_zero]
        rw [h0, mul_zero]
      | zero =>
        rw [(locH Z p).h_herm, (locH Z p).h_zero_left, map_zero]
      | add u v _ _ ihu ihv =>
        rw [(locH Z p).h_herm, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm, ← (locH Z p).h_herm, ihu, ihv,
          add_zero]
      | smul c u _ ih =>
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm, ih, mul_zero]
    have h2 := hperp _ hb
    rw [hE, ← map_sub] at h2
    have h3 : baseChange₂ D p (γ x - x) ∈ Submodule.span (D.s.atP p).Ep
        ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' Set.univ) := by
      rw [Set.image_univ]; exact h2
    have h4 := mem_of_baseChange_mem_span p _ (span_scaled_le Z p F Set.univ h3)
    rw [Set.image_univ] at h4
    exact h4

end GlobalTheory.LocReflect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToDeterminesUnipotentFactorisation
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameStep

theorem frame_mapLF {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem upUni_of_uni {N : ℕ} {K : Type} [Field K] {A : Matrix (Fin N) (Fin N) K} (h : GlobalTheory.LocOver.Uni A) :
    IsUpUni A := fun i j => ⟨fun hij => h.1 i j hij, fun hij => by subst hij; exact h.2 i⟩

theorem upUni_mul {N : ℕ} {K : Type} [Field K] {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A)
    (hB : IsUpUni B) : IsUpUni (A * B) := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul ..)

theorem unip_tri {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : ∃ A : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧
      ∀ b, n (frame F b) = ∑ a, A a b • frame F a := by
  have hmap : ∀ a, (mapFlag n hn.1 F.fl).fvec a = n (F.fl.fvec a) := by
    intro a
    induction a using Fin.lastCases with
    | last => simp [FlagG.fvec, mapFlag]
    | cast i => simp [FlagG.fvec, mapFlag]
  obtain ⟨A, hA, hc⟩ := GlobalTheory.FlagChange.tri_of_unip F.fl (mapFlag n hn.1 F.fl) n hn.2.1 hn.2.2 hmap
  refine ⟨A, upUni_of_uni hA, fun b => ?_⟩
  rw [← hmap b]
  exact hc b

theorem sum_change {D : D7} (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U A : Formalism.L2.SG.PairVal.MatR D) (hU : ∀ b, g (f b) = ∑ a, U a b • f0 a) (b : Fin (D.R.rS + 1)) :
    g (∑ a, A a b • f a) = ∑ c, (U * A) c b • f0 c := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hU, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem step : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM t n m ⟨hn, hm, ht⟩
  obtain ⟨hρ, hU, hU', hf, hf'⟩ := hM
  obtain ⟨A, hA, hnA⟩ := unip_tri _ n hn
  obtain ⟨A', hA', hmA'⟩ := unip_tri _ m hm
  have ht0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have ht1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  refine ⟨A, A', hA, hA', hnA, hmA', Subgroup.mul_mem _ hρ hn.1, upUni_mul hU hA, upUni_mul hU' hA', ?_, ?_⟩
  · intro b
    rw [LinearEquiv.mul_apply]
    exact (congrArg ρ (hnA b)).trans (sum_change ρ _ _ U A hf b)
  · intro b
    have h0 : ∀ a, (ρ * t₀.lin) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.mul_apply, ← hf' a]
      show _ = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
      rw [frame_mapLF _ ht0]
    have e1 : frame t.frame b = t.lin (frame (lf D (X.Fu u')) b) := frame_mapLF _ ht1 _ b
    rw [e1, ht]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
    have hinv : ∀ x, n (n⁻¹ x) = x := fun x => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [hinv, hmA' b]
    have := sum_change (ρ * t₀.lin) _ _ U' A' h0 b
    simpa only [LinearEquiv.mul_apply] using this

end GlobalTheory.FrameStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmp


open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants in
theorem bessel_schur_gap (hH : GlobalTheory.GapIn.Hyp) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hCl : 1000 ≤ Cl) : BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hZ
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine _root_.GlobalTheory.BesselSchurGap.bessel_schur hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl
    (fun _ _ _ _ _ h => GlobalTheory.BesselSchur.theta_pos D (by linarith) h) (fun w => ?_) hZ
  unfold Tr
  exact_mod_cast (D.mem w).A.T_prime.pos


open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S in
theorem schur_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT →
        OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  obtain ⟨C₀, hC⟩ := GlobalTheory.Amp.schurSt_of_big_tie Cg cb Cu cT CT C0 C1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := _root_.GlobalTheory.Amp.LocalInputsGap.locIn_of_hypGap hH Cg cb Cu cT CT C0
  refine ⟨C₀, 1000, fun eps Fm _ h2 _ => ?_⟩
  obtain ⟨x0, hx⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₀ m₁) 1)
  refine ⟨x0, fun x hxx i => ?_⟩
  obtain ⟨-, hmM, -, -, hrd, -⟩ := hx x hxx i
  have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ sCl Fm * ((Fm.D x i).R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm)
    (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) (Fm.ties x i).cdScale_tie
    (bessel_schur_gap hH _ _ _ _ _ _ _ _ _ _ h2)
    (hL _ _ _ _ (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _))))

end GlobalTheory.GapAmp
end

