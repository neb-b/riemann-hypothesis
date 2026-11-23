module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
section
noncomputable section

open scoped TensorProduct InnerProductSpace
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ColDict Matrix

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def WittX (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
    (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u

def IsAdeleIso (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) : Prop :=
  (∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
    Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (X.ιE x)) ∧
  ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ IntAf D.host.F D.host.E

def LatMatchH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∀ x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
    (h0⁻¹).1.1 *ᵥ x ∈
      Formalism.UG.latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Formalism.UG.tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Formalism.UG.intOE D.host.E)
          (Formalism.UG.intAd D.host.F)) F.cls0.lev.Lb ↔
    (∑ j, ιA.symm (x j) • qA X wt j) ∈ X.B.I.Lf

def LevelKH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y →
    (h ∈ Ku X u hK ↔ ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
      F.cls0.lev.U) ∧
    ∀ (hk : h ∈ Ku X u hK) (hy : ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U),
      ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ)

def JOK (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ)) : Prop :=
  (∀ s ∈ Hinf X u, ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
    Formalism.L2.Forms.IsTr (sTil X wt s) y' y → J (X.piU u s ξ) y = J ξ y') ∧
  (∀ ξ, J ξ ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0)) ∧
  ∀ (c : (D.mem u).C.cls 0) (ξ η : X.Vpi u),
    (D.fm u).ipV 0 c (fun z => J ξ (F.val0.eY z))
      (fun z => J η (F.val0.eY z)) = ⟪η, ξ⟫_ℂ

variable (D)

def WittExists : Prop := ∀ (X : HidaSetting D) (u : D.what₂.Word), ∃ wt, WittX X u wt

def GenusMatch (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA, WittX X u wt → IsAdeleIso X ιA →
    ∃ h0, LatMatchH X u (F u) wt ιA h0

def LevelConj (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    LatMatchH X u (F u) wt ιA h0 →
    ∃ h0', LatMatchH X u (F u) wt ιA h0' ∧ LevelKH X u (F u) wt ιA h0' hK

def HcExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    ∀ c : (D.mem u).C.cls 0, ∃ h : Hfin X u,
      RepF X wt ιA (h : X.B.I.Gf) ((F u).cls0.y c * h0⁻¹)

def JExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt →
    ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u (F u) wt J

def RescaleStep3 : Prop :=
  ∀ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I), X.MeasTie hb →
    ∃ (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS) (hg : mg.IsTextNorm)
      (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
        (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
          crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
      (hw : ∀ u, (mw u).IsTextNorm),
      (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw).MeasTie hb ∧
      ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ ∧
        ∀ w, Formalism.L2.SG.LocVol.LocCompatX (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ w

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

def ColDictCore : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter),
    LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) →
      ClsMatch X Tr hK ∧ ColDictInto X Tr hK ∧ ColDictBij X Tr hK ∧
      ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂)
        (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)),
        Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj

end GlobalTheory.St

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UnitriangularLatticeStabiliserSubFrameAutomorphi
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_one (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) Λ = Λ := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul (a b : GV D) (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem adapt_one {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Adapt (1 : GV D) F F :=
  ⟨Subgroup.one_mem _, fun a => by simp⟩

theorem unitriangular_lattice_stabiliser_sub_frame_automorphisms {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : LV D) : NLam Λ F ⊆ Aut0 F Λ := by
  rintro n ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨h1, fun a => ?_⟩, h2⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, frame, FlagG.fvec, Fin.snoc_last, LinearMap.mem_ker]
      intro x hx
      refine Submodule.span_induction (p := fun x _ => (VS D).hT x F.fl.z = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, rfl⟩; exact F.fl.z_orth a
      · simp
      · intro x y _ _ a b; simp [a, b]
      · intro c x _ a; simp [a]
    have := h4 _ hz
    have e : Xflag F (Fin.last D.R.rS).val = Xsp F := by
      simp only [Xflag, FlagG.Xa, Xsp, FlagG.X, Fin.val_last]
      congr 1; ext v; simp
    rwa [e]
  · apply h3
    apply Submodule.subset_span
    exact ⟨i, by simp, by simp [frame, FlagG.fvec]⟩

section
variable {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

theorem mem_gmap (h : GV D) (Λ : LV D) (x) : x ∈ Formalism.HermitianLatticesTheory.gmap h Λ ↔ h.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem gmap_sup (h : GV D) (A B : LV D) : Formalism.HermitianLatticesTheory.gmap h (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap h A ⊔ Formalism.HermitianLatticesTheory.gmap h B :=
  Submodule.map_sup _ _ _

variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}

theorem h_add_right (p : PlF D) (x y y' : Vp D p) : (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _ + LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (p : PlF D) (c) (x y : Vp D p) : (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  show LocFacts₂ _ _ _ _ = _ * LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_unitary {p : PlF D} {h : GV D} (hh : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {g} (hg : Ext p h g) :
    LocNG.IsUnitary (locH Z p) g := by
  have key : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) = (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hg, hg]
    show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _
    rw [baseChangeAt_form _ _ (Z.hcj p), baseChangeAt_form _ _ (Z.hcj p)]
    simp only [brS]; rw [hh]
  have z1 : ∀ y, (locH Z p).h 0 y = 0 := fun y => by
    have := (locH Z p).h_smul_left 0 0 y; simpa using this
  have z2 : ∀ x, (locH Z p).h x 0 = 0 := fun x => by
    have := h_smul_right (Z := Z) p 0 x 0; simpa using this
  intro x y
  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  have hy : y ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero, z1, z1]
  | add a b _ _ ha hb => rw [map_add (f := _), (locH Z p).h_add_left, (locH Z p).h_add_left, ha, hb]
  | smul c a _ ha => rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, ha]
  | mem a ha =>
    obtain ⟨a, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | zero => rw [map_zero, z2, z2]
    | add a b _ _ ha hb => rw [map_add (f := _), h_add_right, h_add_right, ha, hb]
    | smul c a _ ha => rw [map_smul, h_smul_right, h_smul_right, ha]
    | mem b hb => obtain ⟨b, rfl⟩ := hb; exact key a b

end

section
variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {Tn T'n : ℕ}
  {F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)} {F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)}

end

section
variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

end

end GlobalTheory.Unfold.Model
end
end

