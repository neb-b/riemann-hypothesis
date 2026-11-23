module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0011

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyTie
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem intN_massDataY : (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN = IntNX X u u' ψ := rfl

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def nfE (D : D7) : ℕ := Fintype.card (InfinitePlace D.host.E)

def plE (D : D7) : Fin (nfE D) ≃ InfinitePlace D.host.E := (Fintype.equivFin _).symm

def tauE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Fin (nfE D) ≃ InfinitePlace X.B.I.F :=
  (plE D).trans (e.trans X.pl.symm)

def embE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) : D.host.E →+* ℂ :=
  (X.B.I.φ (tauE X e j)).comp X.ιE.symm.toRingHom

def PlaceTie (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Prop :=
  ∀ x : InfinitePlace D.host.E, InfinitePlace.mk ((X.B.I.φ (X.pl.symm (e x))).comp X.ιE.symm.toRingHom) = x

theorem hembE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (h : PlaceTie X e) (j : Fin (nfE D)) :
    InfinitePlace.mk (embE X e j) = plE D j := h (plE D j)

def castLoc (u : D.what₂.Word) {v w : InfinitePlace X.B.I.F} (h : v = w) : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u w := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

theorem tauE_symm (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (v : InfinitePlace X.B.I.F) :
    X.pl.symm (e (plE D ((tauE X e).symm v))) = v := by
  simp [tauE]

def carrierInOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    CarrierIn X u u' where
  Wp := fun x => X.Vloc u (X.pl.symm (e x))
  Wq := fun x => X.Vloc u' (X.pl.symm (e x))
  nf := nfE D
  pl := plE D
  emb := embE X e
  hemb := hembE X e he
  G := Formalism.L2.SG.SpectralTiesReal.gOf D e
  CA := CA
  de := de
  de' := de'
  l := l
  grid := grid
  grid1 := grid1
  hv := hv
  T := T
  hT := hT
  fc := fc
  χ := χ
  sg := sg
  ν' := ν'
  m₀ := m₀
  top := top
  A₀ := A₀
  τ := tauE X e
  Q := fun v => Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  Qi := fun v => Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  eP := fun v => castLoc X u (tauE_symm X e v)
  eQ := fun v => castLoc X u' (tauE_symm X e v)

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCMT2 (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCMT2

section hermitianSpaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuilt_of_builtPlace {Cb Cc : ℝ} {S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq}
    {p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    Formalism.FourierDecayAlt.D.IsBuilt S (Formalism.FourierDecayAlt.KB.plT S p) f χ (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (Formalism.FourierDecayAlt.KB.plTop S p) A₀ := by
  obtain ⟨⟨-, -, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩, hE, -⟩ := h
  exact ⟨hχ, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩

end hermitianSpaces

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CarrierDataBound (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn CA : ℝ)
    (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) (C₆ Cc Cb : ℝ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wp x))
    (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (A₀ : ℝ) (c : Formalism.FourierDecayAlt.LE.Cut)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧ Formalism.L2.SG.DataInst.Compat S u u' ∧
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀ ∧ Formalism.FourierDecayAlt.JCT.SliceBudget S A₀ ∧ c.χ = χ ∧
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) ∧
    Formalism.FourierDecayAlt.JCT.VtTensor S (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (VtPt X u u' sc i0 i0' FdN FdN' νq) ∧
    BuiltFromX X S u u' (Formalism.FourierDecayAlt.KB.plT S p) f τ Q Qi eP eQ ∧
    BaseFromX X S u u' i0 i0' τ Q Qi (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧
    VJoint X S u u' sc i0 i0' νq (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) τ eP eQ ∧
    ∀ (L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
        (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r)
      (j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
        Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ)
      (Cm σ : Fin S.f → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace S (Formalism.FourierDecayAlt.KB.plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel S j Cm v) = jn

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTEquiv
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sm_stable_uh (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  obtain ⟨gg, rfl⟩ := Formalism.IndefR.Eqv.KerDiag.gt_of_uh τ M hg
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ gg hw

abbrev comp (a : GA D V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) a


open Classical in
def translS (a : GA D V) (s : Finset D.what₂.Tau) (v : M.Vec) : M.Vec := fun τ =>
  if τ ∈ s then ⟨M.rep τ (comp a τ) (v τ), sm_stable_uh M τ (Formalism.IndefR.Eqv.infMat_unitary' D V a τ) (v τ).2⟩
  else v τ

def transl (a : GA D V) (v : M.Vec) : M.Vec := translS M a Finset.univ v

theorem transl_apply (a : GA D V) (v : M.Vec) (τ : D.what₂.Tau) :
    (transl M a v τ : M.H τ) = M.rep τ (comp a τ) (v τ) := by
  simp [transl, translS]

variable {M}

theorem equiv_ginf {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {T : MMap M}
    (hT : Formalism.IndefR.AutomorphicEvaluation.EqCont θ M T) {a : GA D V} (ha : a ∈ GinfC V) (v : M.Vec) (y : GA D V) :
    T v (y * a) = T (transl M a v) y := by
  classical
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => comp a τ with hgsd
  have hgs : Formalism.IndefR.Eqv.IsUnitFam D V gs := Formalism.IndefR.Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, ∀ y, T v (y * Formalism.IndefR.Eqv.famH D V _ (hu s)) = T (translS M a s v) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu ∅) = 1 := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_one]
        convert Formalism.IndefR.Eqv.famM_one D V using 2
        funext τ
        simp
      have e2 : translS M a ∅ v = v := by
        funext τ; simp [translS]
      rw [e, mul_one, e2]
    | insert τ0 s hτ0 ih =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu (insert τ0 s)) =
          Formalism.IndefR.Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Formalism.IndefR.Eqv.famH D V _ (hu s) := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_mul, Formalism.IndefR.Eqv.matA_atH, Formalism.IndefR.Eqv.matA_famH]
        apply Formalism.IndefR.Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Formalism.IndefR.Eqv.psi_famM, Formalism.IndefR.Eqv.psi_atM, Formalism.IndefR.Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Formalism.IndefR.Eqv.fin_famM, Formalism.IndefR.Eqv.fin_atM, Formalism.IndefR.Eqv.fin_famM,
            Matrix.one_mul]
      rw [e, ← mul_assoc, ih]
      have hw : M.rep τ0 (gs τ0) ((translS M a s v τ0 : M.H τ0)) ∈ M.sm τ0 :=
        sm_stable_uh M τ0 (hgs τ0) (translS M a s v τ0).2
      have hq := hT.equiv τ0 (gs τ0) (hgs τ0) (translS M a s v) ⟨_, hw⟩ rfl
      have hq' := congrFun hq y
      simp only [rTr] at hq'
      rw [Formalism.IndefR.Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)] at hq'
      rw [← hq']
      refine congrFun (congrArg T ?_) y
      funext τ
      by_cases h : τ = τ0
      · subst h
        rw [Function.update_self]
        apply Subtype.ext
        simp [translS, hτ0, hgsd]
      · rw [Function.update_of_ne h]
        simp [translS, h]
  have e : a = Formalism.IndefR.Eqv.famH D V _ (hu Finset.univ) :=
    Formalism.IndefR.Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  conv_lhs => rw [e]
  exact key Finset.univ y

section Read

variable {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Read

end Formalism.L2.SG.EvalTEquiv

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Eqv Formalism.IndefR
open scoped TensorProduct

namespace Formalism.L2.SG.EvalTIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def uM' (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (v : InfinitePlace D.host.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ := uMat (x.1 v)

def Pi (v : InfinitePlace D.host.F) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (Formalism.IndefR.RationalEmbedding.inst D).P v

theorem P_isUnit_det' (v : InfinitePlace D.host.F) : IsUnit (Pi (D := D) v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)

theorem thetaV_eq_psiT_i (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : (Formalism.IndefR.RationalEmbedding.inst D).φ (Formalism.L2.Host.tauPl D ρ) x = tauE D ρ x := by
      show Formalism.MainNotions.S.embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = _
      rw [Equiv.symm_apply_apply]
      rfl
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem infMat_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig (D.sp.Y 0).gram (thetaC D ρ) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM' x (Formalism.L2.Host.tauPl D ρ) = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (psiT D ρ) *
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT_i ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC_i {M : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : x.1 = 1 ↔ ∀ v, uM' x v = 1 := by
  constructor
  · intro h v
    show uMat (x.1 v) = 1
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ x.1 = 1 := by
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff_i]
  have hc : ∀ ρ, ((matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D)).map (thetaC D ρ) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg_i, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
    have e' : Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM' x (Formalism.L2.Host.tauPl D ρ)
        = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹) * Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC_i
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det' _)]

theorem tauF_eq_i : Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : Lev.finE (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = (x.2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq_i] at hb
  exact hb.symm

theorem iota_symm_mem_GinfC (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) :
    (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GinfC (D.sp.Y 0) ↔ x.2 = 1 := by
  show finHom (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = 1 ↔ _
  rw [Formalism.IndefR.Eqv.finHom_eq_one_iff, finE_brg_i]
  constructor
  · intro e
    exact Subtype.ext e
  · intro e
    rw [e]
    rfl

end Formalism.L2.SG.EvalTIota

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBFrame
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal

namespace Formalism.L2.SG.Pf.LoopBFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem rowLat_fl' {u u' : D.what₂.Word} (t : D.s.Term u u') :
    IsRowLat D (fl'Of W hI t).fl (lamOf W hI t) := by
  have hR := rowLat_map (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) (W.δ u) (W.isom u) (X.Fu u) _ (rowLat_tc hI t)
  have hFx := fixedC W hI (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) t
  obtain ⟨hLift, -, hOK⟩ := pdC W hI t
  exact ⟨hR.1, ⟨hFx.1, hFx.2.1, ⟨hLift.1, rfl⟩, hOK.1⟩, hOK.2⟩

theorem frameChangeAt_holds : FrameChangeAt W hI := by
  intro u u' t ξ hl hd
  obtain ⟨n, hn, hnf⟩ := Formalism.L2.S.Pv.ClassCounting.frameOpFull D u' (fl'Of W hI t).fl (lamOf W hI t) (rowLat_fl' W hI t) ξ hl hd
  exact ⟨n, hn, fun b => hnf b⟩

theorem frameChangeC_holds : FrameChangeC := fun _ _ _ _ hI W => frameChangeAt_holds W hI

end Formalism.L2.SG.Pf.LoopBFrame
end
end

