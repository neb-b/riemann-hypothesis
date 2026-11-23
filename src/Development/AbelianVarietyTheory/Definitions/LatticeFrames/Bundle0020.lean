module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def scT {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) : PB.Terms τ Rw I H H₁ :=
  { X with scal := fun _ _ => True }

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def cls1 (t : TauC Y u u) : Set (TauC Y u u) :=
  {t' | t' ∈ (Y.tO u u).genSet ∧ (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t ∧ (Y.tO u u).s0 t t' = 1}

def NOf1 (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.NGData (TauC Y u u) D.host.E D.R.rS (Set (TauC Y u u)) (NuC D) :=
  { NOfG Y u νL νB ng with
    cls := cls1 Y u
    a2 := GlobalTheory.SnFam.a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL }

def GeneratorBoundAt (Γ : ℝ) : Prop := (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).genSet) ≤ Γ * ddC X Y u u

end Conc

def CorankOneIsEquivalenceOnRow : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').s0 t t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, ∀ t'' ∈ (Y.tO u u').nzSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').s0 t t'' = 1)

def StepClass1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
      PN.ClassInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)

def StepNormals1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def FamGen1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    GlobalTheory.SnFam.FamQ Y u u Not (Y.tO u u).genSet (cls1 Y u)

def StepFam1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

def StepLoc1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

def RowGen1P : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u → ConcTie X Y → (Y.tO u u).AbsConv →
      GeneratorBoundAt Y u (gamB D large₂ CB)

end GlobalTheory.Core.One
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_cartan {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n ≃ m) {C : Matrix m (Fin n) ℂ}
    {J : Matrix m m ℂ} {G : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J) (hG : IsUnit G.det)
    (h : Cᴴ * J * C = G) : ∃ s, IsCartanInv G s ∧ C * s = J * C := by
  have h1 : G⁻¹ * Cᴴ * J * C = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h, Matrix.nonsing_inv_mul _ hG]
  generalize G⁻¹ * Cᴴ * J = C' at h1
  have h2 : C * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h3 : C * (C' * J * C) = J * C := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : G * (C' * J * C) = Cᴴ * C := by
    rw [← h, Matrix.mul_assoc, h3, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJ, Matrix.one_mul]
  refine ⟨C' * J * C, ⟨?_, ?_, ?_⟩, h3⟩
  · rw [Matrix.mul_assoc (C' * J), h3, Matrix.mul_assoc C', ← Matrix.mul_assoc J, hJ, Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, h4, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_mul, hJ', h]
  · rw [h4]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have := congrArg (C' *ᵥ ·) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this

theorem gramAt_unit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).map _

theorem isSplit_two (v : FinPl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w, hw⟩
  · exact hs
  · exfalso
    unfold Formalism.UG.IsInertAt at hw
    obtain ⟨ω, k, hω, hc⟩ := GlobalTheory.SplitIdem.exists_omega D
    let c : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.sp.cm.sig.toRingHom
    have hst : ∀ x ∈ w.asIdeal, c x ∈ w.asIdeal := by
      have : w.asIdeal ≤ w.asIdeal.comap c := by
        conv_lhs => rw [← hw]
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have e : c (algebraMap _ _ a) = algebraMap _ _ a := Subtype.ext (D.sp.cm.sig.commutes a)
        rw [Ideal.mem_comap, Ideal.mem_comap, e, ← hw]
        exact Ideal.mem_map_of_mem _ ha
      exact this
    have hcω : c ω = 1 - ω := RingOfIntegers.ext (by
      change star (ω : D.host.E) = _
      rw [GlobalTheory.SplitIdem.star_eq_conj, hc]; simp)
    have h2' : (2 : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hw, ← map_ofNat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) 2]
      exact Ideal.mem_map_of_mem _ h2
    have hp : ω * (1 - ω) = 2 * k := RingOfIntegers.ext (by
      push_cast at hω ⊢
      simp only [map_mul, map_sub, map_one, map_ofNat, map_natCast]
      linear_combination -hω)
    have hone : ω ∈ w.asIdeal → False := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by have := add_mem h (hcω ▸ hst ω h); rwa [add_sub_cancel] at this))
    rcases w.isPrime.mem_or_mem (hp ▸ Ideal.mul_mem_right _ _ h2') with h | h
    · exact hone h
    · have := hst _ h
      rw [map_sub, map_one, hcω, sub_sub_cancel] at this
      exact hone this

theorem isSphOff_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T}
    {LS : Lat S} {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) (Sf : Finset (FinPl D)) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT Sf Φ ∧ Φ ≠ 0 := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    AddSubgroup.closure_mono fun _ ⟨α, h1, _, h3⟩ => ⟨α, h1, fun _ h => absurd trivial h, h3⟩
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, ⟨fun u hu => h.2.lat.1 u (hle hu), fun e he u hu => h.2.lat.2 e he u (hle hu)⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    exact h.2.fock p.1 p.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h'⟩ := h.2.norm
    simpa [nrm2] using h' p hp

section Coef

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B} {ν : Measure (WO A B)}
  {𝓕 : Set (WO A B)} {Φ₁ Φ₂ : WO A B → ℂ}

end Coef

end GlobalTheory.Core.Rk.IP.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

structure Places {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop) : Prop where
  nodup : I.Nodup
  all : ∀ i, i ∈ I
  inj : Function.Injective fun i => (p i).v
  mem : ∀ x, P x ↔ ∃ i, x = (p i).v
  unit : ∀ i, (p i).UnitAA

def OpAt (P : Pl D → Prop) {A S A' : HSp D} (op : BiOp A S A') : Prop := ∀ i, CombAt P (op.u i) ∧ CombAt P (op.u' i)

def Reps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ)
    {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T)
    (Ψ : ι → Matrix n n' k → ℂ) (I : List ι) (P : Pl D → Prop) (c : WO S T →₀ ℂ) : Prop :=
  CombAt P c ∧ ∀ f, Vac ψ S T LS LT P f → OverAll ψ α β LS LT Ψ I f (comb ψ S T c f)

def smallPair {V₀ A L S T : HSp D} (o : OrthDec V₀ A L) (om₁ : Om V₀ S) (omT : Om S T) (vA : Vol A) (vS : Vol S) (vT : Vol T)
    (φ : GA D A → ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (F : GA D T → ℂ) : ℂ :=
  ∫ h' in vT.𝓕, F h' * (∫ h in vS.𝓕, omT (h, h') Φ₂ 0 * liftA o om₁ vA φ Ξ h 0 ∂vS.μ) ∂vT.μ

def AllComb (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → ∀ Ψ : ι → Matrix n n' k → ℂ,
      ((∀ i, Ψ i ∈ SB (Matrix n n' k)) → ∃ c, Reps ψ α β LS LT Ψ I P c) ∧
      (∀ f f' f'', OverAll ψ α β LS LT Ψ I f f' → OverAll ψ α β LS LT Ψ I f f'' → f' = f'') ∧
      ∀ d : WO S T →₀ ℂ, CombAt (fun x => ¬ P x) d → ∀ f, Vac ψ S T LS LT P f → Vac ψ S T LS LT P (comb ψ S T d f) ∧
        ∀ f', OverAll ψ α β LS LT Ψ I f f' → OverAll ψ α β LS LT Ψ I (comb ψ S T d f) (comb ψ S T d f')

def RebaseAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS MS : Lat S) (LT MT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT →
    ∃ e e' : WO S T →₀ ℂ, CombAt P e ∧ CombAt P e' ∧ ∀ f, Vac ψ S T LS LT P f →
      Vac ψ S T MS MT P (comb ψ S T e f) ∧ comb ψ S T e' (comb ψ S T e f) = f ∧
      ∀ Ψ f', OverAll ψ α β LS LT Ψ I f f' ↔ OverAll ψ α β MS MT Ψ I (comb ψ S T e f) f'

def LatAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S : HSp D) (α : ∀ i, Frame (p i) S n) (L : Lat S), IsSelfDualC S L →
    ∀ Λ : ι → Submodule 𝒪[k] (n → k), (∀ i, (Λ i).IsFullLattice k) →
    ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i, (α i).IsLat M (Λ i)) ∧ ∀ x, ¬ P x → latV S M (· = x) = latV S L (· = x)

def ExtAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    ∀ (α : ∀ i, Frame (p i) A n') (α₀ : ∀ i, Frame (p i) S (n' ⊕ Fin 1)) (β : ∀ i, Frame (p i) T n),
    (∀ i, IsSumFrame o ζ (α i) (α₀ i)) → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : ι → Submodule 𝒪[k] (n' → k))
      (ΛT : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT →
      (∀ i, (α i).IsLat LA (ΛA i) ∧ (α₀ i).IsLat LS (lastKer (ΛA i)) ∧ (β i).IsLat LT (ΛT i)) →
      (∀ x, P x → ∃ LL, OrthAt o LS LA LL x) ∧
      (∀ Ψ c, Reps ψ α β LA LT Ψ I P c → Reps ψ α₀ β LS LT (fun i => tensCol (Ψ i) (vecInd (ΛT i))) I P (extS o T c)) ∧
      ∀ Ψ c, Reps ψ β α LT LA Ψ I P c → Reps ψ β α₀ LT LS (fun i => tensRow (Ψ i) (dualInd (ΛT i))) I P (extT o T c)

def ContrOp (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank)
      (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'')
      (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀)
      (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)),
      IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' →
      (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧
        (γ₀ i).IsLat M' (lastKer (Λ' i))) →
      ∀ (e₁ : WO B.V₀ S →₀ ℂ) (e₂ : WO S B'.V₀ →₀ ℂ), CombAt P e₁ → CombAt P e₂ →
      ∃ op : BiOp B.A S B'.A, OpAt P op ∧ ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ →
        GlobalTheory.Unf.contr l S vL (comb ψ _ _ e₁ f₁) (comb ψ _ _ e₂ f₂) = op.app ψ (GlobalTheory.Unf.contr l S vL f₁ f₂)

def BiInv (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (op : BiOp A S A'), OpAt P op →
    (∀ (LA : Lat A) (LS : Lat S) (LA' : Lat A'), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC A' LA' →
      (∀ C, BiVacAt ψ LA LS LA' P C → op.app ψ C = 0) ∨
        ∃ op' : BiOp A S A', OpAt P op' ∧ ∀ C, BiVacAt ψ LA LS LA' P C → op'.app ψ (op.app ψ C) = C) ∧
    ∀ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ), CombAt P e → CombAt P e' →
      ∃ op' : BiOp A S A', OpAt P op' ∧ ∀ C, op'.app ψ C = biComb ψ A S A' e e' (op.app ψ C)

def LastOp (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ P : Pl D → Prop,
    (∀ e : WO V₀ S →₀ ℂ, CombAt P e → ∃ op : BiOp A S X, OpAt P op ∧ ∀ Ξ Φ₂,
      lastBi o o'' τ (comb ψ V₀ S e Ξ) Φ₂ = op.app ψ (lastBi o o'' τ Ξ Φ₂)) ∧
    ∀ (d : WO A S →₀ ℂ) (d' : WO S X →₀ ℂ), CombAt P d → CombAt P d' →
      ∃ (N : ℕ) (a : Fin N → WO V₀ S →₀ ℂ) (b : Fin N → WO S T →₀ ℂ), (∀ i, CombAt P (a i) ∧ CombAt P (b i)) ∧ ∀ Ξ Φ₂,
        biComb ψ A S X d d' (lastBi o o'' τ Ξ Φ₂) = ∑ i, lastBi o o'' τ (comb ψ V₀ S (a i) Ξ) (comb ψ S T (b i) Φ₂)

def SeeSmall (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → CoCpt A → CoCpt S → CoCpt T →
    ∀ (χA χz χS χS' χT : (AE D)ˣ →* Circle) (om₁ : Om V₀ S) (oma : Om A S) (omz : Om L S) (omX : Om S X) (omT : Om S T)
      (omz'' : Om S L''), IsWeilDatumO ψ V₀ S (χA * χz) χS om₁ → IsWeilDatumO ψ A S χA χS oma →
      IsWeilDatumO ψ L S χz χS omz → IsWeilDatumO ψ S X χS' (χT * χz⁻¹) omX → IsWeilDatumO ψ S T χS' χT omT →
      IsWeilDatumO ψ S L'' χS' χz⁻¹ omz'' → ∀ (vA : Vol A) (vS : Vol S) (vT : Vol T) (N : ℕ) (Ξ : Fin N → WO V₀ S → ℂ)
      (Φ₂ : Fin N → WO S T → ℂ), (∀ i, IsThetaFunO ψ V₀ S (Ξ i) ∧ IsThetaFunO ψ S T (Φ₂ i)) →
      ∀ φ F, IsContAut A φ → IsContAut T F →
        ∫ h' in vT.𝓕, F h' * biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) ∂vT.μ =
          ∑ i, smallPair o om₁ omT vA vS vT φ (Ξ i) (Φ₂ i) F

def LastTAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), (∀ i, (p i).IsChar ψ (χ i)) →
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E)
      (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ →
    ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), τ *ᵥ ζ₀ = lam • ζ →
      (∀ i, valuation k ((p i).pr (incA D lam)) = 1) → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
    ∃ ε : ι → 𝓀[k]ˣ, ∀ (α : ∀ i, Frame (p i) A n') (α₀ : ∀ i, Frame (p i) V₀ (n' ⊕ Fin 1)) (β : ∀ i, Frame (p i) S n)
      (γ : ∀ i, Frame (p i) T n'') (γ₀ : ∀ i, Frame (p i) X (n'' ⊕ Fin 1)),
      (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ IsSumFrame o'' ζ₀ (γ i) (γ₀ i)) →
      ∀ (Q : ι → Pair k n) (Λ : ι → Submodule 𝒪[k] (n'' → k)) [∀ i, (Λ i).IsFullLattice k] (Ψ : ι → Matrix n n' k → ℂ) (LA : Lat A)
        (LS : Lat S) (LT : Lat T) (LX : Lat X) (L₁ : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT →
        IsSelfDualC X LX → IsSelfDualC V₀ L₁ → (∀ i, (β i).IsLat LS (Q i).lat ∧ (γ i).IsLat LT (Λ i)) →
      ∀ c c', Reps ψ α β LA LS Ψ I P c → Reps ψ β γ₀ LS LX (fun i => phiOne (ε i • Q i) (lastPair q (Λ i))) I P c' →
      ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt P e ∧ CombAt P e' ∧ ∀ (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ),
        Vac ψ V₀ S L₁ LS P f₁ →
        OverAll ψ α₀ β L₁ LS (fun i => tensCol (Ψ i) (charInd (resChar (χ i) (hχ i) q) (Q i))) I f₁ Ξ → Vac ψ S T LS LT P Φ₂ →
        BiVacAt ψ LA LS LX P (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧
          lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂))

def SmallOne (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1),
    ∃ (r : ℝ) (e : ℤ), 0 < r ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S T : HSp D) (o : OrthDec V₀ A L)
      (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → CoCpt S → CoCpt T →
      ∀ (χV χW χS χT : (AE D)ˣ →* Circle) (om₁ : Om V₀ S) (omT : Om S T), IsWeilDatumO ψ V₀ S χV χW om₁ →
      IsWeilDatumO ψ S T χS χT omT → CharUnramAt D χV p.v → CharUnramAt D χW p.v → CharUnramAt D χS p.v → CharUnramAt D χT p.v →
      ∀ (vA : Vol A) (vS : Vol S) (vT : Vol T) (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n),
      IsSumFrame o ζ α α₀ → ∀ (P : Pair k n') (Q : Pair k n) (s : 𝓀[k]ˣ) (L₁ : Lat V₀) (L₂ L₂' : Lat S) (L₃ : Lat T)
        (f₁ Ξ Ξ' : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (charInd (resChar χ hχ q) (s • Q))) Ξ' →
        IsSelfDualC S L₂' → IsSelfDualC T L₃ → β.IsLat L₂' Q.lat → Vac ψ S T L₂' L₃ (· = p.v) Φ₂ →
        ∀ φ, RamAt α P φ → ∀ F, IsContAut T F → smallPair o om₁ omT vA vS vT φ Ξ Φ₂ F =
          (r : ℂ) * chrPow χW (p.idele q.unit) e * smallPair o om₁ omT vA vS vT (sOp α P q (resChar χ hχ q) s φ) Ξ' Φ₂ F

def SmallAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    ∃ (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S T : HSp D) (o : OrthDec V₀ A L)
      (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → CoCpt S → CoCpt T →
      ∀ (χV χW χS χT : (AE D)ˣ →* Circle) (om₁ : Om V₀ S) (omT : Om S T), IsWeilDatumO ψ V₀ S χV χW om₁ →
      IsWeilDatumO ψ S T χS χT omT →
      (∀ x, P x → CharUnramAt D χV x ∧ CharUnramAt D χW x ∧ CharUnramAt D χS x ∧ CharUnramAt D χT x) →
      ∀ (vA : Vol A) (vS : Vol S) (vT : Vol T) (a : PairDat p A V₀ n') (b : MidDat p S n) (s : ι → 𝓀[k]ˣ) (L₁ : Lat V₀)
        (L₂ : Lat S) (L₃ : Lat T), IsSelfDualC V₀ L₁ → IsSelfDualC S L₂ → IsSelfDualC T L₃ →
        (∀ i, IsSumFrame o ζ (a.α i) (a.α₀ i) ∧ (a.α₀ i).IsLat L₁ (gluedS q 1 (a.P i).ker (a.P i).vec) ∧
          (b.β i).IsLat L₂ (b.Q i).lat) →
        ∀ Ξ Ξ' Φ₂, Vac ψ V₀ S L₁ L₂ P Ξ → Vac ψ S T L₂ L₃ P Φ₂ →
        OverAll ψ a.α₀ b.β L₁ L₂
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i))) I Ξ Ξ' →
        ∀ φ, a.Ram φ → ∀ F, IsContAut T F → smallPair o om₁ omT vA vS vT φ Ξ Φ₂ F =
          (I.map fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i)).prod *
            smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s I φ) Ξ' Φ₂ F

def VertexAll (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    (∀ i, (p i).IsChar ψ (χ i)) → ∃ ε : ι → 𝓀[k]ˣ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], ∃ (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧
    ∀ (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), (∀ x, P x → UnrAt s₁ x ∧ UnrAt s₂ x) →
      ∀ (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n'') (M₀ : Lat B.V₀) (M₁ : Lat J.W₀)
        (M₂ : Lat B'.V₀), IsSelfDualC _ M₀ → IsSelfDualC _ M₁ → IsSelfDualC _ M₂ →
        (∀ i, GluedCore B M₀ q (a.α i) (a.α₀ i) (a.P i) ∧ GluedCore B' M₂ q (a'.α i) (a'.α₀ i) (a'.P i) ∧
          (b.β i).IsLat M₁ (b.Q i).lat) →
        ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ P Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M₂ P Ξ₂ → ∀ Ξ₁' Ξ₂',
          OverAll ψ a.α₀ b.β M₀ M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁' →
          OverAll ψ b.β a'.α₀ M₁ M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂' →
          ∀ φ, a.Ram φ → hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
            (I.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
              hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ) Ξ₁' Ξ₂'

def FlatVac (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W)
      (LW₀ : Lat J.W₀), (∀ x, P x → GoodBF ψ B J LV LV₀ LW LW₀ x) → ∀ Φ, Vac ψ B.V J.W LV LW P Φ →
      Vac ψ B.V₀ J.W₀ LV₀ LW₀ P (flatBF s Φ)) ∧
    (∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V)
      (LW₀ : Lat B.V₀), (∀ x, P x → AdaptFB ψ J B LV LV₀ LW LW₀ x) → ∀ Φ, Vac ψ J.W B.V LV LW P Φ →
      Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s Φ)) ∧
    ∀ (V V₀ T : HSp D) (d : HypDec V V₀ 0) (L : Lat V) (L₀ : Lat V₀) (LT : Lat T), IsSelfDualC V L → IsSelfDualC V₀ L₀ →
      IsSelfDualC T LT → (∀ x, P x → MonoAt d L L₀ x) → ∀ Φ, Vac ψ V T L LT P Φ → Vac ψ V₀ T L₀ LT P fun w => Φ (d.ext0 T w)

def LastVac (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
    ∀ (P : Pl D → Prop) (M : Lat V₀) (LA : Lat A) (LS : Lat S) (LX : Lat X) (LT : Lat T), IsSelfDualC V₀ M → IsSelfDualC A LA →
      IsSelfDualC S LS → IsSelfDualC X LX → IsSelfDualC T LT →
      (∀ x, P x → Tame D x ∧ ∃ (LL : Lat L) (LZ : Lat L''), IsSelfDualC L LL ∧ IsSelfDualC L'' LZ ∧ OrthAt o M LA LL x ∧
        OrthAt o'' LX LT LZ x ∧ ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x),
          kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) →
      ∀ Ξ Φ₂, Vac ψ V₀ S M LS P Ξ → Vac ψ S T LS LT P Φ₂ → BiVacAt ψ LA LS LX P (lastBi o o'' τ Ξ Φ₂)

end GlobalTheory.FinPl

end
end

