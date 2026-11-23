module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeLineRamifiedFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.LevProd

theorem prX_le_KO_of_prCat (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (hle : prCat (Pr := Pr) cst.sharp j P.1 γ ≤ GLint X.E (R.N j) P.1) :
    prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ KO k _ := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
    GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P.1 ι hcompl.int e' y
  have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
    (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ KO k _ := hy.2
  have hyC : φ' y ∈ prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
  have := mul_mem hyK hy2; simpa using this

end GlobalTheory.LevProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamShareOfFreeT
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem ramShare_of_freeT {D : D7} {u : D.what₂.Word} (W : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) : RamShare D u := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.rank_nat W
  have hT2 : 2 ≤ (D.mem u).A.T := ((D.mem u).A.T_prime).two_le
  unfold RamShare dU
  rw [d0_eq]
  have h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f =
      (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f := by
    have e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2 := by omega
    rw [e2] at h
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2] at this
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
    linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1) := by
    field_simp; ring
  rw [e, div_pow]
  have hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp
  linarith [h']

theorem ramShare_of_trueD (D : D7) (u : D.what₂.Word) (hD : TrueD D) : RamShare D u :=
  TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u)
    (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u

end GlobalTheory.Core.Rk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealTransSm

open Formalism.MainNotions.StandardLattice

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem infMat_list_prod (hθ : IsInfFam θ) (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    ∀ l : List D.what₂.Tau, l.Nodup →
      infMat D.sp.cm.sig V.gram (θ ρ) (l.map fun τ => atTau θ V τ (u τ)).prod = if ρ ∈ l then u ρ else 1
  | [], _ => by simpa using GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_list_prod hθ u hu ρ l hl.2]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V a (hu a)
    by_cases c : ρ = a
    · subst c
      rw [hs.2.1, ite_eq_right hl.1, ite_eq_left List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      by_cases d : ρ ∈ l
      · rw [ite_eq_left d, ite_eq_left (List.mem_cons_of_mem a d)]
      · rw [ite_eq_right d, ite_eq_right]
        simp [c, d]

theorem eq_realElt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    g = GlobalTheory.AdelicScalar.realElt θ V (fun τ => infMat D.sp.cm.sig V.gram (θ τ) g) := by
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) g with hu_def
  have hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  set P := GlobalTheory.AdelicScalar.realElt θ V u with hP
  have hPm : P ∈ GinfC V := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V τ (u τ)
  have e : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) P = infMat D.sp.cm.sig V.gram (θ ρ) g := fun ρ => by
    rw [hP, GlobalTheory.AdelicScalar.realElt, infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
      ite_eq_left (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  refine mul_inv_eq_one.1 (GlobalTheory.PointAtPlace.eq_one_of_mem V _ ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 _ fun ρ => ?_)
    (mul_mem hg (inv_mem hPm)))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

def smAct (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (τ : D.what₂.Tau) :
    M.sm τ →ₗ[ℂ] M.sm τ :=
  (M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) g)).toLinearMap.restrict fun _ hw =>
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ) hw

theorem rTrans_eq_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  intro D θ V S M hθ g hg
  refine ⟨PiTensorProduct.map (smAct hθ M g), fun J χ T hT x => ?_⟩
  have hU : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod]
    let u τ := infMat D.sp.cm.sig V.gram (θ τ) g
    let w : M.Vec := fun τ => smAct hθ M g τ (v τ)
    have hu (τ : D.what₂.Tau) : u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have hw (τ : D.what₂.Tau) : (w τ : M.H τ) = M.rep τ (u τ) (v τ : M.H τ) := rfl
    have translate (U : MMap M) (hU : U ∈ Mult θ M J χ) :
        U w = rTr V (GlobalTheory.AdelicScalar.realElt θ V u) (U v) := by
      induction hU using Submodule.span_induction with
      | mem U hU =>
        have onList (l : List D.what₂.Tau) (hl : l.Nodup) :
            U (fun τ => if τ ∈ l then w τ else v τ) =
              rTr V (l.map fun τ => atTau θ V τ (u τ)).prod (U v) := by
          induction l with
          | nil =>
            funext h
            simp [rTr]
          | cons a l ih =>
            rw [List.nodup_cons] at hl
            have ha := hU.equiv a (u a) (hu a) (fun τ => if τ ∈ l then w τ else v τ)
              (w a) (by simpa only [ite_eq_right hl.1] using hw a)
            rw [ih hl.2] at ha
            have hupdate : (fun τ => if τ ∈ a :: l then w τ else v τ) =
                Function.update (fun τ => if τ ∈ l then w τ else v τ) a (w a) := by
              funext τ
              by_cases hτ : τ = a
              · subst τ
                simp
              · rw [Function.update_of_ne hτ]
                simp [hτ]
            rw [hupdate, ha]
            funext h
            simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        have hall := onList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
        simpa [GlobalTheory.AdelicScalar.realElt] using hall
      | zero => funext h; simp [rTr]
      | add U U' _ _ h₁ h₂ =>
        funext h
        simpa only [rTr, add_apply, Pi.add_apply] using
          congrArg₂ (· + ·) (congrFun h₁ h) (congrFun h₂ h)
      | smul a U _ h₁ =>
        funext h
        simpa only [rTr, smul_apply, Pi.smul_apply] using
          congrArg (a • ·) (congrFun h₁ h)
    have key := translate _ hU
    have hreal : GlobalTheory.AdelicScalar.realElt θ V u = g := (eq_realElt hθ hg).symm
    rw [hreal, PiTensorProduct.lift_symm] at key
    simp only [LinearMap.compMultilinearMap_apply] at key
    change c • T (PiTensorProduct.tprod ℂ w) = _
    funext h
    simp only [key, rTr, rTrans, map_smul, Pi.smul_apply]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    funext h
    simp [rTrans]

end GlobalTheory.RealTransSm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem coefClause_of_thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → ThetaClause ψ A B χB om omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → CoefClause ψ A B om omh ν 𝓕 := by
  intro D ψ A B χA χB om omh _ hT ν 𝓕 _ f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta A B ν 𝓕 f₁ f₂, fun g => ?_⟩
  have h := ((hT f₁ f₂ h₁ h₂).2 g 1 1).1
  have h1 : om ((1 : GA D A), (1 : GA D B)) f₂ = f₂ := by
    rw [show ((1 : GA D A), (1 : GA D B)) = (1 : GA D A × GA D B) from rfl, map_one]; rfl
  have hd : detA A (1 : GA D A) = 1 := map_one _
  rw [h1, hd, map_one, inv_one, Circle.coe_one, one_smul] at h
  simp only [swSec]
  rw [h, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta]

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem continuous_covolOne_integral {D : D7} {m n : ℕ} {X : Type} [TopologicalSpace X] {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (F : X → Mx D m n → ℂ)
    (hc : Continuous fun p : X × Mx D m n => F p.1 p.2)
    (hF : ∀ x, ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, F x (γ + a) = F x a) :
    Continuous fun x => ∫ a in 𝓕, F x a ∂μ := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have hi : ∀ x, IntegrableOn (F x) 𝓕 μ := fun x =>
    GlobalTheory.MixModel.covolOne_integrableOn h _ (hc.comp (Continuous.prodMk_right x)) (hF x)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc' : Continuous fun p : X × Mx D m n => ‖F p.1 p.2 - F x₀ p.2‖ :=
    (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ x in nhds x₀, ∀ a ∈ K, ‖F x a - F x₀ a‖ < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hc'.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hε
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  have hb : ∀ a, ‖F x a - F x₀ a‖ ≤ ε / 2 := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hF x γ hγ a, ← hF x₀ γ hγ a]
    exact (hx _ ha).le
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_lt ?_
  rw [measureReal_def, Measure.restrict_apply_univ, h.2.2, ENNReal.toReal_one, mul_one]
  exact half_lt_self hε

theorem swSec_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  intro D ψ A B χB omh hω ν 𝓕 hν φ hφ
  refine ⟨GlobalTheory.ThetaMean.integrableOn_lagr hν hφ, ?_⟩
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ omh hω φ hφ
  exact continuous_covolOne_integral hν (fun g w => omh (g, 1) φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w))
    (hj.comp ((continuous_fst.prodMk continuous_const).prodMk (GlobalTheory.ThetaMean.continuous_lagr.comp continuous_snd)))
    (fun g => GlobalTheory.ThetaMean.periodic_lagr (hω.om_pres _ _ hφ))

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def signEquiv {n : ℕ} (ε : Fin n → Bool) {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : Fin n ≃ Fin p ⊕ Fin q :=
  (Equiv.sumCompl fun a => ε a = true).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; exact hp))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simpa using hq)))

theorem signEquiv_inl {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin p) : ε ((signEquiv ε hp hq).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  generalize (Fintype.equivFinOfCardEq (α := {a // ε a = true}) _).symm i = x
  exact x.2

theorem signEquiv_inr {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin q) : ε ((signEquiv ε hp hq).symm (Sum.inr i)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  generalize (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) _).symm i = x
  simpa using x.2

theorem card_true (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = true).card = (V.sig (tauE D τ)).1 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).1

theorem card_false (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).2

def sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Mem.Th.CptF V := fun τ =>
  (M.fr τ).submatrix (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ)).symm id

theorem Jpq_submatrix {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    (Formalism.UG.Jpq p q).submatrix (signEquiv ε hp hq) (signEquiv ε hp hq) = Formalism.REAL.Jm ε := by
  ext a b
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rcases h1 : signEquiv ε hp hq a with i | i
    · have := signEquiv_inl hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
    · have := signEquiv_inr hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
  · have hne : signEquiv ε hp hq a ≠ signEquiv ε hp hq b := (signEquiv ε hp hq).injective.ne hab
    rw [if_neg hab]
    rcases h1 : signEquiv ε hp hq a with i | i <;> rcases h2 : signEquiv ε hp hq b with j | j <;> rw [h1, h2] at hne <;>
      simp_all [Formalism.UG.Jpq, Matrix.one_apply]

end GlobalTheory.ChainOnto.RealData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

namespace GlobalTheory.Core.Rk.HdGap

theorem bOne_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
  unfold bOne
  rw [dite_eq_left (by omega)]
  rfl

theorem gap_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := H
  have h := hg τ (j + 1) (by omega) (by omega)
  rwa [bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)] at h

theorem scale_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl)
    (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ∧ 1801 ≤ D.R.r := by
  obtain ⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := H
  have hm : 1801 ≤ D.R.m := by exact_mod_cast hCl.trans hClm
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, by unfold Ranks.r; omega⟩
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf1
  have hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L := by nlinarith
  calc 1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    _ = Cl * (D.R.r : ℝ) ^ 19 * 1 := by ring
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * L) := by
        apply mul_le_mul_of_nonneg_left h1; nlinarith
    _ = _ := by ring

end GlobalTheory.Core.Rk.HdGap
end

