module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0012
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0013
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsLocalZetaDataRealizingStandardPair
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0018

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StageGeo

variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}

structure Reads (α β : T → ((AE D)ˣ →* Circle)) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (Bs : Base D.host.F D.host.E)
    (t : T) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  eα : Xc.α = α t

  eβ : Xc.β = β t

  pl : ∀ w, w ∈ S t ↔ ∃ v : Bs.P, v.1 ∈ Xc.T ∧ splitPrime (Bs.τ v) = w

  unit : ∀ v : Bs.P, v.1 ∈ Xc.T → AUnit (Bs.τ v)

theorem exists_fin (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {t : T}
    {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (hR : Reads α β S Bs t Xc) {om om' R Rf}
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {g g'}
    (hg : X.vac = thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M.vac))
    (hg' : X.vac' = thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' Γ.M'.vac)) :
    ∃ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ v ∉ Xc.T, φ v = Γ.M.vac v) ∧
      (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) ∧ (∀ v, φ v ≠ 0) ∧ (∀ v, φ' v ≠ 0) ∧ (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) ∧
      X.f t = thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) ∧
      X.f' t = thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ') := by
  have hT := hm.triple
  let u : Xc.T → Bs.P := fun v => ⟨v.1, hT.chars.sub v.2⟩
  choose ι ι' φ₀ φ₀' l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 using fun v : Xc.T =>
    UpperTheory.exists_local_zeta_data_realizing_standard_pair _ _ D.sp.cm.sig Bs _ _ Γ Xc Rf (u v) hT.chars.heckeα hT.chars.heckeβ (hm.fin.zeta (u v) v.2) hT.geo.hM hT.geo.hM'
      (X.c t (splitPrime (Bs.τ (u v))))
  have hν : Xc.ν = α t / β t := by rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, hR.eα, hR.eβ]
  have hψ : Bs.ψ = ψ := hG.pairA.psi
  rw [hν] at l7 l8
  rw [hψ] at l1 l2
  have hS : ∀ w, w ∈ S t ↔ ∃ v : Xc.T, splitPrime (Bs.τ (u v)) = w := fun w =>
    (hR.pl w).trans ⟨fun ⟨v, hv, e⟩ => ⟨⟨v.1, hv⟩, e⟩, fun ⟨v, e⟩ => ⟨u v, v.2, e⟩⟩
  let φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if h : v ∈ Xc.T then φ₀ ⟨v, h⟩ else Γ.M.vac v
  let φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if h : v ∈ Xc.T then φ₀' ⟨v, h⟩ else Γ.M'.vac v
  have e1 : ∀ v (h : v ∈ Xc.T), φ v = φ₀ ⟨v, h⟩ := fun v h => dif_pos h
  have e1' : ∀ v (h : v ∈ Xc.T), φ' v = φ₀' ⟨v, h⟩ := fun v h => dif_pos h
  have e2 : ∀ v ∉ Xc.T, φ v = Γ.M.vac v := fun v h => dif_neg h
  have e2' : ∀ v ∉ Xc.T, φ' v = Γ.M'.vac v := fun v h => dif_neg h
  have s1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ ∧ φ v ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · rw [e1 v h]; exact ⟨l5 _, l10 _⟩
    · rw [e2 v h]; exact ⟨(hT.geo.hM.vac v).1, (hT.geo.hM.vac v).2.1⟩
  have s2 : ∀ v, φ' v ∈ GlobalTheory.WeilM.SB _ ∧ φ' v ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · rw [e1' v h]; exact ⟨l6 _, l11 _⟩
    · rw [e2' v h]; exact ⟨(hT.geo.hM'.vac v).1, (hT.geo.hM'.vac v).2.1⟩
  refine ⟨φ, φ', fun v => (s1 v).1, fun v => (s2 v).1, e2, e2', fun v => (s1 v).2, fun v => (s2 v).2, fun v h => ?_, ?_, ?_⟩
  · rw [e1 v h, e1' v h]; exact l9 ⟨v, h⟩
  · exact UpperTheory.thetaLift_triple_local_split_places D T A A' WW X ψ θ α β νH S hX hX.rank Bs Γ.V Γ.W Γ.M hG.pairA hG.latA t Xc.T (fun v => Bs.τ (u v)) hS
      (fun v => Γ.V.bas v) (fun v => Γ.W.bas v) ι (fun v => hG.basA (u v)) (fun v => hG.basW (u v) (hR.unit (u v) v.2)) l1 l3 φ
      (fun v => (s1 v).1) e2 (fun v => by rw [e1 v.1 v.2]; exact l7 v) g hg
  · exact UpperTheory.triple_dualCoord_split_places_of_isPair_isLat D T A A' WW X ψ θ α β νH S hX hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB hG.latB t Xc.T (fun v => Bs.τ (u v)) hS
      (fun v => Γ.V'.bas v) (fun v => Γ.W.bas v) ι' (fun v => hG.basB (u v)) (fun v => hG.basW (u v) (hR.unit (u v) v.2)) l2 l4 φ'
      (fun v => (s2 v).1) e2' (fun v => by rw [e1' v.1 v.2]; exact l8 v) g' hg'

theorem exists_vac {ε : Bool} {S₀ : HSp D} {d : ℕ} {e : Fin d ≃ Fin WW.rank} {Vs : Spc D.host.F D.host.E S₀.rank}
    {Ws : Spc D.host.F D.host.E d} {M : Model D.sp.cm.sig Vs Ws} (hP : IsPair ψ ε S₀ WW e Bs Vs Ws M)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S₀.rank → D.host.E)} {ΛX : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hL : IsLat e Vs Ws ΛS ΛX) {s s'} {f : WO (sgn ε S₀) WW → ℂ} (hf : IsVacO ψ θ (sgn ε S₀) WW s s' ΛS ΛX f) :
    ∃ g : SInf D.host.F (Fin S₀.rank × Fin d), g ≠ 0 ∧ f = thO M ψ (sgn ε S₀).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  obtain ⟨g, hg⟩ := UpperTheory.exists_thO_eq_of_isLatVac_thetaFun D ψ ε S₀ WW d e Bs Vs Ws M hP ΛS ΛX hL f hf.2.theta hf.2.lat
  refine ⟨g, fun h0 => ?_, hg⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have h1 := hn p hp
  have h2 : f = 0 := by
    rw [hg, h0]
    funext x
    simp [thO, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [h2] at h1
  simp [nrm2] at h1

end GlobalTheory.StageGeo

end
