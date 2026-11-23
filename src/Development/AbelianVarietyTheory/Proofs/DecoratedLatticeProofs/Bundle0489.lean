module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

theorem volLev_ne_zero_of_isCompact {D : D7} (V : HSp D) (hK : IsCompact (GinfC V : Set (GA D V))) (v : GlobalTheory.Unf.Vol V)
    (U : Subgroup (GA D V)) (hle : U ≤ GfC V) (hc : IsCompact (U : Set (GA D V)))
    (ho : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))) : GlobalTheory.SeeSaw.volLev v U ≠ 0 := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal := by
    unfold GlobalTheory.SeeSaw.volLev
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hc
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      ho.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho'
    show g ∈ (K : Set (GA D V))
    rw [hKset]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  rw [hvol]
  exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'

end GlobalTheory.TopVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E) Λ
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

end GlobalTheory.TopVol.InKConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frGL_mul' {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E n y := by
  simp [Formalism.L2.DIV.frGL]


set_option maxHeartbeats 1000000 in
theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : Formalism.IndefR.Lev.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Formalism.IndefR.Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul' β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem locHom_eq {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) {π' : Formalism.IndefR.Lev.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = q.pr a) (V : HSp D) (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) (F : GlobalTheory.LocMod.Frame k V.rank Y) (e : Y ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) :
    (GlobalTheory.LevIdx.locHom q V F x).val = (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix e e := by
  have h := mul_moved (ofSplit q) (π' := π') hπ V t x β y hy hM
  have hF : F.β = (F.β.submatrix id e.symm).submatrix id e := by
    ext i j; simp
  rw [GlobalTheory.LevIdx.locHom_val]
  generalize (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) = Yn at h ⊢
  generalize hMm : F.β.submatrix id e.symm = Mm at h hF
  have key : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) k) (B : Matrix (Fin V.rank) (Fin V.rank) k),
      A * B.submatrix id e = (A * B).submatrix id e := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have h' : (mt V x).map q.pr * Mm = Mm * Yn := h
  have h2 : (mt V x).map q.pr * F.β = F.β * Yn.submatrix e e := by
    calc (mt V x).map q.pr * F.β = (mt V x).map q.pr * Mm.submatrix id e := by rw [← hF]
      _ = ((mt V x).map q.pr * Mm).submatrix id e := key _ _
      _ = (Mm * Yn).submatrix id e := by rw [h']
      _ = Mm.submatrix id e * Yn.submatrix e e := (Matrix.submatrix_mul_equiv Mm Yn id e e).symm
      _ = F.β * Yn.submatrix e e := by rw [← hF]
  calc F.γ * (mt V x).map q.pr * F.β = F.γ * ((mt V x).map q.pr * F.β) := Matrix.mul_assoc _ _ _
    _ = F.γ * (F.β * Yn.submatrix e e) := by rw [h2]
    _ = Yn.submatrix e e := by rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_twist_levTop {s : ℕ} {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ)
    (hδ : GlobalTheory.SplitWeil.IsTame δ) (ν : ℕ → kˣ →* ℂˣ) (x : GL (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2)) k) :
    x ∈ (GlobalTheory.StepData.twistChain s τ κ δ hδ ν).levTop.J ↔
      x ∈ GlobalTheory.SplitWeil.KO k _ ∧ ∀ i j, ValuativeRel.valuation k (x.val (Sum.inr i) (Sum.inl j)) < 1 := by
  have e : (GlobalTheory.StepData.LatFrame.refl k (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2))).conj.symm x = x := by
    rw [MulEquiv.symm_apply_eq]
    ext i j
    simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_val]
  show x ∈ ((GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 2) × τ) δ hδ).toLevel.map
    (GlobalTheory.StepData.LatFrame.refl k _).conj).J ↔ _
  rw [GlobalTheory.StepData.Level.mem_map, e, GlobalTheory.StepData.mem_parahoric]
  rfl

theorem frGL_inv {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {t g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) :
    Formalism.L2.DIV.frGL β y⁻¹ = Formalism.IndefR.Lev.finE V (t⁻¹ * g⁻¹ * t) := by
  have e : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
  exact ((Formalism.L2.DIV.frGL β).map_inv y).trans ((congrArg (·⁻¹) hy).trans
    (((Formalism.IndefR.Lev.finE V).map_inv _).symm.trans (congrArg (Formalism.IndefR.Lev.finE V) e.symm)))


set_option maxHeartbeats 1000000 in
theorem red_iff {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] (q : SplitPt D k)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (t g : GA D V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (F : GlobalTheory.LocMod.Frame k V.rank (R ⊕ S)) (e : R ⊕ S ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) (r : ℕ)
    (hl : ∀ a, (e (Sum.inl a)).val < r) (hr : ∀ a, r ≤ (e (Sum.inr a)).val)
    (hst : Formalism.IndefR.Lev.finE V (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) ∈ blockTri (blk2 r) ↔
      GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ ∧
        ∀ i j, ValuativeRel.valuation k ((GlobalTheory.LevIdx.locHom q V F g).val (Sum.inr i) (Sum.inl j)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
  obtain ⟨y, hy⟩ := hst
  have h1 := locHom_eq q hπ V t g β y hy F e hM
  have h2 := locHom_eq q hπ V t g⁻¹ β y⁻¹ (frGL_inv hy) F e hM
  have hK : GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [h1]; exact hred.int _
    · rw [← (GlobalTheory.LevIdx.locHom q V F).map_inv, h2]; exact hred.int _
  have h3 : Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (Formalism.L2.DIV.redFn β PP) hy.symm).trans (redFn_frGL β PP y)
  rw [h3, mem_blockTri, h1]
  constructor
  · intro h
    refine ⟨hK, fun i j => (hred.ker _).1 (h (e (Sum.inr i)) (e (Sum.inl j)) ?_)⟩
    simp [blk2, hl j, (hr i).not_gt]
  · rintro ⟨-, h⟩ i j hij
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i
    · simp [blk2, hl i] at hij
    rcases j with j | j
    · exact (hred.ker _).2 (h i j)
    · simp [blk2, (hr i).not_gt, (hr j).not_gt] at hij


set_option maxHeartbeats 1000000 in
theorem red_iff_levTop {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
    (δ : G.kˣ →* ℂˣ) (hδ : GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (g : GA D c.T)
    (hst : Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT) ∈ Formalism.L2.DIV.St B.βT) :
    Formalism.L2.DIV.redFn B.βT PP (Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ x, (mt c.T g).map G.q.pr = G.FT.β * Units.val x * G.FT.γ → x ∈ (G.T δ hδ η).levTop.J := by
  obtain ⟨e, he, hM⟩ := G.frameTop
  have hs := G.hs
  have hk : D.R.r = D.R.k + (G.s + 1) := by
    unfold Ranks.r
    omega
  refine (red_iff G.q PP G.idem c.T B.bT g B.βT G.FT e hM _ (fun a => ?_) (fun a => ?_) hst).trans ?_
  · rw [he, hk]
    rcases a with a | a
    · exact lt_of_lt_of_le a.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left a.2 _
  · rw [he, hk]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · refine (mem_twist_levTop δ hδ η _).symm.trans ⟨fun h x hx => ?_, fun h => h _ ?_⟩
    · obtain rfl := (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g x).1 hx
      exact h
    · exact (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g _).2 rfl

theorem levS_split (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    κ ∈ levS V β L ↔ κ ∈ levS V β { L with Q := ∅, xq := ξ } ∧
      ∀ PP ∈ L.Q, Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V κ) ∈ blockTri (blk2 L.r) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c, d⟩ := mem_parLev.1 h2
    exact ⟨⟨h1, mem_parLev.2 ⟨a, b, c, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, h3⟩, d⟩
  · rintro ⟨⟨h1, h2, h3⟩, d⟩
    obtain ⟨a, b, c, -⟩ := mem_parLev.1 h2
    exact ⟨h1, mem_parLev.2 ⟨a, b, c, d⟩, h3⟩

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree


end GlobalTheory.TopAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

def relax (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (GlobalTheory.PenBridge.rd J j hj)

def U0 (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

end GlobalTheory.PenLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  first | exact @GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | exact GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | (intros; apply GlobalTheory.UnitLevelInt.entry_mem_of_levelVL <;> assumption)
end

