module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducesToResidueOfLocalLevelElementMovedBack
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroFamRead
open GlobalTheory.LevZeroRead


set_option maxHeartbeats 1000000 in
theorem red_of_isLoc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  intro D c v G PP b β hL hbf hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : ((β.val.map f).map (toEAf D)) = β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (c.V 0) b * β * intGL _ _ _ m =
      Lev.finE (c.V 0) g * (Lev.finE (c.V 0) b * β) := by
    have : β * intGL _ _ _ m * β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (c.V 0).rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (c.V 0).rank ≤ D.R.r := by
    have := Fintype.card_congr e
    simp at this
    have := G.hs
    show _ ≤ D.R.k + D.R.m - 1
    omega
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroFamRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section
namespace GlobalTheory.TwLevRed

theorem reGL_symm_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem blockTri_iff_mem_lev : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  intro E _ _ k _ _ _ _ PP ι hPP K T s j d hd δ hδ η n e he x hx R hR
  have hent : ∀ a b, R.val a b = 0 ↔ valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a))
      (stdOrd (Fin K) (Fin T) j d hd (e.symm b))) < 1 := by
    intro a b
    constructor
    · intro h0
      have := hR a b 0 (by rw [h0, map_zero])
      simpa using this
    · intro hv
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (R.val a b)
      have h1 := hR a b z hz.symm
      have h2 : valuation k (ι (z : E)) < 1 := by
        have : ι (z : E) = x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) -
            (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) - ι (z : E)) := by
          ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
      rw [← hz, Ideal.Quotient.eq_zero_iff_mem]
      exact hPP z h2
  have hblk : ∀ q : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j,
      Formalism.L2.DIV.blk2 (K + (s + 1)) (e q) = Sum.elim (fun _ => 0) (fun _ => 1) q := by
    intro q
    have h := he q
    unfold Formalism.L2.DIV.blk2
    rcases q with (i | i) | p
    · have : (e (.inl (.inl i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : (e (.inl (.inr i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : ¬ (e (.inr p)).val < K + (s + 1) := by
        rw [h, not_lt]; simp only [GlobalTheory.SymBridge.zPos]
        exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      simp [this]
  have hJ : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J ↔
      ∀ (p : Fin j × Fin T) (i : Fin K ⊕ Fin (s + 1)),
        valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inl i))) < 1 := by
    change (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J ↔ _
    rw [mem_parahoric]
    have e' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x =
        (reGL (stdOrd (Fin K) (Fin T) j d hd)).symm x := by
      simp [LatFrame.conj, plainFrame]
      rfl
    rw [e', reGL_symm_mem_KO_iff]
    simp only [hx, true_and]
    rfl
  rw [hJ, Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h p i
    have := h (e (.inr p)) (e (.inl i)) (by rw [hblk, hblk]; simp)
    rw [hent] at this
    simpa using this
  · intro h a b hab
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨q', rfl⟩ := e.surjective b
    rw [hblk, hblk] at hab
    rw [hent]
    rcases q with q | q <;> rcases q' with q' | q' <;> simp at hab
    simpa using h q q'

end GlobalTheory.TwLevRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitOffRed

theorem resS_eq_zero_of_cpt {D : D7} (PP' : Formalism.L2.DIV.Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) = 0) : Formalism.L2.DIV.resS D.host.F PP' s = 0 := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' s
  rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
  rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' s] at h2
  change Valued.v (GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) - _) < 1 at h2
  rw [h, zero_sub, Valuation.map_neg] at h2
  exact h2

theorem redFn_eq_one_off : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  intro D k _ _ _ _ q PP hq V β κ hS hst PP' hne
  have hPP' : PP' ≠ PP := fun h => hne (h ▸ rfl)
  have hcP : GlobalTheory.IdemSupport.cP PP' ≠ PP := fun h => hne (by rw [← h, GlobalTheory.IdemSupport.under_cP])
  have h1 : q.e * q.e = q.e := q.split.1
  have hc1 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  have hi1 : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP hq).1
  have hi2 : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1]))
  have hint : toEAf D (q.e + cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_add (f := _)]; exact add_mem hi1 hi2
  have hc0 : GlobalTheory.StdFrames.cpt PP' (toEAf D (q.e + cA D q.e)) = 0 := by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 PP' hPP', zero_add,
      GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 _ hcP)
  have hres : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D (q.e + cA D q.e), hint⟩ = 0 :=
    resS_eq_zero_of_cpt PP' _ hc0
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl
  refine GlobalTheory.LevSplit.redFn_eq_one β PP' (Lev.finE V κ) hst ⟨toEAf D (q.e + cA D q.e), hint⟩ hres ?_
  ext i j
  have := congrArg (toEAf D) (hS i j)
  rw [RingHom.map_mul, Matrix.sub_apply, RingHom.map_sub] at this
  show toEAf D (q.e + cA D q.e) * ((Lev.finE V κ).val - 1) i j = ((Lev.finE V κ).val - 1) i j
  rw [Matrix.sub_apply, hval, Matrix.map_apply]
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j = toEAf D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [e1]
  exact this

end GlobalTheory.SplitOffRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PenVol

section Gen

open ValuativeRel

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem mulVec_mem_box_of_int (A : Matrix n n k) (hA : ∀ i j, valuation k (A i j) ≤ 1) {c : kˣ} {y : n → k}
    (hy : y ∈ GlobalTheory.StepData.box n c) : A *ᵥ y ∈ GlobalTheory.StepData.box n c := by
  intro i
  show valuation k ((A *ᵥ y) i) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc valuation k (A i j) * valuation k (y j) ≤ 1 * valuation k (c : k) := mul_le_mul' (hA i j) (hy j)
    _ = valuation k (c : k) := one_mul _

theorem val_le_one_of_mem_KO {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (i j : n ⊕ Fin 0) :
    valuation k (g.val i j) ≤ 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val i j).2

theorem toBlocks₁₁_mulVec_mem_box {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) {c : kˣ}
    {y : n → k} (hy : y ∈ GlobalTheory.StepData.box n c) : g.val.toBlocks₁₁ *ᵥ y ∈ GlobalTheory.StepData.box n c :=
  mulVec_mem_box_of_int _ (fun i j => val_le_one_of_mem_KO hg (Sum.inl i) (Sum.inl j)) hy

def boxQ {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    ((n → k) ⧸ GlobalTheory.StepData.box n c) →ₗ[𝒪[k]] ((n → k) ⧸ GlobalTheory.StepData.box n c) :=
  Submodule.mapQ _ _ ((Matrix.mulVecLin g.val.toBlocks₁₁).restrictScalars 𝒪[k])
    (fun _ hy => toBlocks₁₁_mulVec_mem_box hg hy)

theorem boxQ_mk {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) (y : n → k) :
    boxQ hg c (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) := rfl

def boxAct (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    MulAction J ((n → k) ⧸ GlobalTheory.StepData.box n c) where
  smul g q := boxQ (hJ g.2) c q
  one_smul q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = _
    rw [boxQ_mk, show ((1 : J) : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]
  mul_smul g h q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = boxQ _ c (boxQ _ c _)
    rw [boxQ_mk, boxQ_mk, boxQ_mk, show ((g * h : J) : GL (n ⊕ Fin 0) k).val = g.val.val * h.val.val from rfl,
      toBlocks_mul_fin_zero, Matrix.mulVec_mulVec]

theorem relIndex_cosStab_box (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ)
    (x : (n → k) ⧸ GlobalTheory.StepData.box n c) :
    (cosStab J (GlobalTheory.StepData.box n c) x).relIndex J = Nat.card {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
  letI := boxAct J hJ c
  have smk : ∀ (g : J) (y : n → k), g • (Submodule.Quotient.mk y : (n → k) ⧸ GlobalTheory.StepData.box n c) =
      Submodule.Quotient.mk (g.val.val.toBlocks₁₁ *ᵥ y) := fun _ _ => rfl
  have hst : (cosStab J (GlobalTheory.StepData.box n c) x).subgroupOf J = MulAction.stabilizer J x := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_cosStab, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [smk]
      exact (h y).2 rfl
    · intro h
      refine ⟨g.2, fun y => ?_⟩
      rw [← smk]
      constructor
      · intro h'
        rw [← h] at h'
        exact smul_left_cancel g h'
      · intro h'
        rw [h', h]
  have horb : MulAction.orbit J x = {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
    ext yb
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, GlobalTheory.QPl.SameOrb]
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨g.1, g.2, y, rfl, (smk g y).symm⟩
    · rintro ⟨g, hg, y, rfl, h⟩
      exact ⟨⟨g, hg⟩, by rw [smk]; exact h⟩
  rw [Subgroup.relIndex, hst, MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

end Gen

end GlobalTheory.PenVol

end

namespace GlobalTheory.PenVol

theorem relIndex_cosStab_eq_wt {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}
    (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)) :
    (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex
      (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  have hJ := E.le (G.s + 1) 0 rfl
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (cosStab_le _ _ _) hJ, relIndex_cosStab_box _ hJ, E.wt_pen y,
    E.idx_mid (G.s + 1) 0 rfl]
  push_cast
  ring

end GlobalTheory.PenVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem GlobalTheory.FinPl.flatFB_om_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  intro D ψ σ J B s LV LW v hLV hLW hv hu f hf n hn hnv x κ hκ
  have hmul : s.om (1, n * x * κ) f = s.om (1, n) (s.om (1, x) (s.om (1, κ) f)) := by
    have : ((1 : GA D J.W), n * x * κ) = (1, n) * (1, x) * (1, κ) := by simp
    rw [this, map_mul, map_mul]; rfl
  have hκf : s.om (1, κ) f = f := by
    refine _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hLV hLW (· = v) ?_ f hf 1 κ ?_ hκ
    · rintro w rfl; exact ⟨hv, hu.1, hu.2⟩
    · refine ⟨one_mem _, ?_⟩
      intro y _
      simp
  have hth : IsThetaFunO ψ J.W B.V (s.om (1, x) f) := s.weil.om_pres _ _ hf.1
  have h := ((_root_.GlobalTheory.FinPl.flatLaws_all D ψ (· = v)).2 σ J B s).equiv _ hth n hn hnv 1 (one_mem _)
  have he : B.o.emb (1, 1) = 1 := map_one B.o.emb
  have he₀ : s.om₀ ((1 : GA D J.W₀), (1 : GA D B.V₀)) = 1 := map_one s.om₀
  rw [map_one, mul_one, he, he₀, Module.End.one_apply] at h
  rw [hmul, hκf, h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferAllFinitePlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem transferOn_all : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun _ => True := by
  intro hH D ψ S T χS χT om hW t ht v _
  by_cases hv : IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.sphericalParameterTransfer_splitPlace D ψ S T χS χT om hW t ht v hv
  · exact GlobalTheory.T.sphericalTransfer_weilPairing_inertPlaces hH D ψ S T χS χT om hW t ht v hv

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_integralAdele_iff_both_components : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D), a ∈ GlobalTheory.FinPl.idAt D (· = q.v) → (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.SplitInt.intAt_iff_pr | exact GlobalTheory.SplitInt.intAt_iff_pr | (intros; apply GlobalTheory.SplitInt.intAt_iff_pr <;> assumption)
end

