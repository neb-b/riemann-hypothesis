module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DualLine

variable {D : D7}

theorem idV_le_idAt {𝔞 : FI D} {v : Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, hα, b, -, rfl⟩ := hx
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => hα w hw) b
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem cA_mem_idV_one {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v) : cA D c ∈ idV (1 : FI D) v := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨o', ho'⟩ := GlobalTheory.FinPl.LatMem.star_int o
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, (o' : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨o', rfl⟩, ?_⟩
    show pairA D.host.F 0 α ⊗ₜ[D.host.F] star ((o : D.host.E)) = _
    rw [ho']
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_incA_mem {S : HSp D} {L : Lat S} {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v)
    {s : Fin S.rank → D.host.E} (hs : s ∈ L) : (fun a => c * incA D (s a)) ∈ latV S L (· = v) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw => hα w hw, 1, rfl, o • s, L.smul_mem o hs, ?_⟩
    funext l
    show (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s l) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have : (fun a => (0 : AE D) * incA D (s a)) = 0 := funext fun a => zero_mul _
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (x + y) * incA D (s a)) = (fun a => x * incA D (s a)) + fun a => y * incA D (s a) :=
      funext fun a => add_mul _ _ _
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : (fun a => (-x) * incA D (s a)) = -fun a => x * incA D (s a) := funext fun a => neg_mul _ _
    rw [this]; exact neg_mem hx

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

def hA (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ a, ∑ b, cA D (y a) * gA S a b * w b

theorem hA_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : hA S (w + w') y = hA S w y + hA S w' y := by
  simp only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : hA S (-w) y = -hA S w y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_zero_left (S : HSp D) (y : Fin S.rank → AE D) : hA S 0 y = 0 := by
  simp only [hA, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem hA_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : hA S w (y + y') = hA S w y + hA S w y' := by
  simp only [hA, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : hA S w (-y) = -hA S w y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (w : Fin S.rank → AE D) : hA S w 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem hA_mem {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S L (· = v)) (hy : y ∈ latV S L (· = v)) : hA S w y ∈ idV (1 : FI D) v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hy'
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨α, hαi, hα, c, hc, x, hx, rfl⟩ := hw'
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 (β * α) := Prod.ext (zero_mul _) rfl
      have e : hA S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        show (pairA D.host.F 0 β ⊗ₜ[D.host.F] star (1 * x' a)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram a k) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x k)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp, one_mul, one_mul]
      rw [e]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi,
        fun w hw => by rw [map_mul, hβ w hw, zero_mul], (b : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩, rfl⟩
    | zero => rw [hA_zero_left]; exact zero_mem _
    | add w w' _ _ h h' => rw [hA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hA_neg_left]; exact neg_mem h
  | zero => rw [hA_zero_right]; exact zero_mem _
  | add y y' _ _ h h' => rw [hA_add_right]; exact add_mem h h'
  | neg y _ h => rw [hA_neg_right]; exact neg_mem h

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

theorem cA_cA' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c e => show c ⊗ₜ[D.host.F] star (star e) = _; rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_gA (S : HSp D) (a b : Fin S.rank) : cA D (gA S a b) = incA D (S.gram b a) :=
  congrArg (incA D) (GlobalTheory.LatVac.gram_star S a b)

theorem mem_of_hA {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D}
    (hyAt : ∀ a, y a ∈ idAt D (· = v)) (h : ∀ w ∈ latV S L (· = v), hA S w y ∈ idV (1 : FI D) v) :
    y ∈ latV S L (· = v) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
  set ι : AE D := pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) with hι
  set w : Fin m → Fin S.rank → AE D := fun i l =>
    pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * s' i l) with hwdef
  have hw : ∀ i, w i ∈ latV S L (· = v) := fun i => AddSubgroup.subset_closure
    ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s' i, hs' i, rfl⟩
  have hcw : ∀ i l, cA D (w i l) = ι * incA D (star (s' i l)) := fun i l => by
    show pairA D.host.F 0 _ ⊗ₜ[D.host.F] star (1 * s' i l) = (pairA D.host.F 0 _ ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] star (s' i l))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]
  have hyeq : y = ∑ i, fun a => cA D (hA S (w i) y) * incA D (s i a) := by
    funext a
    rw [Finset.sum_apply]
    have e1 : y a = ∑ a', y a' * ι * incA D (∑ i, s i a * ∑ k, star (s' i k) * S.gram k a') := by
      simp only [hdual]
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, map_one, mul_one]
      exact (GlobalTheory.FinPl.LatMem.mul_indP (hyAt a)).symm
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA, map_sum, map_mul, cA_cA', cA_gA, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hyeq]
  exact sum_mem fun i _ => mul_incA_mem (cA_mem_idV_one (h _ (hw i))) (hs i)

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

theorem dualLine_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  intro D ψ hψ S S₀ ρ d L L₀ 𝔟 v hL hM i hb t ht
  have I2 := (_root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v).2.1 (𝔟 i) 1 hb one_ne_zero (cA D t) (cA_mem_idAt ht)
  rw [one_mul] at I2
  have hH : ∀ w, hA S w (colMul d.jY i t) = cA D t * (d.pX *ᵥ w) i := by
    intro w
    rw [d.pX_eq]
    simp only [hA, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    show cA D t * cA D (d.jY a i) * gA S a b * w b = cA D t * (cA D (d.jY a i) * gA S a b * w b)
    ring
  have hPX : ∀ a, (d.pX *ᵥ colMul d.jX i a) i = a := by
    intro a
    have h1 := congrFun (congrFun d.pX_jX i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [Matrix.mulVec, dotProduct, colMul]
    calc ∑ k, d.pX i k * (a * d.jX k i) = a * ∑ k, d.pX i k * d.jX k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = a := by rw [h1, mul_one]
  constructor
  · intro hy
    refine I2.1 fun a ha => ?_
    have hx := (hM.2 i a (idV_le_idAt ha)).2 ha
    have h2 := hA_mem hL hx hy
    rwa [hH, hPX] at h2
  · intro hc
    have hall := I2.2 hc
    refine mem_of_hA hL (fun k => Ideal.mul_mem_right _ _ ht) fun w hw => ?_
    rw [hH]
    have hwAt := GlobalTheory.FinPlLoc.latV_idAt hw
    have heAt : (d.pX *ᵥ w) i ∈ idAt D (· = v) := by
      show ∑ b, d.pX i b * w b ∈ idAt D (· = v)
      exact
      Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (d.pX i b) (hwAt b)
    exact hall _ ((hM.2 i _ heAt).1 (((hM.1 w).1 hw).1 i))

end GlobalTheory.DualLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPin


set_option maxHeartbeats 4000000 in
theorem exists_levelData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), SymRead W l S → (∀ PP, LocY (l PP) y v.N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (pk W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, GRead (⟨mkGeo m b, j, row, col⟩ : FamCh W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (pk W).ψ (-1) := hc.std
  choose ν hν using fun PP : (pk W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (pk W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (pk W).Pg
  let pl : Fin n ≃ (pk W).Pg := (Fintype.equivFin _).symm

  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT

  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (pk W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩

  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i

end GlobalTheory.LevPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymReadEx
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem tame_step {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E} (hP : PP ∈ L.Pg)
    (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ}
    (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta j).1⁻¹ μ) : IsTame μ := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : L.mu0 (i + 1) (idl q x) = 1 := res_idl q h (hL.mu0 ⟨i, h2⟩) (hL.chi ⟨i, h2⟩ PP hP) x hx
  have hr : IsRes L.C.eta PP 1 := fun z y v hy hv => by
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    have hzP : z ∉ PP.asIdeal := fun hm => v.ne_zero (hv.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
    rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := y)
      (by rw [hy]; exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP)]
    rfl
  have e2 : L.eta (idl q x) = 1 := res_idl q h hL.eta hr x hx
  have e3 : (Lift.chrStep L.mu0 L.eta (i + 1)).1 (idl q x) = 1 := by
    unfold Lift.chrStep
    split_ifs
    · change L.mu0 (i + 1) (idl q x) * (L.eta (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem red_sym {D : D7} {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP)
    (S : SymData l.k l.s D.R.k) {π : Equiv.Perm (Fin D.R.r)} (hπ : IsSymOrd D.R.rS D.R.k π)
    (g g' : GL (Fin D.R.r) (kP PP)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j)) :
    ((∃ x, l.Red S x g) ↔ g' ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧
    ∀ ψ₀ : AddChar (kP PP) ℂ,
      (∀ z, (S.ψ (((S.ϖ⁻¹ : l.kˣ) : l.k) * prO l.q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z)) → ∀ x, l.Red S x g →
        (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge D.R.rS D.R.k) g') := by
  have h1 := l.hs
  have h2 := S.odd
  have hρ : D.R.rS = S.ρ := by unfold Ranks.rS; omega
  let e : Fin D.R.k ⊕ Fin (l.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
  have hr : ∀ x, l.Red S x g ↔ ∀ a b z, Ideal.Quotient.mk PP.asIdeal z = g.val (e a) (e b) →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val a b - prO l.q z) < 1 := fun x =>
    ⟨fun h a b => h a b _ _ (he a) (he b), fun h a b a' b' ha hb => by
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      exact h a b⟩
  rw [hρ] at hπ ⊢
  simp only [hr]
  exact ⟨sym_grp S (prO l.q) (prO_le l.q l.idem) (prO_lt l.q l.idem) e he hπ g g' hg,
    fun ψ₀ h x hx => sym_chr S (prO l.q) e he hπ g g' hg ψ₀ h x hx⟩

theorem exists_symRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW _ a l
  obtain ⟨ψ₀, hψ₀, -, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hlev := W.Q.charW.base.lev
  have loc : ∀ PP : (pk W).Pg, ∃ S : SymData (l PP).k (l PP).s D.R.k, (ofSplit (l PP).q).IsChar (pk W).ψ S.ψ ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ (S.μ j)) ∧
      ∀ z, (S.ψ (((S.ϖ⁻¹ : (l PP).kˣ) : (l PP).k) * prO (l PP).q z) : ℂ) = ψ₀ PP.1 (Ideal.Quotient.mk _ z) := by
    intro PP
    obtain ⟨⟨ψk, hch, hcond⟩, -⟩ := GlobalTheory.WeilCondUnif.cond_unif W u hW a PP.1 (Or.inl PP.2) (l PP)
    obtain ⟨ϖ, hϖ, hres⟩ := exists_unif (l PP).q (l PP).idem hcond (hψ₀ PP.1 PP.2)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (l PP).s + 1 = 2 * ρ + 1 := by
      obtain ⟨b, hb⟩ := D.R.m_even
      have := (l PP).hs
      exact ⟨b - 1, by omega⟩
    obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel (l PP).k ψk hcond ϖ hϖ ρ D.R.k ((l PP).s + 1)
    choose μ hμ using fun j => GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (l PP).q) (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹
    refine ⟨⟨ψk, ϖ, ρ, P, fun j => if 1 ≤ j ∧ j ≤ D.R.m then μ j else 1, fun j => ?_, hcond, hϖ, hρ, hP'⟩, hch,
      fun j h1 h2 => ?_, hres⟩
    · split_ifs with h
      · exact tame_step (pk W).toLevCh hlev (l PP).q PP.2 (l PP).idem h.1 h.2 (hμ j)
      · exact fun _ _ => rfl
    · simp only [if_pos (And.intro h1 h2)]
      exact hμ j
  choose S h1 h2 h3 using loc
  refine ⟨S, h1, h2, fun x => (hH x).trans ?_, fun x hx y hxy => ?_⟩
  · exact ⟨fun h PP => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.2 (h PP (Set.mem_univ _)),
      fun h PP _ => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.1 (h PP)⟩
  · refine (hχ x hx ((hH _).1 hx)).trans ?_
    refine (map_prod (MonoidHom.eval _) _ _).trans (Finset.prod_congr rfl fun PP _ => Units.ext ?_)
    exact ((red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).2 _ (h3 PP) _ (hxy PP)).symm

end GlobalTheory.SymReadEx

end
end

