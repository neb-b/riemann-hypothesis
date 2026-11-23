module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingKeepsGluedCoreIffFixesPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec_any (p : SplitPt D k) {S : HSp D} (h : GA D S) (y : Fin S.rank → k) :
    Formalism.L2.Theta.mt S h *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((((Formalism.L2.Theta.mt S h).map p.pr) *ᵥ y) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem col_mulVec {m : Type} [Fintype m] (Y : m → k) (t : Fin 1 → k) :
    Matrix.replicateCol (Fin 1) Y *ᵥ t = t 0 • Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem vec_emb {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀)
    (g : GL n k) (x : n ⊕ Fin 1 → k) :
    (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (β₀.b *ᵥ x) =
      β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  have hA : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jA.map p.pr = o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [← Matrix.map_mul, o.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jB.map p.pr = o.jB.map p.pr := by
    rw [← Matrix.map_mul, o.emb_jB]
    simp
  have hz : (fun i => p.pr (ratV (vecB o ζ) i)) = o.jB.map p.pr *ᵥ (fun j => p.pr (incA D (ζ j))) := by
    funext i
    simp [ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat]
  have hY : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) =
      (fun i => p.pr (ratV (vecB o ζ) i)) := by
    rw [hz, Matrix.mulVec_mulVec, hB]
  rw [hs, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec, col_mulVec, col_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hY,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
  have e : o.jA.map p.pr * (β.b * g.val * β.b') * β.b = (o.jA.map p.pr * β.b) * g.val := by
    simp only [Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem mem_glued_iff {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} {M : Lat S} {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (hG : GluedW β₀ M q m P) (x : n ⊕ Fin 1 → k) :
    (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
      ∃ s : 𝒪[k], x ∘ Sum.inl - s • P.vec ∈ P.ker ∧ m * x (Sum.inr 0) = q.inv * s := by
  rw [hG x, GlobalTheory.LevelUnfold.mem_gluedS, Sum.elim_comp_inl]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp [Fin.forall_fin_one]

theorem glued_stab {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    {g : GL n k} (hP : g • P = P) {u : n → k} {t : k}
    (h : ∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) :
    ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := by
  obtain ⟨hk, hv⟩ := (GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec).1 hP
  obtain ⟨s, h1, h2⟩ := h
  refine ⟨s, ?_, h2⟩
  have h3 : g • (u - s • P.vec) ∈ P.ker := hk ▸ Submodule.smul_mem_pointwise_smul _ g _ h1
  have e : g.val *ᵥ u - s • P.vec = g • (u - s • P.vec) + s • (g • P.vec - P.vec) := by
    rw [smul_sub, smul_sub, smul_comm g s]
    change _ = g • u - _ + _
    change _ = g.val *ᵥ u - _ + _
    abel
  rw [e]
  exact add_mem h3 (P.ker.smul_mem s hv)

theorem glued_zero {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (u : n → k) : (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * 0 = q.inv * s) ↔ u ∈ P.ker := by
  constructor
  · rintro ⟨s, h1, h2⟩
    have hs : (s : k) = 0 := by
      rw [mul_zero, eq_comm, mul_eq_zero] at h2
      exact h2.resolve_left (inv_ne_zero q.ne_zero)
    have hs' : s = 0 := Subtype.ext hs
    simpa [hs'] using h1
  · intro h
    exact ⟨0, by simpa using h, by simp⟩

end GlobalTheory.Core.Mi.LatMatch.StabPair


open GlobalTheory.Core.Mi.LatMatch.StabPair in
theorem GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M q m P hs hM hm hG g
  have hE : ∀ x : n ⊕ Fin 1 → k, Formalism.L2.Theta.mt S (o.emb (β.gl g, 1)) *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) =
      fun i => p.sec ((β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr)) i) := fun x => by
    rw [mt_sec_any, vec_emb o ζ hs]
  constructor
  · intro hmov
    have hGG : ∀ (u : n → k) (t : k), (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) ↔
        ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := fun u t => by
      have := hmov (fun i => p.sec ((β₀.b *ᵥ Sum.elim u fun _ => t) i)) (fun i => GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _)
      rw [hE, mem_glued_iff hG, mem_glued_iff hG] at this
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Function.comp_apply] using this
    rw [GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec]
    have hker : ∀ u, u ∈ P.ker ↔ g.val *ᵥ u ∈ P.ker := fun u => by
      rw [← glued_zero (q := q) (m := m), ← glued_zero (q := q) (m := m), hGG]
    refine ⟨?_, ?_⟩
    · ext y
      rw [GlobalTheory.LatPair.mem_smul_iff, hker]
      change g.val *ᵥ ((g⁻¹ : GL n k).val *ᵥ y) ∈ P.ker ↔ _
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · have h1 : ∃ s : 𝒪[k], P.vec - s • P.vec ∈ P.ker ∧ m * (m⁻¹ * q.inv) = q.inv * s :=
        ⟨1, by simp, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]; simp⟩
      obtain ⟨s, h2, h3⟩ := (hGG _ _).1 h1
      have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
      have hs : (s : k) = 1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at h3
        exact mul_left_cancel₀ hq (h3.symm.trans (mul_one _).symm)
      have hs' : s = 1 := Subtype.ext hs
      change g.val *ᵥ P.vec - P.vec ∈ P.ker
      simpa [hs'] using h2
  · intro hP
    refine (sMoves_one _ _ _ _).1 (_root_.GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp D k p S M M 1 _ hM hM (normOneAt_one _) fun x => ?_)
    rw [map_one, one_smul]
    obtain ⟨y, rfl⟩ : ∃ y, x = β₀.b *ᵥ y := ⟨β₀.b' *ᵥ x, by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]⟩
    rw [vec_emb o ζ hs, mem_glued_iff hG, mem_glued_iff hG]
    simp only [Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply]
    refine ⟨glued_stab hP, fun h => ?_⟩
    have := glued_stab (inv_smul_eq_iff.2 hP.symm) h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.TFlatFam

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}

theorem om_split (s : StepFB ψ J B) (a : GA D J.W) (h : GA D B.V) (Φ : WO J.W B.V → ℂ) :
    s.om (a, h) Φ = s.om (a, 1) (s.om (1, h) Φ) := by
  have e : ((a, h) : GA D J.W × GA D B.V) = (a, 1) * (1, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem tFlat_eq_pairKer (hD : Descent D) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ) (hΦ : IsThetaFunO ψ J.W B.V Φ) (h₀ : GA D J.W₀)
    (h : GA D B.V) :
    tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) = pairKer s vL Y (flatFB s (s.om (1, h) Φ)) h₀ 1 := by
  have hc := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1
  rw [(embA B.d B.o).map_one, ← om_split] at hc
  have h1 : B.o.emb ((1 : GA D B.A), (1 : GA D B.L)) = 1 := B.o.emb.map_one
  rw [h1] at hc
  unfold tFlat pairKer
  rw [hc, h1]

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem star_psi_mul (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) * ψ a = 1 := by
  have h := Complex.conj_mul' (ψ a)
  rw [hψ.1.2.1 a] at h
  simpa using h

theorem pair_periodic (hψ : IsStdChar D ψ (-1)) (o : OrthDec B.V₀ B.A B.L) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (y : WO J.W₀ B.L → ℂ)
    (hy : ∀ γ w, y (ratW B.L J.W₀ γ + w) = ψ (-(symplOH J.W₀ B.L (ratW B.L J.W₀ γ) w)) * y w)
    (γ : Mx D B.L.rank J.W₀.rank) (hγ : γ ∈ ratMx D B.L.rank J.W₀.rank) (v : Mx D B.L.rank J.W₀.rank) :
    Ξ ((o.resT J.W₀).symm (0, γ + v)) * star (y (γ + v)) = Ξ ((o.resT J.W₀).symm (0, v)) * star (y v) := by
  obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
  have hmem : (o.resT J.W₀).symm (0, rat γ₀) ∈ ratL B.V₀ J.W₀ := by
    rw [o.mem_ratL_resT, AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, ⟨γ₀, rfl⟩⟩
  obtain ⟨g₀, hg₀⟩ := hmem
  have hg : ratW B.V₀ J.W₀ g₀ = (o.resT J.W₀).symm (0, rat γ₀) := hg₀
  have hsplit : (o.resT J.W₀).symm (0, rat γ₀ + v) = ratW B.V₀ J.W₀ g₀ + (o.resT J.W₀).symm (0, v) := by
    rw [hg, ← map_add (f := _), Prod.mk_add_mk, zero_add]
  have hsym : symplOH J.W₀ B.V₀ (ratW B.V₀ J.W₀ g₀) ((o.resT J.W₀).symm (0, v)) =
      symplOH J.W₀ B.L (ratW B.L J.W₀ γ₀) v := by
    rw [hg, o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
    rfl
  have hy' := hy γ₀ v
  have hrat : ratW B.L J.W₀ γ₀ = rat γ₀ := rfl
  rw [hrat] at hy'
  rw [hsplit, hΞ.quasi, hsym, hy', hrat, star_mul']
  calc ψ (-symplOH J.W₀ B.L (rat γ₀) v) * Ξ ((o.resT J.W₀).symm (0, v)) *
        (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * star (y v))
      = (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * ψ (-symplOH J.W₀ B.L (rat γ₀) v)) *
        (Ξ ((o.resT J.W₀).symm (0, v)) * star (y v)) := by ring
    _ = _ := by rw [star_psi_mul hψ, one_mul]

end GlobalTheory.Unf.FB.TFlatFam

namespace GlobalTheory.Unf.FB.TFlatFam

theorem flatFB_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (Ψ : WO J.W B.V → ℂ) :
    flatFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) 0 Ψ := rfl

theorem tFlat_eq_int {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) :
    tFlat s vL y Ψ = ∫ v in vL.𝓕, flatFB s Ψ ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := rfl

theorem main : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W B.V Φ → (Continuous fun p : GA D J.W₀ × GA D B.V => tFlat s vL (Y p.1) (s.om (J.d.emb0 p.1, p.2) Φ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h, tFlat s vL (Y (γ * h₀)) (s.om (J.d.emb0 (γ * h₀), h) Φ) = tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ∧ ∀ h, handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1 = ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
  intro D hD ψ σ J B s vL Y Φ hY hΦ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hflat : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) := fun h =>
    (_root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hxo, hx⟩ := _root_.GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B
    have hfl := _root_.GlobalTheory.FlatCont.flatAt_om_continuous D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hxo.1 Φ hΦ
    rw [hx] at hfl
    let f : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) →
        (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ :=
      fun vp => ((J.d.emb0 vp.2.1, vp.2.2), ((0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, vp.1)))
    have hf : Continuous f :=
      ((J.d.continuous_embed.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)).prodMk (continuous_const.prodMk
          ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_fst)))
    have h1 := hfl.comp hf
    let K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.V → ℂ := fun v p =>
      flatFB s (s.om (J.d.emb0 p.1, p.2) Φ) ((B.o.resT J.W₀).symm (0, v)) * star (Y p.1 v)
    have h2 : Continuous fun vp : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) => star (Y vp.2.1 vp.1) :=
      continuous_star.comp (hY.cont.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst))
    have hKc : Continuous (Function.uncurry K) := by
      have e : Function.uncurry K = fun vp => (fun q : (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ =>
          flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) q.2.1 (s.om q.1 Φ) q.2.2) (f vp) *
          star (Y vp.2.1 vp.1) := by
        funext vp
        simp only [Function.uncurry, K, f, flatFB_eq]
      rw [e]
      exact h1.mul h2
    have hKp : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ v p, K (γ + v) p = K v p := by
      intro γ hγ v p
      have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (J.d.emb0 p.1, p.2) Φ)) :=
        (_root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
      exact pair_periodic hψ B.o _ hΞ (Y p.1) (hY.quasi p.1) γ hγ v
    have hK := (_root_.GlobalTheory.Unf.ParCont.parCont D B.L.rank J.W₀.rank vL (GA D J.W₀ × GA D B.V) K hKc hKp).2.1
    simp only [tFlat_eq_int]
    exact hK
  · intro γ hγ h₀ h
    rw [tFlat_eq_pairKer hD s vL Y Φ hΦ, tFlat_eq_pairKer hD s vL Y Φ hΦ]
    exact (_root_.GlobalTheory.PairKer.pairKer_law D ψ σ J B s vL Y _ hY (hflat h)).2.1 γ hγ h₀ 1
  · intro h
    unfold handFB
    congr 1
    funext h₀
    exact (tFlat_eq_pairKer hD s vL Y Φ hΦ h₀ h).symm

end GlobalTheory.Unf.FB.TFlatFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.RowLevel

theorem rTrans_lev {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {a b k : GA D V} (ha : a ∈ GinfC V)
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans (a * b) (G w)) = χ (b⁻¹ * k * b) • rTrans (a * b) (G w) := by
  have h1 := (GlobalTheory.ValMoveProof.valMove D θ hθ V S M J χ).1 G hG w _ hm
  have hc : a * k = k * a := GlobalTheory.AdelicSplit.commute_GinfC_GfC V ha hk
  funext y
  have h2 := congrFun h1 (y * (a * b))
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [← h2]
  refine congrArg (G w) ?_
  calc y * k * (a * b) = y * (k * a) * b := by group
    _ = y * (a * k) * b := by rw [hc]
    _ = y * (a * b) * (b⁻¹ * k * b) := by group

theorem rightTranslate_level_conj_acts_by_character_finite {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {b k : GA D V}
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans b (G w)) = χ (b⁻¹ * k * b) • rTrans b (G w) := by
  have := rTrans_lev hθ M J χ G hG w (a := 1) (Subgroup.one_mem _) hk hm
  simpa only [one_mul] using this

theorem conj_mem_off {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} {M : ℕ}
    (hβ : IsSDFrame V β Λ M) (hN : IsSelfDualC V N) (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {b κ : GA D V} (hb : b ∈ GfC V)
    (hmv : ∀ p, P p → GlobalTheory.FinPl.Moves V b Λ N (· = p)) (hκ : GlobalTheory.FinPl.InK V N P κ) :
    b⁻¹ * κ * b ∈ levS V β L ∧ levChi V β L (b⁻¹ * κ * b) = 1 := by
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ M hβ
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨hκf, hκS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ κ).1 hκ.1
  have h1 : ∀ p, ¬ P p → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram p (b⁻¹ * κ * b) = 1 := fun p hp => by
    rw [map_mul, map_mul, hκS p hp, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hSt : Lev.finE V (b⁻¹ * κ * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr _).2 fun p => ?_
    by_cases hp : P p
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hΛ.1.fg p, GlobalTheory.StMoves.moves_conj_iff κ (hmv p hp)]
      exact GlobalTheory.LevConj.moves_at_of_moves hN.1 hp hκ.2
    · rw [h1 p hp]; exact one_mem _
  have h' : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Lev.finE V (b⁻¹ * κ * b)) = 1 := fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (h1 _ (hP PP h))
  refine ⟨⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) hκf) hb,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hSt h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ h', Units.val_one]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_eq_mu {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E}
    (hPP : PP ∈ L.Pg) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a)
    (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation k (π s) < 1)
    (c : ℕ) (hc : c < D.R.m) (μ : kˣ →* ℂˣ) (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta (c + 1)).1⁻¹ μ) (ht : IsTame μ)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (y : (kP PP)ˣ) (x : kˣ) (hy : (y : kP PP) = resS D.host.F PP s)
    (hx : (x : k) = π s) : L.chi (c + 1) PP y = μ x := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (y : kP PP)
  have hzP : z ∉ PP.asIdeal := fun hm => y.ne_zero (hz.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
  have hz0 : (z : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hzP (zero_mem _))
  have hπ : π (oToS D.host.F D.host.E z) = q.pr (incA D (z : D.host.E)) := h1 (incA D (z : D.host.E))
  have hv : valuation k (q.pr (incA D (z : D.host.E))) = 1 :=
    le_antisymm (hπ ▸ h3 (oToS D.host.F D.host.E z)) (not_lt.1 fun hl => hzP ((GlobalTheory.LocMod.LevBack.pr_lt q h z).2 hl))
  have hne : q.pr (incA D (z : D.host.E)) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hd : valuation k ((x : k) - q.pr (incA D (z : D.host.E))) < 1 := by
    have := (h4 (s - oToS D.host.F D.host.E z)).1 (by rw [map_sub, resS_oToS, hz, hy, sub_self])
    rwa [AddSubgroupClass.coe_sub, RingHom.map_sub, hπ, ← hx] at this
  have e1 : μ x = μ (Units.mk0 _ hne) := by
    have := ht (x * (Units.mk0 _ hne)⁻¹) (by
      have e : ((x * (Units.mk0 _ hne)⁻¹ : kˣ) : k) - 1 =
          ((x : k) - q.pr (incA D (z : D.host.E))) * (q.pr (incA D (z : D.host.E)))⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hne]; simp
      rw [e, map_mul, map_inv₀, hv, inv_one, mul_one]
      exact hd)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have e2 := hμ (Units.mk0 _ hne) (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) rfl
  have e3 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h (hL.mu0 ⟨c, hc⟩) hz0 (Units.mk0 _ hne) rfl
  have e4 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h hL.eta hz0 (Units.mk0 _ hne) rfl
  rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := Units.mk0 _ hz0)
    ((PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP), Units.val_one] at e4
  have e5 := hL.chi ⟨c, hc⟩ PP hPP z (Units.mk0 _ hz0) y rfl hz.symm
  rw [← e5] at e3
  have e4' : L.eta (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) = 1 := Circle.coe_injective e4
  apply Units.ext
  rw [e1, e2]
  unfold Lift.chrStep
  split_ifs
  · simp only [MonoidHom.inv_apply, MonoidHom.mul_apply, e4', inv_one, mul_one, Circle.coe_inv]
    rw [e3]; simp
  · simp only [MonoidHom.inv_apply, Circle.coe_inv]
    rw [e3]; simp

theorem red_lam {s κ t j n r : ℕ} (S : GlobalTheory.SymChain.SymData k s κ) (hr0 : r = κ + (s + 1)) (hr : r ≤ n)
    {e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j ≃ Fin n} (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) {O K : Type} [CommRing O]
    [CommRing K] [Nontrivial K] (φ : O →+* K) (ψ : O →+* k) (h1 : ∀ z, ψ z ∈ 𝒪[k]) (h2 : ∀ z, φ z = 0 ↔ valuation k (ψ z) < 1)
    (χ : ℕ → Kˣ →* ℂˣ) (hχ : ∀ c, c < j → ∀ (z : O) (y : Kˣ) (x : kˣ), (y : K) = φ z → (x : k) = ψ z → χ (c + 1) y = S.μ (c + 1) x)
    (Y : GL (Fin n) O) (g : (S.P.iter (Fin t) S.μ S.tame j).J)
    (hy : ∀ a b, ψ (Y.val (e a) (e b)) = (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j) k).val a b) :
    Formalism.UG.bc φ Y ∈ blockTri (blkOf r t) ∧ ∃ x : S.P.J, (∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O,
        φ z = (upperLeftBlock hr (Formalism.UG.bc φ Y)).val a' b' → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - ψ z) < 1) ∧
      (S.P.iter (Fin t) S.μ S.tame j).lam g =
        S.P.lam x * ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) (Formalism.UG.bc φ Y)) := by
  obtain ⟨-, hP⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ S (Fin t) j g.1).1 g.2
  have hb := (GlobalTheory.LocMod.LevBack.red_of_pattern S hr0 hr he φ ψ h1 h2 Y fun a b hab => by rw [hy]; exact hP a b hab).1
  obtain ⟨g₀, Dm, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ (Fin t) S.P S.μ S.tame j g
  refine ⟨hb, g₀, fun a b a' b' ha hb' z hz => ?_, ?_⟩
  · have hc : ∀ a (a' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → Fin.castLE hr a' = e (Sum.inl a) := fun a a' h =>
      Fin.ext (by rw [he]; rcases a with a | a <;> exact h)
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hb), submatrix_apply, hc a a' ha, hc b b' hb'] at hz
    rw [e0, submatrix_apply, ← hy, ← map_sub, ← h2, map_sub, hz]
    exact sub_self _
  · rw [el, Finset.prod_range]
    congr 1
    refine Finset.prod_congr rfl fun c _ => (hχ c c.2 (Ix.diagonalBlockOfMatrix (Y.val.submatrix e e) c).det _ _ ?_ ?_).symm
    · have hk := GlobalTheory.LocMod.LevBack.blkOf_zPos hr0 he
      have hbij : Function.Bijective fun i : Fin t =>
          (⟨e (.inr (c, i)), hk _⟩ : {i : Fin n // blkOf r t i = c.val + 1}) := by
        refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
        obtain ⟨i | ⟨c', s⟩, rfl⟩ := e.surjective i
        · exact absurd ((hk _).symm.trans hi) (Nat.succ_ne_zero _).symm
        · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((hk _).symm.trans hi))
          exact ⟨s, rfl⟩
      rw [diag_block_det_val _ hb, ← det_submatrix_equiv_self (Equiv.ofBijective _ hbij), RingHom.map_det]
      rfl
    · rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, RingHom.map_det]
      congr 1
      ext a b
      exact (hy _ _).symm

end Loc

theorem mat_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a) {V : HSp D}
    {β : GL (Fin V.rank) (Lev.EAf D)} {b x : GA D V} {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k V.rank Y) (L : LatFrame k ι Y) (e : ι ≃ Fin V.rank)
    (hmv : MovedTo (ofSplit q) V b β ((F.β * L.bas.val).submatrix id fun i => L.ord (e.symm i))) (xk : GL Y k)
    (hx : (mt V x).map q.pr = F.β * xk.val * F.γ) :
    GeneralLinearGroup.map π (β⁻¹ * Lev.finE V (b⁻¹ * x * b) * β) = reGL e (L.conj.symm xk) := by
  have hmap : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D), (M.map (toEAf D)).map π = M.map q.pr :=
    fun M => Matrix.ext fun _ _ => h1 _
  rw [← GlobalTheory.LocMod.LevBack.conj_frame F L e (GeneralLinearGroup.map π (Lev.finE V b * β))
    (GeneralLinearGroup.map π (Lev.finE V x)) (L.conj.symm xk) ?_ ?_]
  · rw [MonoidHom.map_mul (Lev.finE V), MonoidHom.map_mul (Lev.finE V), MonoidHom.map_inv, GlobalTheory.LocMod.LevBack.conj_conj,
      MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  · have hb : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
      Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
    refine Eq.trans ?_ (hmv _ hb)
    refine Eq.trans ?_ (hmap _)
    rw [Matrix.map_mul, hb]
    rfl
  · rw [MulEquiv.apply_symm_apply]
    exact (hmap _).trans hx

theorem conj_list_prod {G ι : Type} [Group G] (b : G) (h : ι → G) (l : List ι) :
    b⁻¹ * (l.map h).prod * b = (l.map fun i => b⁻¹ * h i * b).prod := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih]; group


end GlobalTheory.RowLevel
end

