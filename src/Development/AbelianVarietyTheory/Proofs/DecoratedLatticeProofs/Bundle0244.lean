module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unscaled

variable {D : D7}

def rescale {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E) (hμ : μ ≠ 0) : HypDec S S₀ ρ where
  e := μ • d.e
  e' := (star μ)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero]
  e'e' := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero]
  e'e := by
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      mul_inv_cancel₀ hμ, one_smul]
  iso := d.iso
  i₀e := by simp only [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by simp only [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

end GlobalTheory.Core.Mi.Unscaled

namespace GlobalTheory.Core.Mi


open GlobalTheory.Core.SBesEx GlobalTheory.Core.Mi.Unscaled in
theorem exists_sBes_scaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ (μ : D.host.E) (vA : Vol (D.sp.X 0)), μ ≠ 0 → ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ B.vA = vA ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hP⟩ := GlobalTheory.Core.Mi.tiepsi_sign D X h u ψ hE hψ
  have hg : ((X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero X)
  have hl0 : lam ≠ 0 := by
    rcases hlam with hl | hl <;> rw [hl]
    · exact hg
    · exact neg_ne_zero.2 hg
  refine ⟨lam, hlam, fun μ vA hμ => ?_⟩
  obtain ⟨L, t, ht, hL1, hz0, hLg⟩ := GlobalTheory.RankOneLine.exists_line D X u
  obtain ⟨⟨V₀, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D (D.sp.X 0) L
  obtain ⟨d₀, hde, hde', hdi⟩ := GlobalTheory.Core.SBesEx.exists_hypDec D X h u F₀ tr t lam ht hl0 (GlobalTheory.Core.SBesEx.cY_isom D X h hE)
    (GlobalTheory.Core.Mi.transported_frame_gram_orth D X u F₀ tr) L hL1 hLg V₀ o
  have hcard : Fintype.card (Fin L.rank) = 1 := by rw [Fintype.card_fin, hL1]
  have hz₀ : d₀.i₀ *ᵥ vecB o (zeta L) = t • cY X h (X.zu u) := by
    rw [vecB, Matrix.mulVec_mulVec, hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iB, o.qB_iB,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
    funext k
    simp only [Matrix.mulVec, dotProduct, zM, zeta, mul_one, Finset.sum_const, Finset.card_univ, hcard, one_smul,
      Pi.smul_apply, smul_eq_mul]
  have hline₀ : IsLineVec L (zeta L) := by
    refine ⟨hL1, ?_⟩
    simp only [zeta, hLg, dotProduct, Matrix.mulVec, Pi.star_apply, star_one, one_mul, mul_one, Finset.sum_const,
      Finset.card_univ, hcard, one_smul]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 ht) ht) hz0
  have ht' : μ * t⁻¹ ≠ 0 := mul_ne_zero hμ (inv_ne_zero ht)
  set d := rescale d₀ (μ * t⁻¹) ht' with hd
  set ζ : Fin L.rank → D.host.E := (μ * t⁻¹) • zeta L with hζ
  have hline : IsLineVec L ζ := by
    refine ⟨hline₀.1, ?_⟩
    rw [hζ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero (star_ne_zero.2 ht') (mul_ne_zero ht' hline₀.2)
  have hde1 : d.e = eM X h μ lam := by
    funext k a
    show ((μ * t⁻¹) • d₀.e) k a = _
    rw [hde]
    simp only [Matrix.smul_apply, eM, scl, smul_eq_mul]
    field_simp
  have hde1' : d.e' = e'M X h μ lam := by
    funext k a
    show ((star (μ * t⁻¹))⁻¹ • d₀.e') k a = _
    rw [hde']
    simp only [Matrix.smul_apply, e'M, scl, smul_eq_mul, star_mul', star_inv₀, inv_inv, mul_inv]
    have hst : star t ≠ 0 := star_ne_zero.2 ht
    field_simp
  have hz : d.i₀ *ᵥ vecB o ζ = μ • cY X h (X.zu u) := by
    show d₀.i₀ *ᵥ (o.iB *ᵥ ((μ * t⁻¹) • zeta L)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← vecB, hz₀, smul_smul, inv_mul_cancel_right₀ ht]
  refine ⟨SBes.mk V₀ L d o ζ hline (GlobalTheory.Unf.DefCpt.coCpt_X_zero D) vA
    (GlobalTheory.Unf.Inhab.nonempty_volN d).some (_root_.GlobalTheory.Core.SBesFlagTie.mem_flagN_iff D X h u μ lam hμ hl0 hE V₀ d hde1)
    (_root_.GlobalTheory.Core.SBesLevi.range_embA_eq_H D X h u μ lam hμ hl0 hE V₀ L d o ζ hline hde1 hde1' hz)
    (hP μ hμ V₀ L d o ζ hde1 hde1' hz), ?_, rfl, ?_, ?_, ?_⟩
  · intro k j
    show (d₀.i₀ * o.iA) k j = _
    rw [hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iA, o.qB_iA, Matrix.mul_zero, add_zero,
      Matrix.mul_one]
    rfl
  · intro k
    show (d.i₀ *ᵥ vecB o ζ) k = _
    rw [hz]
    rfl
  · intro k a
    show d.e k a = _
    rw [hde1]
    rfl
  · intro k a
    show d.e' k a = _
    rw [hde1']
    rfl

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroMapsCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul_left {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x) : MxAt P (y ⬝ x) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem symplO_resT_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A) (t : WO T S) :
    symplO T S ((o.resT T).symm (a, 0)) t = symplO T A a (o.pA ⬝ t) := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  have h0 : symplO T L 0 ((o.resT T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO T A, MxAt (· = p.v) u → (u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v) ↔ ∀ u' ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), ψ (symplO T A u u') = 1)) → (∀ u : WO T S, MxAt (· = p.v) u → (u ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) ↔ ∀ u' ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v), ψ (symplO T S u u') = 1)) → halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), (o.resT T).symm (u, 0) ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO T A (LT : Set _) (LA : Set _) (· = p.v) with hΛA
  set ΛS := latO T S (LT : Set _) (LS : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hrow0 : GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zrow β ζ (0 : WO T L) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zrow, Matrix.vecMul_zero, Pi.zero_apply, map_zero]
      have : ((fun _ => 0 : Fin T.rank → k) ᵥ* β.b) = 0 := Matrix.zero_vecMul _
      rw [this, smul_zero]
    have h0 : IsHalf p.e (0 : WO T L) := fun i j => by simp
    have hd : InDual ΛT (0 : n → k) := fun y _ => by
      rw [zero_dotProduct]; exact zero_mem _
    simp [GlobalTheory.FinPl.ExtZero.rowFun, hz, dualInd, h0, hd]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resT T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resT T).symm (a, 0))
    rw [OrthDec.boxT, AddEquiv.apply_symm_apply, hrow0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → o.pA ⬝ t ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxT] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resT T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D T A _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resT T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resT T).symm (u, 0)) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
    exact mxAt_mul_left _ huM
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resT_symm_left, ← hsplit u' hu'M, Matrix.mul_add, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO T A u (o.pA ⬝ (p.e • u'))) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO T A u (o.pA ⬝ (cA D p.e • u'))) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO T A (cA D p.e • u) (o.pA ⬝ (cA D p.e • u')) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_left_comm, (smul_isHalf hce.1 u') l j]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resT_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB.ThLaws

variable {D : D7}

theorem heisO_zero_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T p f 0 = f p := by
  rw [heisO, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem jacS_zero_apply (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (n : GA D S) (f : WO S₀ T → ℂ) :
    jacS ψ d T x n f 0 = ψ (cenS d T x n) * f (ptS d T x n) := by
  rw [jacS, Pi.smul_apply, smul_eq_mul, heisO_zero_apply]

theorem jacS_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (c : skewA D ρ) (f : WO S₀ T → ℂ) : jacS ψ d T x (d.nC c) f = ψ (d.qS T c x) • f := by
  have h := ptS_nB_mul_nC d T x 0 c
  rw [d.nB_zero, one_mul, Matrix.mul_zero] at h
  rw [jacS, h, cenS_nC, heisO_zero]

theorem continuous_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) : Continuous (psiE ψ) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp ht

theorem continuous_upSum {X : Type} [TopologicalSpace X] {ρ : ℕ} {T : X → Mx D ρ ρ} (hT : Continuous T) :
    Continuous fun t => upSum (T t) := by
  unfold upSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true]; exact (continuous_apply j).comp ((continuous_apply i).comp hT)
  · simp only [h, if_false]; exact continuous_const

theorem continuous_psiFlag {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) : Continuous (psiFlag ψ d) := by
  unfold psiFlag blockX
  exact (continuous_psiE hψ).comp
    (continuous_upSum (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt S).matrix_mul continuous_const)))

theorem continuous_ptS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (ptS d T x) := by
  unfold ptS
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S)).matrix_mul continuous_const

theorem continuous_cenS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (cenS d T x) := by
  unfold cenS
  exact GlobalTheory.OrientedHeis.continuous_symplOH continuous_const
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S))

theorem exists_bound_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S L : HSp D}
    {y : WO S L → ℂ} (hy : Quasi ψ S L y) : ∃ M : ℝ, ∀ w, ‖y w‖ ≤ M := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D L.rank S.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hy.2.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, ⟨γ0, rfl⟩, hγ⟩ := hKc w
  have h2 : ‖y w‖ = ‖y (ratW L S γ0 + w)‖ := by rw [hy.1 γ0 w, norm_mul, hψ.2.1, one_mul]
  rw [h2]
  exact hC _ hγ

theorem zl_rat {σ : ℕ} (B : BesLev D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zl B = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zl, zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem ptS_rat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ g0, ptS d T (rat x0) γ = ratW T S₀ g0 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  refine ⟨x0 * d.qX * g * d.i₀, ?_⟩
  rw [ratW_eq, ptS, HypDec.extX_apply, ← hg]
  simp only [rat_mul]
  rfl

theorem psi_cenS_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ψ (cenS d T (rat x0) γ) = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : cenS d T (rat x0) γ = symplOH S T ((x0 * d.qX).map (incA D)) ((x0 * d.qX * g).map (incA D)) := by
    rw [cenS, HypDec.extX_apply, ← hg]
    change _ = symplOH S T (rat (x0 * d.qX)) (rat (x0 * d.qX * g))
    simp only [rat_mul]
    rfl
  rw [e]
  exact GlobalTheory.AnisoMean.psi_rat hψ S T _ _

theorem upSum_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat M : Mx D ρ ρ) = incA D (∑ i, ∑ j, if j.1 = i.1 + 1 then M i j else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [upSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [rat]

theorem psiE_incA {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : D.host.E) : psiE ψ (incA D t) = 1 := by
  rw [psiE, show Algebra.trace (AF D.host.F) (AE D) (incA D t) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) from GlobalTheory.AnisoMean.trace_one_tmul (AF D.host.F) t]
  exact hψ.2.2.1 _

theorem psiFlag_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {γ : GA D S} (hγ : γ ∈ GQ S) : psiFlag ψ d γ = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : blockX d γ = rat (d.qX * (g * d.e)) := by
    rw [blockX, ← hg]
    simp only [rat_mul]
    rfl
  rw [psiFlag, e, upSum_rat, psiE_incA hψ]

theorem psiFlag_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) :
    psiFlag ψ d (d.nC c) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nC_jX c), upSum_one, psiE_zero]

theorem psiFlag_nB (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (b : Mx D ρ S₀.rank) :
    psiFlag ψ d (d.nB b) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nB_jX b), upSum_one, psiE_zero]

theorem psiFlag_levi (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) :
    psiFlag ψ d (d.levi u) = psiUni ψ u := by
  rw [psiFlag_eq, psiBes_levi]

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → Continuous (th J ψ B y) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖th J ψ B y n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, th J ψ B y (γ * n) = th J ψ B y n) ∧ (∀ c, ∀ n ∈ flagN J.d, th J ψ B y (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zl B))) * th J ψ B y n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), th J ψ B y (n * J.d.levi u) = th J ψ B y n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), th J ψ B y (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zl B ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zl B) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, th J ψ B y n =
      star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [th, jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : th J ψ B y = fun n =>
        star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zl_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zl B) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    rw [th, (hmul _ hc n hn).2.2, th, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    rw [th, hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, th, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zl B) (J.d.nB b) = zl B ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zl B) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zl B) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    rw [th, hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.SplitUnifIdele

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  intro D v w hw hs χ _
  obtain ⟨e, he⟩ := GlobalTheory.WeilAtPlace.exists_isIdemAt_of_split hs hw
  have hP : IsPrimeIdem w e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hee : e * e = e := he.1.1
  have hlt : w.asIdeal ^ 2 < w.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (by norm_num : 1 < 2)
  rw [pow_one] at hlt
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt hlt
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    exact h2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have hab : incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
  have hba : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [mul_comm]; exact hab
  let x : (AE D)ˣ := ⟨e * incA D (ϖ : D.host.E) + (1 - e), e * incA D ((ϖ : D.host.E)⁻¹) + (1 - e),
    by linear_combination (incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hab,
    by linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hba⟩
  refine ⟨e, ϖ, x, he, h1, h2, rfl, fun χ' hχ' => ?_⟩
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x (by
      change e * (e * incA D (ϖ : D.host.E) + (1 - e) - 1) = e * incA D (ϖ : D.host.E) + (1 - e) - 1
      linear_combination (incA D (ϖ : D.host.E) - 1) * hee)
  have hy' : (y : w.adicCompletion D.host.E) = algebraMap D.host.E _ (ϖ : D.host.E) := by
    rw [hy, show (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) from rfl,
      GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), GlobalTheory.LFun.compAt_incA]
  have hu : Formalism.L2.Host.IsUnifAt w y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hy']
    exact (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans
      (GlobalTheory.LFun.EulerTie.valuation_of_mem_notMem_sq w h1 h2)
  have := hχ'.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.SplitUnifIdele

end
end

