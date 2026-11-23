module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SigConv

variable {D : D7}

theorem mt_jX_eq {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have e3 : blockX d n = 1 + T := by
    rw [blockX, h1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  rw [e3, h1, Matrix.mul_add, Matrix.mul_one]

theorem blockX_mul_inv {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    blockX d n ⬝ blockX d n⁻¹ = 1 := by
  have h1 := mt_jX_eq d (inv_mem hn)
  have h2 := mt_jX_eq d hn
  have h3 : d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹) = d.jX := by
    rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
      Matrix.one_mul]
  have h4 : d.pX ⬝ (d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹)) = d.pX ⬝ d.jX := by rw [h3]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h4

theorem blockX_rat {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ B : Matrix (Fin ρ) (Fin ρ) D.host.E, rat B = blockX d γ :=
  mem_ratMx.1 (ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V γ).1 hγ) (rat_mem d.e)))

def sumAbs (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ) : ENNReal :=
  ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS Ψ x‖ₑ

end GlobalTheory.Unf.SigConv


open GlobalTheory.Unf.SigConv in
theorem GlobalTheory.Unf.sum_term_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.MixedAbsGrowth.mixed_abs_growth D ψ V W χV χW om hW V₀ ρ d vS Φ hΦ
  have hT := fun Ψ (hΨ : IsThetaFunO ψ V W Ψ) => _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ

  have hA : ∀ g h, sumAbs ψ d W vS (om (g, h) Φ) ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    intro g h
    refine le_trans ?_ (hC g h 0)
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E =>
        (⟨rat x, rat_mem x⟩ : ratMx D W.rank ρ))
      (fun x y hxy => rat_injective (congrArg Subtype.val hxy))
      (fun y : ratMx D W.rank ρ => ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) y 0‖ₑ)

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ γ ∈ GQ V, γ ∈ flagN d →
      sumAbs ψ d W vS (om (γ, 1) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ γ hQ hN
    obtain ⟨B, hB⟩ := blockX_rat d hQ
    have key : ∀ x, term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ (x * B) :=
      fun x => (hT Ψ hΨ).2.1 γ hQ hN x (x * B) (by rw [rat_mul, hB])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => x * B) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : x * B = y * B := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => (rat z : Mx D W.rank ρ) ⬝ blockX d γ⁻¹) hxy'
    simp only [rat_mul, hB, Matrix.mul_assoc, blockX_mul_inv d hN, Matrix.mul_one] at h5
    exact h5

  have hD : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ δ ∈ GQ W,
      sumAbs ψ d W vS (om (1, δ⁻¹) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ δ hQ
    obtain ⟨M, hM⟩ := mem_ratMx.1 ((mem_GQ_iff W δ).1 hQ)
    have key : ∀ x, term ψ d W vS (om (1, δ⁻¹) Ψ) x = term ψ d W vS Ψ (M * x) :=
      fun x => (hT Ψ hΨ).2.2.1 δ⁻¹ (inv_mem hQ) x (M * x)
        (by rw [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => M * x) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : M * x = M * y := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => mt W δ⁻¹ ⬝ (rat z : Mx D W.rank ρ)) hxy'
    simp only [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul] at h5
    exact h5

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image continuous_subtype_val)
  set c' := max c 1 with hc'
  set C₀ := max C 0 with hC₀
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set C' := C₀ * c' ^ A with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _)

  have hN : ∀ g h, ∀ n ∈ flagN d, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * height W h) ^ A) := by
    intro g h n hn
    obtain ⟨γ, hγ, k, hk, hnk⟩ := hcov ⟨n, hn⟩
    have hγQ : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have hn' : n = γ.1 * k.1 := congrArg Subtype.val hnk
    have hp : ((n * g, h) : GA D V × GA D W) = (γ.1, 1) * (k.1 * g, h) := by
      rw [hn']; ext <;> simp [mul_assoc]
    have hom : om (n * g, h) Φ = om (γ.1, 1) (om (k.1 * g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    refine (hB _ (hW.om_pres _ _ hΦ) γ.1 hγQ γ.2).trans ((hA _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V k.1 ≤ c' := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (k.1 * g) ≤ c' * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx : height V (k.1 * g) * height W h ≤ c' * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (k.1 * g) * height W h) ^ A ≤ C₀ * (height V (k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ C₀ * (c' * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hC₀0
      _ = C' * (height V g * height W h) ^ A := by rw [mul_pow, hC', mul_assoc]
  refine ⟨C', A, fun g h n hn => ?_⟩

  have hδ : ∀ δ : GQ W, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * max (height W (δ.1 * h)) 0) ^ A) := by
    intro δ
    rw [max_eq_left (height_pos W _).le]
    have hp : ((n * g, h) : GA D V × GA D W) = (1, δ.1⁻¹) * (n * g, δ.1 * h) := by
      ext <;> simp [← mul_assoc]
    have hom : om (n * g, h) Φ = om (1, δ.1⁻¹) (om (n * g, δ.1 * h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    exact (hD _ (hW.om_pres _ _ hΦ) δ.1 δ.2).trans (hN g _ n hn)
  let φ : ℝ → ENNReal := fun t => ENNReal.ofReal (C' * (height V g * max t 0) ^ A)
  have hmono : Monotone φ := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC'0
    apply pow_le_pow_left₀ (mul_nonneg (height_pos V g).le (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) (height_pos V g).le
  have hcont : Continuous φ := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have hinf := hmono.map_ciInf_of_continuousAt (g := fun δ : GQ W => height W (δ.1 * h)) hcont.continuousAt
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height W _⟩
  have hq : ENNReal.ofReal (C' * (height V g * quotHeight W h) ^ A) = φ (quotHeight W h) := by
    simp only [φ, max_eq_left (quotHeight_pos W h).le]
  change sumAbs ψ d W vS (om (n * g, h) Φ) ≤ _
  rw [hq, quotHeight, hinf]
  exact le_iInf hδ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartLevel

variable {D : D7}

open ValuativeRel in
theorem val_lt_one_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h : valuation (Fv D.host.F v) 1 ≤ valuation (Fv D.host.F v) x ↔ Valued.v (1 : Fv D.host.F v) ≤ Valued.v x := by
    haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]


set_option maxHeartbeats 1000000 in
theorem redFn_entry_eq_zero_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V}
    (hS : Lev.finE V g ∈ St β) {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : SplitProj D v} {PP : Pl D.host.E}
    (hφ : IsProjAt φ PP) (a b : Fin V.rank) :
    (redFn β PP (Lev.finE V g)).val a b = 0 ↔ Valued.v ((grpCo φ V (frCo φ β) g).val a b) < 1 := by
  obtain ⟨⟨r, -, hr0, -, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  obtain ⟨y, hy⟩ := hS
  rw [← hy, redFn_frGL]
  obtain ⟨h, hrd⟩ := hN _ (y.val a b).2
  have e1 : (Formalism.UG.bc (resS D.host.F PP) y).val a b = resS D.host.F PP (y.val a b) := rfl
  rw [e1, ← hrd, hr0]
  have hi : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V g * β := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  have hx : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Lev.finE V g) =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V g) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Lev.finE V g).val i j) = rdA φ ((Formalism.L2.Theta.matHom V g).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (β⁻¹ * Lev.finE V g * β) = grpCo φ V (frCo φ β) g := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hx]
    rfl
  have key : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (grpCo φ V (frCo φ β) g).val a b := by
    rw [← hm, ← hi]
    rfl
  change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1 ↔ _
  rw [key]

end GlobalTheory.ChartLevel

namespace GlobalTheory.ChartLevel

variable {D : D7}

theorem eps_inr_ge {r n : ℕ} {B : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (i : B) :
    r ≤ (ε (.inr i) : ℕ) := by
  by_contra h
  rw [not_le] at h
  have e : ε (.inl ⟨_, h⟩) = ε (.inr i) := Fin.ext (hε _)
  exact Sum.inl_ne_inr (ε.injective e)

theorem twoBlockIndex_lt_iff_lowerLeft {r n : ℕ} (a b : Fin n) : blk2 r b < blk2 r a ↔ (b : ℕ) < r ∧ r ≤ (a : ℕ) := by
  unfold blk2
  by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb] <;> omega

theorem lower_iff {r n : ℕ} {B K : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (M : Fin n → Fin n → K)
    (P : K → Prop) : (∀ a b : Fin n, blk2 r b < blk2 r a → P (M a b)) ↔ ∀ i j, P (M (ε (.inr i)) (ε (.inl j))) := by
  constructor
  · intro h i j
    refine h _ _ ((twoBlockIndex_lt_iff_lowerLeft _ _).2 ⟨?_, eps_inr_ge ε hε i⟩)
    rw [hε]; exact j.2
  · intro h a b hab
    rw [twoBlockIndex_lt_iff_lowerLeft] at hab
    obtain ⟨p, rfl⟩ := ε.surjective a
    obtain ⟨q, rfl⟩ := ε.surjective b
    rcases p with p | p
    · exfalso; rw [hε] at hab; have := p.2; omega
    rcases q with q | q
    · exact h p q
    · exfalso; have := eps_inr_ge ε hε q; omega

end GlobalTheory.ChartLevel


open GlobalTheory.ChartLevel in
theorem GlobalTheory.chart_level_iff : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι y
  obtain ⟨hr, hL, hfl⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hfr : IsFrame s.β s.Λ := hfl.frame
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hsd hfr hι
  have hstab := _root_.GlobalTheory.ChartStab.chart_stab D s j v φ ι hsd hfr hι e he y
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  have hSt : Lev.finE s.V (ι y) ∈ St s.β ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr, he y, ← hstab]
    constructor
    · intro h
      have := h v
      rwa [GlobalTheory.AdelicU.proj_emb_self] at this
    · intro h u
      by_cases hu : u = v
      · subst hu
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact h
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ hu]
        exact one_mem _
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → Lev.finE s.V (ι y) ∈ St s.β →
      redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne hS
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hred : Lev.finE s.V (ι y) ∈ St s.β → (redFn s.β PP (Lev.finE s.V (ι y)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ i j', ValuativeRel.valuation (Fv D.host.F v) (y.1 (.inr i) (.inl j')) < 1) := by
    intro hS
    rw [mem_blockTri]
    have h1 : ∀ a b, (redFn s.β PP (Lev.finE s.V (ι y))).val a b = 0 ↔
        Valued.v ((grpCo φ s.V (frCo φ s.β) (ι y)).val a b) < 1 := redFn_entry_eq_zero_iff hS hφ
    simp only [h1]
    rw [lower_iff ε hε (fun a b => (grpCo φ s.V (frCo φ s.β) (ι y)).val a b) (fun x => Valued.v x < 1)]
    have hy : ∀ p q, (grpCo φ s.V (frCo φ s.β) (ι y)).val (ε p) (ε q) = y.1 p q := fun p q => by
      have := congrFun (congrFun (hch y).2 p) q
      simpa using this
    simp only [hy, val_lt_one_iff]
  have hG : ι y ∈ GfC s.V := by
    rw [he y]; exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC _ _ _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, ← hSt, hL, Lev.levG, Lev.mem_levA, mem_lev, mem_parLev]
  constructor
  · rintro ⟨-, ⟨-, hS, -, hQ⟩, -⟩
    exact ⟨hS, (hred hS).1 (hQ PP hPP)⟩
  · rintro ⟨hS, hlow⟩
    have hPg : ∀ PP' ∈ w.Pg, redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
      intro PP' hP'
      refine hone PP' (hsub _ (Or.inl hP')) ?_ hS
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    refine ⟨hG, ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hS, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPg PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · subst e
        exact (hred hS).2 hlow
      · rw [hone PP' (hsub _ (Or.inr hP')) e hS]
        exact one_mem _
    · have h1 : rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B)
          (Lev.finE s.V (ι y)) = 1 := by
        funext PP'
        show upperLeftBlock hr (redFn s.β PP'.1 (Lev.finE s.V (ι y))) = 1
        rw [hPg PP'.1 PP'.2]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact one_mem _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField IsDedekindDomain GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_unif (q : Unif k) {x : k} (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
  have hx' : x ∈ 𝒪[k] := hx.le
  have hm : (⟨x, hx'⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
    rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have h : x = (c : k) * ((q.1 : 𝒪[k]) : k) := by
    have := congrArg (fun z : 𝒪[k] => (z : k)) hc
    simpa using this.symm
  rw [h, Valuation.map_mul]
  have hc1 : valuation k (c : k) ≤ 1 := c.2
  exact (mul_le_mul_of_nonneg_right hc1 zero_le').trans_eq (one_mul _)

theorem val_unif_lt_one (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 q.2.not_isUnit

theorem val_unif_pos (q : Unif k) : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
  rw [zero_lt_iff, Valuation.ne_zero_iff]
  exact fun h => q.2.ne_zero (Subtype.ext h)

variable {D : D7}

theorem val_prF_le_one (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : Formalism.L2.Herm.intAf D.host.F D.host.E) : valuation k (p.prF he c.1) ≤ 1 :=
  (p.prF_mem_iff he c.1).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he).1 c.2)

theorem val_lt_of_mem_idS_of_forall (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt p.e PP) {I : Ideal (𝓞 D.host.E)} {γ : ValueGroupWithZero k} (hγ : 0 < γ)
    (hI : ∀ a ∈ I, valuation k (p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E a : EAf D)) < γ)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    valuation k (p.prF he s.1) < γ := by
  refine Submodule.span_induction (p := fun s _ => valuation k (p.prF he s.1) < γ) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · simpa using hγ
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (p.val_prF_le_one he c) zero_le').trans_lt (by rwa [one_mul])

theorem val_eq_unif_and_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  intro D k _ _ _ _ p PP he t t' ht ht2 ht'
  let f : 𝓞 D.host.E →+* k :=
    (p.prF he).comp ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.comp (Formalism.L2.DIV.oToS D.host.F D.host.E))
  have hf : ∀ x : 𝓞 D.host.E, f x = p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D) := fun _ => rfl
  have hf' : ∀ x : 𝓞 D.host.E, p.pr (incA D (x : D.host.E)) = f x := fun x =>
    (p.prF_toEAf he (incA D (x : D.host.E))).symm
  have hle : ∀ x, valuation k (f x) ≤ 1 := fun x => p.val_prF_le_one he _
  have hlt : ∀ x, x ∈ PP.asIdeal ↔ valuation k (f x) < 1 := fun x => p.mem_iff_val_lt he x
  rw [hf', hf']
  refine ⟨?_, le_antisymm (hle _) (not_lt.1 fun h => ht' ((hlt _).2 h))⟩
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  refine ⟨q, le_antisymm (val_le_unif q ((hlt _).1 ht)) (not_lt.1 fun hlt' => ?_)⟩
  set γ := valuation k ((q.1 : 𝒪[k]) : k) with hγ
  have hγ0 : 0 < γ := val_unif_pos q

  have hPP : Ideal.span {t} ⊔ PP.asIdeal ^ 2 = PP.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := PP.asIdeal) (I := Ideal.span {t} ⊔ PP.asIdeal ^ 2) (i := 1)
      PP.ne_bot (lt_of_le_of_ne le_sup_right fun h => ht2 (by
        rw [show (2 : ℕ) = 1 + 1 from rfl, h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)))
      (by
        rw [pow_one]
        exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero))
    rwa [pow_one] at h
  have hsq : ∀ a ∈ PP.asIdeal ^ 2, valuation k (f a) < γ := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, Valuation.map_mul]
      calc _ ≤ valuation k (f x) * γ := mul_le_mul_of_nonneg_left (val_le_unif q ((hlt _).1 hy)) zero_le'
        _ < 1 * γ := mul_lt_mul_of_pos_right ((hlt _).1 hx) hγ0
        _ = γ := one_mul _
    · rw [map_add (f := _)]; exact Valuation.map_add_lt _ hx hy
  have hall : ∀ a ∈ PP.asIdeal, valuation k (f a) < γ := by
    intro a ha
    rw [← hPP] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_add (f := _)]
    refine Valuation.map_add_lt _ ?_ (hsq y hy)
    rw [map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hle c) zero_le').trans_lt (by rwa [one_mul])

  have hs : toEAf D (p.sec ((q.1 : 𝒪[k]) : k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart ((p.int_iff _).1 q.1.2)
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, hs⟩
  have hsv : p.prF he s.1 = ((q.1 : 𝒪[k]) : k) := (p.prF_toEAf he _).trans (p.pr_sec _)
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h2 := val_lt_of_mem_idS_of_forall p he hγ0 hall ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub, hsv, ← hf] at h2
  have hγ1 : γ < 1 := val_unif_lt_one q
  have haP : a ∈ PP.asIdeal := (hlt a).2 (by simpa using Valuation.map_sub_lt _ hγ1 (h2.trans hγ1))
  have h3 := Valuation.map_add_lt _ h2 (hall a haP)
  rw [sub_add_cancel] at h3
  exact lt_irrefl _ h3

end GlobalTheory.FinPl.SplitPt

end
end

