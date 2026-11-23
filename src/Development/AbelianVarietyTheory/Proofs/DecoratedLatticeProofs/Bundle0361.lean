module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalDoublingIntegralOddCase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.ContrSum

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_colE_indep {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ)
    (μ : kˣ →* ℂˣ) (β : n → k) (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    om μ 1 (colE c p β) Φ = om 1 1 (colE c p β) Φ := by
  have h : Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
    apply Units.ext
    simp [colE, upU, Matrix.GeneralLinearGroup.val_det_apply]
  funext x
  simp only [om, h, map_one]

theorem isClosedEmbedding_negCol (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n → k) =>
      (fromCols q.1 (Matrix.of fun r (_ : Unit) => (-q.2) r) : Matrix n (n' ⊕ Unit) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix n (n' ⊕ Unit) k => (z.toCols₁, fun r => -z r (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, β⟩
    simp
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun r => (continuous_id.matrix_elem _ _).neg)
  · refine continuous_matrix fun r s => ?_
    rcases s with s | s
    · exact continuous_fst.matrix_elem _ _
    · exact ((continuous_apply r).comp continuous_snd).neg

theorem isClosedEmbedding_row (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n' → k) =>
      (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2) : Matrix (n ⊕ Unit) n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix (n ⊕ Unit) n' k => (z.toRows₁, z (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, u⟩
    rfl
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun s => continuous_id.matrix_elem _ _)
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r
    · exact continuous_fst.matrix_elem _ _
    · exact (continuous_apply s).comp continuous_snd

theorem exists_sum_prod (n n' m' : Type) [Fintype n] [Fintype n'] [Fintype m']
    (F : SB (Matrix n n' k × (m' → k))) :
    ∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n n' k)) (Φ₀ : Fin m → SB (m' → k)),
      ∀ x β, F.1 (x, β) = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix n n' k) := inferInstanceAs (TotallyDisconnectedSpace (n → n' → k))
  haveI : LocallyCompactSpace (Matrix n n' k) := inferInstanceAs (LocallyCompactSpace (n → n' → k))
  haveI : T2Space (Matrix n n' k) := inferInstanceAs (T2Space (n → n' → k))
  have hmem : F ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix n n' k) × SB (m' → k) => prodSB q.1 q.2) := by
    rw [Span.span_prodSB_eq_top]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  refine ⟨N, fun i => f i • (p i).1, fun i => (p i).2, fun x β => ?_⟩
  rw [← hq, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hp i]
  simp only [prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

variable [MeasurableSpace k] [BorelSpace k]

theorem fl_eq_flCol (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν)
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (h1 : 1 ≤ ρ) (hc : c = 2 * ρ)
    (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n n' k) (β : n → k) :
    fl ψ ν μ ρ Φ.1 x β = flCol ψ ν (ρ + 1) Φ.1 (fromCols x (Matrix.of fun r (_ : Unit) => (-β) r)) := by
  have h := (((GlobalTheory.RootEx.FourierJacobi.fourierJacobiBessel k).2.2.2.1 n n' c ρ h1 hc).2.2.2 ψ ν hψ hne hν).1
    1 continuous_const Φ β
  have h2 := h.2 x
  unfold fl at h2 ⊢
  rw [om_colE_indep, h2]
  rfl

theorem contr_flat_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ : kˣ →* ℂˣ) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1 ∈ SB (Matrix n₁ (n₀ ⊕ Unit) k) ∧ GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1 ∈ SB (Matrix (n₂ ⊕ Unit) n₁ k) ∧ (∀ Φ₀ : SB (n₁ → k), opEFJ ψ ν ρ Φ₀.1 Φ₂.1 ∈ SB (Matrix n₂ n₁ k)) ∧ (∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), ∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) ∧ ∀ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), (∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) → ∀ x, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1) x = ∑ i, (Ψ i).1 x.1 * opEFJ ψ ν ρ (Φ₀ i).1 Φ₂.1 x.2 := by
  intro k _ _ _ _ _ _ ψ hψ hne ν hν n₀ _ _ n₁ _ _ n₂ _ _ c ρ hc μ Φ₁ Φ₂
  haveI := hν.1
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix n₂ n₁ k) := inferInstanceAs (T2Space (n₂ → n₁ → k))
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular ν
  have h1 : 1 ≤ ρ := by omega
  have hA := ((flat_SB_onto k ψ ν hψ hν.1 n₁ n₀ (c + 1) (ρ + 1) (by omega)).1 (by omega)).1 _ Φ₁.2
  have hB := ((flat_SB_onto k ψ ν hψ hν.1 n₂ n₁ c ρ h1).2 (by omega)).1 _ Φ₂.2
  have hfl := fl_eq_flCol ψ hψ hne ν hν (c + 1) ρ h1 hc μ Φ₁
  have hG : (fun q : Matrix n₂ n₁ k × (n₁ → k) =>
      flRow ψ ν ρ Φ₂.1 (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2))) ∈ SB _ :=
    ⟨hB.1.comp_continuous (isClosedEmbedding_row n₂ n₁).continuous,
      hB.2.comp_isClosedEmbedding (isClosedEmbedding_row n₂ n₁)⟩
  have hE : ∀ (Φ₀ : (n₁ → k) → ℂ) (x : Matrix n₂ n₁ k), opEFJ ψ ν ρ Φ₀ Φ₂.1 x =
      ∫ u, flRow ψ ν ρ Φ₂.1 (fromRows x (Matrix.of fun (_ : Unit) => u)) * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀ u
        ∂(Measure.pi fun _ => ν) := by
    intro Φ₀ x
    unfold opEFJ
    congr 1
    funext u
    rw [mul_comm]
    rfl
  refine ⟨hA, hB, fun Φ₀ => ?_, ?_, fun m Ψ Φ₀ hd x => ?_⟩
  · rw [funext (hE Φ₀.1)]
    exact integral_mul_mem_SB _ _ hG _
  · obtain ⟨m, Ψ, Φ₀, h⟩ := exists_sum_prod n₁ n₀ n₁
      ⟨_, hA.1.comp_continuous (isClosedEmbedding_negCol n₁ n₀).continuous,
        hA.2.comp_isClosedEmbedding (isClosedEmbedding_negCol n₁ n₀)⟩
    exact ⟨m, Ψ, Φ₀, fun x β => (hfl x β).trans (h x β)⟩
  · obtain ⟨c₀, hc₀⟩ := (conductor_exists k).1 ψ hψ hne
    have hhat : ∀ u, GlobalTheory.StepData.hat ψ ν (-1)
        (fun y => flCol ψ ν (ρ + 1) Φ₁.1 (fromCols x.1 (Matrix.of fun r (_ : Unit) => y r))) u =
        ∑ i, (Ψ i).1 x.1 * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u := by
      intro u
      unfold GlobalTheory.StepData.hat GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat
      rw [← integral_neg_eq_self]
      simp only [← hfl, hd, dotProduct_neg, neg_mul_neg, one_mul, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro i _
        have := GlobalTheory.StepData.integrable_hat ψ ν 1 hψ (Φ₀ i).2 u
        simp only [one_mul] at this
        exact this.const_mul _
    unfold contr
    simp only [hhat, hE, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    · intro i _
      have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n₁ => ν) hc₀ (Φ₀ i).2
      have hF' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 ∈ SB (n₁ → k) := by
        convert hF using 1
        funext y
        simp [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm]
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hF'.2.mul_left)
      exact (hG.1.continuous.comp (Continuous.prodMk_right x.2)).mul (continuous_const.mul hF'.1.continuous)

end GlobalTheory.LocFlat.ContrSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QParL

theorem seg_eq_segL : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP →
    ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  intro D v φ PP hφ x ϖ hx z t
  obtain ⟨-, hq⟩ := GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ
  obtain ⟨e, -, -, -, hϖ⟩ := hx
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  refine Multiset.map_congr rfl fun n _ => ?_
  congr 1
  ext
  rw [GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem qPar_succ {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x (k + 1) = (qPar c PP x k).map (· * (Circle.toUnits (c.chS (k + 1) x) * (Circle.toUnits (c.chT (k + 1) x))⁻¹)) +
      GlobalTheory.LFun.seg PP (Circle.toUnits (c.chS (k + 1) x)) D.R.t := rfl

theorem card_qPar {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) : (qPar c PP x k).card = k * D.R.t := by
  induction k with
  | zero => simp [qPar]
  | succ k ih => rw [qPar_succ, Multiset.card_add, Multiset.card_map, ih, GlobalTheory.LFun.card_seg]; ring

theorem seg_map_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (z u : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w z t).map (· * u) = GlobalTheory.LFun.seg w (z * u) t := by
  simp only [GlobalTheory.LFun.seg, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun i _ => mul_right_comm _ _ _

theorem sum_map_mul {ι : Type} (s : Finset ι) (f : ι → Multiset ℂˣ) (u : ℂˣ) :
    (∑ i ∈ s, f i).map (· * u) = ∑ i ∈ s, (f i).map (· * u) :=
  map_sum (Multiset.mapAddMonoidHom (· * u)) f s

theorem qPar_closed {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x k = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * c.eps k) x)) D.R.t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qPar_succ, ih, sum_map_mul, Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [seg_map_mul, ← GlobalTheory.ChainOnto.ParClosed.eps_succ]
      congr 1
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
      ext
      simp only [Units.val_mul]
      ring
    · rw [GlobalTheory.ChainOnto.ParClosed.chS_succ]

theorem qPar_twist {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) =
      ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x)) D.R.t := by
  rw [qPar_closed, sum_map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [seg_map_mul, GlobalTheory.ChainOnto.ParClosed.chT_succ]
  congr 1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [_root_.mul_inv_rev]
  group

theorem invNormFactor_eq (q t k : ℕ) :
    GlobalTheory.GLDoubling.invNormFactor q (k * t) ((t : ℂ) / 2) =
      ((∏ n ∈ Finset.Ioc t ((k + 1) * t), (1 - ((q : ℝ) ^ n)⁻¹) : ℝ) : ℂ) := by
  unfold GlobalTheory.GLDoubling.invNormFactor
  push_cast
  rw [show (k + 1) * t = t + k * t by ring]
  generalize k * t = m
  have h1 : Finset.Ioc t (t + m) = (Finset.Icc 1 m).map (addLeftEmbedding t) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Icc, addLeftEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - t, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
  rw [h1, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (2 * ((t : ℂ) / 2) + (i : ℂ)) = ((addLeftEmbedding t i : ℕ) : ℂ) := by
    simp only [addLeftEmbedding_apply]; push_cast; ring
  rw [this, Complex.cpow_neg, Complex.cpow_natCast]

end GlobalTheory.QParL

open GlobalTheory.QParL in
theorem GlobalTheory.ChainTw.qPar_twist_lFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  intro D c w hw k hk PP hPP v φ hφ x ϖ hx
  refine ⟨seg_eq_segL D v φ PP hφ x ϖ hx, card_qPar c PP x k, fun α hα => ?_⟩
  rw [qPar_twist] at hα
  have hz : ∀ i ∈ Finset.Icc 1 k, Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x) =
      GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP := fun i hi =>
    GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value D v φ PP hφ x ϖ hx _ (GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place D c w hw PP hPP i (k + 1) (Finset.mem_Icc.1 hi).1
      (by have := (Finset.mem_Icc.1 hi).2; omega) (by omega) (by omega))
  have hα' : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k,
      GlobalTheory.LFun.seg PP (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) D.R.t := by
    rw [hα]; exact Finset.sum_congr rfl fun i hi => by rw [hz i hi]
  obtain ⟨hb, hL⟩ := _root_.GlobalTheory.LFun.seg_bounds_and_doubling_lFactor PP k D.R.t (k * D.R.t)
    (fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) (fun i => GlobalTheory.LFun.norm_val _ _) α hα'
  refine ⟨hb, ?_⟩
  rw [hL, invNormFactor_eq, blockL, zinv]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegerIffOfEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Filter Topology

namespace GlobalTheory.PlaceSplitPt

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
  (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem mem_integer_iff_of_equiv (σ : K ≃+* K') (h1 : Continuous σ) (h2 : Continuous σ.symm) (a : K) :
    a ∈ 𝒪[K] ↔ σ a ∈ 𝒪[K'] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  constructor
  · intro h
    refine le_one_of_map σ.symm.toRingHom h2 ?_
    change valuation K (σ.symm (σ a)) ≤ 1
    rwa [σ.symm_apply_apply]
  · exact le_one_of_map σ.toRingHom h1

end Val

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]

section Chart

variable {v : Pl D} (p : Place D k) (he : SplitAt D v p.e)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def toFv : k ≃+* Fv D.host.F v where
  toFun a := comp he (p.ι a)
  invFun b := p.π (sec D v p.e b)
  left_inv a := by
    change p.π (sec D v p.e (comp he (p.ι a))) = a
    rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι, p.π_ι]
  right_inv b := by
    change comp he (p.ι (p.π (sec D v p.e b))) = b
    rw [p.ι_π, map_mul, comp_self, one_mul, GlobalTheory.LocMod.SplitCompl.comp_sec]
  map_mul' x y := by
    change comp he (p.ι (x * y)) = comp he (p.ι x) * comp he (p.ι y)
    rw [ι_mul, map_mul]
  map_add' x y := by
    change comp he (p.ι (x + y)) = comp he (p.ι x) + comp he (p.ι y)
    rw [map_add (f := _), map_add (f := _)]

theorem continuous_toFv : Continuous (toFv p he) := (continuous_comp he).comp p.cont_ι

theorem continuous_toFv_symm : Continuous (toFv p he).symm := p.cont_π.comp continuous_sec

include he in
theorem int_iff (a : k) : a ∈ 𝒪[k] ↔ finPart D (p.ι a) ∈ intAE D := by
  rw [mem_integer_iff_of_equiv (toFv p he) (continuous_toFv p he) (continuous_toFv_symm p he) a,
    GlobalTheory.LocMod.SplitCompl.int_iff_sec he]
  change finPart D (sec D v p.e (comp he (p.ι a))) ∈ intAE D ↔ _
  rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι]

end Chart

theorem exists_splitPt : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k), ∃ q : GlobalTheory.FinPl.SplitPt D k, GlobalTheory.LocMod.Place.ofSplitPt q = p := by
  intro D k _ _ _ _ p
  obtain ⟨-, -, v, ε, hε, hs⟩ := p.split
  have he : SplitAt D v p.e := splitAt_of p.split hε hs
  exact ⟨⟨v, p.e, p.split, ⟨ε, hε, hs⟩, p.π, p.ι, p.π_ι, p.ι_π, p.cont_π, p.cont_ι, int_iff p he⟩, rfl⟩

end GlobalTheory.PlaceSplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockComb

theorem om_pureTensorO_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT (e : WO S T →₀ ℂ) (f₀ f : WO S T → ℂ) (x : ℂ), IsFinComb e → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, om (b, b') f = x • comb ψ S T e f₀ → ∀ P, ∀ a ∈ GinfC S, ∀ a' ∈ GinfC T, om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT f P) = x • comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) ∧ ∀ (N : Lat S) (N' : Lat T), Vac ψ S T N N' (fun _ => True) f₀ → Vac ψ S T N N' (fun _ => True) (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  intro D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ f x he hf₀ hf b hb b' hb' hfx P a ha a' ha'
  have hψ : IsStdChar D ψ (-1) := hW.std

  have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hth₀ : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ P) :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT 1 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f₀ hf₀ P).1

  have hcomb : comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) =
      pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
    let q := e.support.equivFin
    have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
      (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
    have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
      intro g
      rw [← Finset.sum_coe_sort e.support]
      exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
    simp only [comb]
    rw [h1, h1]
    exact key
  refine ⟨?_, fun N N' hv => ?_⟩
  · have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2, hfx, GlobalTheory.FiniteFock.pureTensorO_smul, ← hcomb, map_smul,
      GlobalTheory.FrComb.om_comb hW ha ha' he hth₀]
  · refine ⟨hW.om_pres _ _ hth₀, GlobalTheory.FrComb.latVac_om hW ha ha' hth₀ ?_⟩
    have fix : ∀ u ∈ latO S T (N : Set _) (N' : Set _) (fun _ => True), heisO ψ S T u f₀ = f₀ →
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT f₀ P := by
      intro u hu h0
      have := ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f₀ hf₀).2 u (GlobalTheory.SplitScalar.latO_fin hu)).2 sS BS sT BT P
      rw [← this, h0]
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hv.2.1 u hu),
      fun e' he' u hu hh => fix u hu (hv.2.2 e' he' u hu hh)⟩

end GlobalTheory.FockComb
end
end

