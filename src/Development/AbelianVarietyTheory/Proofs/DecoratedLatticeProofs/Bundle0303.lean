module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple
section
namespace I195MixedCoordinates_73914be5564edd02d7192cbf

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_73914be5564edd02d7192cbf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.MixSumBound

variable {D : D7}

theorem finite_points_in_nhds (D : D7) (m n : ℕ) (K₀ : Set (Mx D m n)) (hK₀ : K₀ ∈ nhds (0 : Mx D m n)) :
    ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K₀ := by
  let K₁ : Set (Fin m → Fin n → AE D) := K₀
  have h1 : K₁ ∈ Filter.pi (fun _ : Fin m => nhds (0 : Fin n → AE D)) := by
    have : K₁ ∈ nhds (0 : Fin m → Fin n → AE D) := hK₀
    rwa [nhds_pi] at this
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 h1
  have h2 : ∀ i, ∃ J : Finset (Fin n), ∃ s : Fin n → Set (AE D), (∀ j, s j ∈ nhds (0 : AE D)) ∧
      (J : Set (Fin n)).pi s ⊆ t i := by
    intro i
    have h5 : t i ∈ Filter.pi (fun _ : Fin n => nhds (0 : AE D)) := by
      have : t i ∈ nhds (0 : Fin n → AE D) := ht i
      rwa [nhds_pi] at this
    exact Filter.mem_pi'.1 h5
  choose J s hs hJs using h2
  set V : Set (AE D) := ⋂ i, ⋂ j, s i j with hVdef
  have hV : V ∈ nhds (0 : AE D) := Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
  obtain ⟨U, hUo, hU⟩ := _root_.GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points D V hV
  let U' : AddSubgroup (Mx D m n) :=
    { carrier := {u | ∀ i j, u i j ∈ U}
      add_mem' := fun ha hb i j => U.add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => U.zero_mem
      neg_mem' := fun ha i j => U.neg_mem (ha i j) }
  refine ⟨U', ?_, fun u hu hfin => ?_⟩
  · have : (U' : Set (Mx D m n)) = ⋂ i, ⋂ j, (fun u : Mx D m n => u i j) ⁻¹' (U : Set (AE D)) := by
      ext u; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact Iff.rfl
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hUo.preimage ((continuous_apply j).comp (continuous_apply i))
  · show u ∈ K₁
    apply hIt
    intro i _
    apply hJs i
    intro j _
    have h3 : infPart D (u i j) = 0 := by
      have := congrFun (congrFun hfin i) j
      simpa using this
    have h4 := hU _ (hu i j) h3
    simp only [hVdef, Set.mem_iInter] at h4
    exact h4 i j

theorem realSize_nsmul (θ : InfFam D) {m n : ℕ} (N : ℕ) (x : Mx D m n) :
    realSize θ (N • x) = N * realSize θ x := by
  unfold realSize compAt
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, norm_mul, Complex.norm_natCast]

theorem inv_pow_le (k N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    ((1 + r) ^ k)⁻¹ ≤ (N : ℝ) ^ k * ((1 + N * r) ^ k)⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < (1 + r) ^ k := by positivity
  have h2 : 0 < (1 + N * r) ^ k := by positivity
  rw [← div_eq_mul_inv, inv_le_comm₀ h1 (by positivity), inv_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) k

end GlobalTheory.MixSumBound

namespace GlobalTheory.MixSumBound

theorem mixS_tsum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), ∃ k : ℕ, ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ w, (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ) ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ T.rank ρ
  refine ⟨k, fun K₀ hK₀ => ?_⟩
  obtain ⟨U, hUo, hU⟩ := finite_points_in_nhds D T.rank S.rank K₀ hK₀
  obtain ⟨K, hKc, hK⟩ := _root_.GlobalTheory.AnnihBox.annihilator_inBox D ψ hψ S S₀ T ρ d U hUo
  obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ S S₀ T ρ d v k
  have hM := hk K hKc
  refine ⟨C₁ * (∑' y : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k y)).toNNReal, fun n hn f hf hfix w => ?_⟩
  have hpt : ∀ x : Mx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤
      ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) * ENNReal.ofReal (maj θ K k (n • x)) := by
    intro x
    by_cases h0 : (_root_.I195MixedCoordinates_73914be5564edd02d7192cbf.source d) T ψ v.μ v.𝓕 f x w = 0
    · change d.mixS T ψ v.μ v.𝓕 f x w = 0 at h0
      simp [h0]
    have hbox : InBox K (n • x) := by
      apply hK
      intro a ha haU
      have hfin : (d.extY T a).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
      have hfix' := hfix _ (hU _ haU hfin) hfin
      have h2 := congrFun ((_root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf).2.1 x (n • a)) w
      rw [map_nsmul, hfix', Pi.smul_apply, smul_eq_mul] at h2
      have h3 : ψ (symplO S T (d.extX T x) (n • d.extY T a)) = 1 :=
        mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm)
      rw [map_nsmul, GlobalTheory.Mem.CoefInv.symplO_nsmul]
      exact h3
    have hmaj : maj θ K k (n • x) = ((1 + realSize θ (n • x)) ^ k)⁻¹ := by simp [maj, hbox]
    have hr := realSize_nonneg θ x
    have hdec := hC₁ f hf x w
    have hA : 0 < (1 + realSize θ x) ^ k := by positivity
    have hkey := inv_pow_le k n hn hr
    rw [← realSize_nsmul] at hkey
    calc ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ
        = ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ k) *
            ENNReal.ofReal (((1 + realSize θ x) ^ k)⁻¹) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul hA.le, mul_inv_cancel₀ hA.ne', ENNReal.ofReal_one, mul_one]
      _ ≤ (C₁ : ℝ≥0∞) * supSob ψ θ k f * ENNReal.ofReal ((n : ℝ) ^ k * ((1 + realSize θ (n • x)) ^ k)⁻¹) :=
          mul_le_mul' hdec (ENNReal.ofReal_le_ofReal hkey)
      _ = _ := by
          rw [hmaj, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          ring
  have hinj : Function.Injective fun x : ratMx D T.rank ρ => n • x := by
    intro x y hxy
    exact Subtype.ext (GlobalTheory.Mem.CoefInv.nsmul_cancel hn (congrArg Subtype.val hxy))
  calc (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ)
      ≤ ∑' x : ratMx D T.rank ρ, ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ENNReal.ofReal (maj θ K k ((n • x : ratMx D T.rank ρ) : Mx D T.rank ρ)) :=
        ENNReal.tsum_le_tsum fun x => by rw [AddSubgroup.coe_nsmul]; exact hpt x
    _ = ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ∑' x : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k ((n • x : ratMx D T.rank ρ) : Mx D T.rank ρ)) :=
        ENNReal.tsum_mul_left
    _ ≤ ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ∑' y : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k y) :=
        mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj
          (fun y : ratMx D T.rank ρ => ENNReal.ofReal (maj θ K k y)))
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM]
        ring

end GlobalTheory.MixSumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfRealQuotHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.MixSumBound

theorem ofReal_quotHeight_pow {D : D7} (T : HSp D) (A : ℕ) (h : GA D T) :
    ENNReal.ofReal (quotHeight T h ^ A) = ⨅ γ : GQ T, ENNReal.ofReal (height T (γ * h) ^ A) := by
  set φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (max t 1 ^ A) with hφ
  have hmono : Monotone φ := fun a b hab =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans (le_max_right _ _)) (max_le_max hab le_rfl) A)
  have hcont : Continuous φ := ENNReal.continuous_ofReal.comp ((continuous_id.max continuous_const).pow A)
  have hbdd : BddBelow (Set.range fun γ : GQ T => height T (γ * h)) :=
    ⟨1, by rintro _ ⟨γ, rfl⟩; exact one_le_height T _⟩
  have e := Monotone.map_ciInf_of_continuousAt hcont.continuousAt hmono hbdd
  have e1 : φ (quotHeight T h) = ENNReal.ofReal (quotHeight T h ^ A) := by
    simp only [hφ, max_eq_left (one_le_quotHeight T h)]
  have e2 : ∀ γ : GQ T, φ (height T (γ * h)) = ENNReal.ofReal (height T (γ * h) ^ A) := fun γ => by
    simp only [hφ, max_eq_left (one_le_height T _)]
  rw [← e1, quotHeight, e]
  exact iInf_congr e2

end GlobalTheory.MixSumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
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
namespace GlobalTheory.ChartStab


set_option maxHeartbeats 1000000 in
theorem mem_splitLat_iff {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (u : Fin n → Fv D.host.F v) :
    u ∈ GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ ↔
      ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) ≤ 1 := by
  set e := GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) with he_def
  have hπ : GlobalTheory.SplitHecke.Chart e v (rdA φ) := GlobalTheory.SplitProjChart.chart_idem φ
  have he : IsSplitIdem D e := GlobalTheory.EmbChart.isSplitIdem_idem _
  have hemb : GlobalTheory.AdelicU.chartEmb hπ = GlobalTheory.SplitProjChart.emb φ := AlgHom.ext fun x => by
    rw [GlobalTheory.AdelicU.chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  choose y hy using fun k => hπ.1 (u k)
  obtain ⟨Λ₁, hle, hfg, heq⟩ := GlobalTheory.ChainOnto.LStab.exists_fg_sub hβ
  have hsl : GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ₁ = GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ := by
    ext w
    rw [GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.ChainOnto.LStab.latLoc_eq hle hfg heq v]
  have h1 := GlobalTheory.AdelicU.SplitFrame.mem_latHat_iff_of_support (GlobalTheory.AdelicU.isCMExt_host D) _ hfg
    (GlobalTheory.AdelicU.SplitFrame.vecLoc_self he hπ y) (GlobalTheory.AdelicU.SplitFrame.vecLoc_ne he hπ y)
  rw [hemb, hsl, show (fun k => rdA φ (y k)) = u from funext hy] at h1
  rw [← h1, GlobalTheory.SplitFrameColumn.latHat_iff_hatL, heq]
  have hβ' := hβ (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k)))
  rw [hβ']
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  rw [hsw, Matrix.mulVec_smul]
  set w : Fin n → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hw
  refine forall_congr' fun i => ?_
  have h2 : (toEAf D e • w) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) := by
    rw [map_mul, GlobalTheory.SplitFrameColumn.toEAf_finEmb]; rfl
  have h3 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) := by
    rw [← GlobalTheory.SplitProjChart.rdE_toEAf, GlobalTheory.SplitFrameColumn.toEAf_finEmb, hw, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact (GlobalTheory.SplitProjChart.rdE_toEAf φ (y k)).trans (hy k)
  rw [h2, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (w i))) from rfl,
    GlobalTheory.SplitFrameColumn.comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h3]

theorem hermND (D : D7) (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem isSelfDualAt_of_isSelfDualC {D : D7} (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSelfDualC V Λ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.IsSelfDualAt D.sp.cm.sig V.gram Λ v := by
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (hermND D V).2 (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ)).2 (fun y => ?_) v
  refine (hΛ.2 y).trans (forall₂_congr fun x _ => ?_)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

theorem isSplitBasis_frCo {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.SplitProjChart.emb φ) Λ (frCo φ β) := fun u => by
  rw [mem_splitLat_iff hβ φ, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem grpCo_emb {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (x : GlobalTheory.FinZeta.Gv V v) :
    grpCo φ V B (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x) =
      GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (hermND D V) (GlobalTheory.SplitProjChart.emb φ) B x := by
  rw [GlobalTheory.AdelicU.splitEquivIn_apply, ← GlobalTheory.SplitChartLink.rdA_matHom_embV]
  rfl

section Reindex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem reindex_mem_KO {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    {x : GL m K} (hx : x ∈ GlobalTheory.SplitWeil.KO K m) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    y ∈ GlobalTheory.SplitWeil.KO K ι := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (ValuativeRel.valuation K).integer (ValuativeRel.valuation K).integer ε.symm).toMonoidHom a, ?_⟩
  ext i j
  rw [h]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem mem_KO_iff_reindex {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    (x : GL m K) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    x ∈ GlobalTheory.SplitWeil.KO K m ↔ y ∈ GlobalTheory.SplitWeil.KO K ι :=
  ⟨fun hx => reindex_mem_KO ε hx y h,
    fun hy => reindex_mem_KO ε.symm hy x fun i j => by rw [h]; simp⟩

end Reindex

theorem chart_stab : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  intro D s k v φ ι hsd hfr hch e he y
  obtain ⟨ε, -, hε⟩ := hch
  have hB := isSplitBasis_frCo hfr φ
  have hL := isSelfDualAt_of_isSelfDualC s.V hsd v
  rw [GlobalTheory.AdelicU.mem_stabLoc_iff_GLint (GlobalTheory.AdelicU.isCMExt_host D) (hermND D s.V) hL hB,
    (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v _).1]
  have h2 := (hε y).2
  rw [he y, grpCo_emb] at h2
  exact mem_KO_iff_reindex ε _ y fun i j => by rw [← h2]; rfl

end GlobalTheory.ChartStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V]

theorem altE_add_left' (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp [altE, map_add (f := _)]

theorem altE_add_right' (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by
  simp [altE, map_add (f := _)]

theorem real_smul_eq (r : ℝ) (x : V) : r • x = (r : ℂ) • x := by
  rw [← algebraMap_smul ℂ r x]; rfl

theorem altE_smul_left' (H : Sesq V) (r : ℝ) (x y : V) : altE H (r • x) y = r * altE H x y := by
  rw [real_smul_eq]; simp [altE]

theorem altE_smul_right' (H : Sesq V) (r : ℝ) (x y : V) : altE H x (r • y) = r * altE H x y := by
  rw [real_smul_eq]; unfold altE; rw [(H x).map_smulₛₗ]; simp

theorem fg_of_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hc : Countable Λ) (hΛ : IsSelfDual H Λ) : Λ.FG := by
  classical
  have hK : ∀ x : V, (∀ y ∈ Λ, altE H x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hmem : ∀ t : ℝ, t • x ∈ Λ := fun t => by
      have h1 : t • x ∈ dualLat H Λ := fun y hy => ⟨0, by rw [altE_smul_left', hx y hy]; simp⟩
      rwa [hΛ] at h1
    let f : ℝ → Λ := fun t => ⟨t • x, hmem t⟩
    have hf : Function.Injective f := fun s t h => by
      have : s • x = t • x := congrArg Subtype.val h
      exact smul_left_injective ℝ hx0 this
    exact not_countable (α := ℝ) hf.countable
  obtain ⟨b, hbΛ, hbspan, hbli⟩ := exists_linearIndependent ℝ (Λ : Set V)
  haveI : Finite b := hbli.setFinite.to_subtype
  have hint : ∀ x ∈ Λ, ∀ e ∈ b, ((⌊altE H x e⌋ : ℤ) : ℝ) = altE H x e := by
    intro x hx e he
    have hx' : x ∈ dualLat H Λ := by rw [hΛ]; exact hx
    obtain ⟨m, hm⟩ := hx' e (hbΛ he)
    rw [hm, Int.floor_intCast]
  let g : Λ →+ (b → ℤ) :=
    { toFun := fun x e => ⌊altE H (x : V) e⌋
      map_zero' := by funext e; simp [altE]
      map_add' := fun x y => by
        funext e
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.add_apply, Int.cast_add]
        rw [hint _ (x + y).2 _ e.2, hint _ x.2 _ e.2, hint _ y.2 _ e.2]
        simp [altE_add_left'] }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ e ∈ b, altE H (x : V) e = 0 := fun e he => by
      have h2 : ⌊altE H (x : V) e⌋ = 0 := congrFun hx ⟨e, he⟩
      rw [← hint _ x.2 _ he, h2]; simp
    have hspan : ∀ y ∈ Submodule.span ℝ b, altE H (x : V) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact h0 y hy
      | zero => simp [altE]
      | add y z _ _ hy hz => rw [altE_add_right', hy, hz, add_zero]
      | smul r y _ hy => rw [altE_smul_right', hy, mul_zero]
    exact Subtype.ext (hK x fun y hy => hspan y (hbspan ▸ Submodule.subset_span hy))
  haveI : IsNoetherian ℤ Λ := isNoetherian_of_injective g.toIntLinearMap hg
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact (AddGroup.fg_iff_addSubgroup_fg Λ).1 this

end General
end GlobalTheory.PeriodReps

namespace GlobalTheory.PeriodReps
open Formalism.L2.Th1.H

theorem countable_lamC {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) :
    Countable (Formalism.L2.Ker.LamC emb δ AA0 N N') := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin b) (Fin a) E) := inferInstanceAs (Countable (Fin b → Fin a → E))
  haveI : Countable (Formalism.L2.Col.HomE E a b) :=
    (LinearMap.toMatrix' : ((Fin a → E) →ₗ[E] (Fin b → E)) ≃ₗ[E] Matrix (Fin b) (Fin a) E).injective.countable
  have hsub : ((Formalism.L2.Ker.LamC emb δ AA0 N N' : AddSubgroup _) : Set (Formalism.L2.Ker.VV ι a b)) ⊆
      Set.range (Formalism.L2.Ker.embH emb δ) := by
    intro y hy
    simp only [Formalism.L2.Ker.LamC, Formalism.L2.Ker.laV, SetLike.mem_coe, AddSubgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact ((Set.countable_range _).mono hsub).to_subtype

theorem reps_genuine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  intro D ψ θ S T a b hS hT δ sc hSP e SS hSS N N' c hc hcS hSS2 hLa
  have hfg := fg_of_selfDual _ _ (countable_lamC _ _ _ _ _) hLa.1
  obtain ⟨i1, i2, i3⟩ := Formalism.L2.Ker.finite_index_of_fg _ _ _ _ (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c hc hfg
  exact ⟨Formalism.L2.Ker.repsOf_spec _ _ i1, Formalism.L2.Ker.repsOf_spec _ _ i2, Formalism.L2.Ker.repsOf_spec _ _ i3⟩

end GlobalTheory.PeriodReps
end
end

