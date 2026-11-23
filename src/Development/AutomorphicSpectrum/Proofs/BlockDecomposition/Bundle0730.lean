module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresented
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_ring {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : AddChar A ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1) (κ : Type) [Fintype κ]
    [FirstCountableTopology (κ → A)] [MeasurableSpace (κ → A)] [OpensMeasurableSpace (κ → A)]
    (μ : Measure (κ → A)) [μ.IsOpenPosMeasure]
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (φ : Y → ℂ) (g : Y → κ → A)
    (hg : Measurable g) (N : Set (κ → A)) (hN : IsOpen N)
    (hb : Integrable φ ν → Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ →
      ∀ N' : Set (κ → A), IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : (κ → A) → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0)
    (z₀ : κ → A) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → A) × (κ → A) => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hd1 : ∀ w, Continuous fun v : κ → A => ψ (-(v ⬝ᵥ w)) := fun w =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_id continuous_const)).neg
  have hd2 : ∀ v, Continuous fun w : κ → A => ψ (-(v ⬝ᵥ w)) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id)).neg
  have hd3 : ∀ v, Continuous fun w : κ → A => ψ (v ⬝ᵥ w) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id))
  by_cases hφ : Integrable φ ν
  swap
  · have h0 : ∀ v : κ → A, ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν = 0 := fun v =>
      integral_undef fun hi => hφ (integrable_of_mul_unimodular ν φ (fun y => ψ (v ⬝ᵥ g y)) hi
        ((hd3 v).measurable.comp hg).aestronglyMeasurable fun y => hψn _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) = 0
    rw [h0 v, zero_mul]
  by_cases hJ : Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ
  swap
  · exact integral_undef fun hi => hJ (integrable_of_mul_unimodular μ _ (fun v => ψ (-(v ⬝ᵥ z₀))) hi
      (hd1 z₀).aestronglyMeasurable fun y => hψn _)
  exact vanish_abs μ (fun v z => ψ (-(v ⬝ᵥ z))) hd1 hd2 (fun _ _ => hψn _) _ hJ N hN (hb hφ hJ) z₀ hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_generic (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)]
    [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) (hμ : GlobalTheory.SWLit.IsTamagawa F κ μ)
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F)
    (hg : Measurable g) (N : Set (κ → AF F)) (hN : IsOpen N) (hgN : ∀ y, g y ∉ N)
    (z₀ : κ → AF F) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ.1
  refine vanish_ring ψ hψ.1 hψ.2.1 κ μ Y ν φ g hg N hN ?_ z₀ hz
  intro hφ hJ N' hN' hsub z₁ hz₁
  obtain ⟨Φ, hΦ, hΦ0, hΦN, hΦ1⟩ := _root_.GlobalTheory.CompanionTheory.AdelicBump.exists_bump F κ N' hN' z₁ hz₁
  obtain ⟨hΦc, -, hΦi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  exact ⟨Φ, hΦc, hΦi μ hμ.1, hΦ0, hΦN, hΦ1,
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish F hF ψ hψ κ μ hμ Y ν φ g hφ hg hJ Φ hΦ (fun y => hΦN _ fun h' => hgN y (hsub h'))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

variable {D : D7}

theorem posOn_add_smul_one {n : ℕ} {ε δ : ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)}
    (hS : NonnegOn ε Z S) (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) :
    PosOn ε (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) S := by
  intro w hw hne
  have h0 := hS w hw
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hB : 0 < (star w ⬝ᵥ w).re := by
    have e : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    rw [e]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (star w ⬝ᵥ (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec w).re =
      (star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  rw [e2]
  have : ε * ((star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re) =
      ε * (star w ⬝ᵥ Z.mulVec w).re + (ε * ε) * δ * (star w ⬝ᵥ w).re := by ring
  rw [this, hεε, one_mul]
  exact add_pos_of_nonneg_of_pos h0 (mul_pos hδ hB)

theorem compAt_add' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a b : Mx D m n) :
    compAt θ ρ (a + b) = compAt θ ρ a + compAt θ ρ b := by
  exact Matrix.map_add (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_add a b

theorem compAt_neg' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a : Mx D m n) :
    compAt θ ρ (-a) = -compAt θ ρ a := by
  exact Matrix.map_neg (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_neg a

theorem W_eq_zero_of_obstruction (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (h : Hyp D r V ψ θ μ lam ν φ) (β : HermE D r) (ρ : D.what₂.Tau) (ε : ℝ)
    (S : Submodule ℂ (Fin r → ℂ)) (hε : ε = 1 ∨ ε = -1) (hS : NonnegOn ε (β.1.map (tauE D ρ)) S)
    (hT : ∀ T : Submodule ℂ (Fin V.rank → ℂ), PosOn ε (gramAt D V ρ) T →
      Module.finrank ℂ T < Module.finrank ℂ S) :
    W ψ V μ lam φ β = 0 := by
  obtain ⟨hr, hψ, hθ, ⟨𝓕, hF⟩, ⟨𝓖, hG⟩, -, -, -⟩ := h
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hF.1
  obtain ⟨n, c, u, R, hu, hR, hRu, hcu, hTam⟩ := _root_.GlobalTheory.CompanionTheory.HermCoord.coords D r lam 𝓖 hG
  have hin := _root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts D θ hθ V r ρ
  let g : Mx D V.rank r → Fin n → AF D.host.F := fun y => u (inner V y y)
  have hgc : Continuous g := hu.comp hin.1
  let N : Set (Fin n → AF D.host.F) := {w | PosOn ε (compAt θ ρ (R w)) S}
  have hN : IsOpen N :=
    (_root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn r ε S).preimage ((GlobalTheory.RealWeil.continuous_compAt hθ ρ r r).comp hR)
  have hgN : ∀ y, g y ∉ N := by
    intro y hy
    have h1 : PosOn ε (compAt θ ρ (R (u (inner V y y)))) S := hy
    rw [hRu _ (hin.2 y).1, (hin.2 y).2] at h1
    obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.positivity_pulls_back_to_subspace _ _ _ _ ε S h1
    have := hT T hT1
    omega
  let z₀ : Fin n → AF D.host.F := u (rat β.1)
  have hcl : ∀ e' : ℕ → Mx D r r, (∀ k, e' k ∈ hermA D r) → Filter.Tendsto e' Filter.atTop (nhds 0) →
      (∀ k : ℕ, compAt θ ρ (e' k) = ((ε * ((1 : ℝ) / ((k : ℝ) + 1)) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) →
      z₀ ∈ closure N := by
    intro e' he' het hec
    have hlim : Filter.Tendsto (fun k => u (rat β.1 + e' k)) Filter.atTop (nhds z₀) := by
      have h2 : Filter.Tendsto (fun k => rat β.1 + e' k) Filter.atTop (nhds (rat β.1 + 0)) :=
        tendsto_const_nhds.add het
      rw [add_zero] at h2
      exact (hu.tendsto _).comp h2
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    show PosOn ε (compAt θ ρ (R (u (rat β.1 + e' k)))) S
    have hrat : compAt θ ρ (rat β.1) = β.1.map (tauE D ρ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ ρ β.1
    rw [hRu _ ((hermA D r).add_mem (GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA β) (he' k)), compAt_add', hec k, hrat]
    exact posOn_add_smul_one hS hε (by positivity)
  obtain ⟨e, he, het, hec⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq D θ hθ r
  have hz : z₀ ∈ closure N := by
    rcases hε with rfl | rfl
    · refine hcl e he het fun k => ?_
      rw [hec k, one_mul]
    · refine hcl (fun k => -e k) (fun k => (hermA D r).neg_mem (he k)) ?_ fun k => ?_
      · have h3 := het.neg
        rw [neg_zero] at h3
        exact h3
      · rw [compAt_neg', hec k]
        simp
  have key := vanish_generic D.host.F D.sp.cm.totReal ψ hψ (Fin n) (lam.map c.symm) hTam _ μ φ g
    hgc.measurable N hN hgN z₀ hz
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hemb : MeasurableEmbedding (c.symm) := c.symm.toHomeomorph.measurableEmbedding
  rw [hemb.integral_map] at key
  refine Eq.trans ?_ key
  unfold W
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ x : Mx D r r, c.symm b ⬝ᵥ u x = halfTr (Matrix.trace (HMul.hMul b.1 x : Mx D r r)) := fun x => by
    rw [← hcu]; simp
  show Jt ψ V μ φ b * _ = (∫ y, φ y * ψ (c.symm b ⬝ᵥ u (inner V y y)) ∂μ) * ψ (-(c.symm b ⬝ᵥ u (rat β.1)))
  simp only [h1]
  rw [Matrix.trace_mul_comm]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem noFrame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ h t β hβ hno
  obtain ⟨ρ, ε, S, hε, hS, hT⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction D r V h.1 t β hβ hno
  rw [W_eq_zero_of_obstruction r V ψ θ μ lam ν φ h β ρ ε S hε hS hT]
  haveI hemp : IsEmpty {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
    ⟨fun x => hno ⟨x.1, x.2⟩⟩
  unfold IfrB
  have h0 : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q) = fun _ => (0 : ℂ) := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, tsum_empty]
  rw [h0]
  simp [MeasureTheory.average]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.Centre

open GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem centre_commutes_embedded_block {R : Type} [CommRing R] (hn : ρ + p = n) (z : Matrix (Fin ρ) (Fin ρ) R)
    (a b c d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (blk4 1 (bl hn z 0 0 0) 0 1)
        (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)) =
      HMul.hMul (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d))
        (blk4 1 (bl hn z 0 0 0) 0 1) := by
  have h1 : HMul.hMul (bl hn z 0 0 0) (bl hn 0 0 0 c) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  have h2 : HMul.hMul (bl hn z 0 0 0) (bl hn 1 0 0 d) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h3 : HMul.hMul (bl hn 1 0 0 a) (bl hn z 0 0 0) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h4 : HMul.hMul (bl hn 0 0 0 c) (bl hn z 0 0 0) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, h1, h2, h3, h4]
  congr 1 <;> simp [add_comm]

theorem nzx_add (M : Maps D hn) (a b : hermA D ρ) : M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0 := by
  rw [nzx_mul, add_zero]

theorem nzx_comm_sh (M : Maps D hn) (z : hermA D ρ) (y : Mx D ρ p) :
    M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0 := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.sh_mat, adj_zero]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem nzx_comm_emb (M : Maps D hn) (z : hermA D ρ) (h : G D p) :
    M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0 := by
  obtain ⟨b, d, hb⟩ := SmallCell.exists_blocks (mat h)
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.emb_mat h _ _ _ _ hb, adj_zero]
  exact centre_commutes_embedded_block hn z.1 _ _ _ _

theorem nzx_rat_mat (M : Maps D hn) (l : ratHerm D ρ) :
    ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := BigCell.exists_hermQ l
  have e : ∀ {a c : ℕ}, (0 : Matrix (Fin a) (Fin c) D.host.E).map (incA D) = 0 := rat_zero'
  refine ⟨b.1, hb, ?_⟩
  rw [blockMatrix_map₂, hb, e, e, e, M.nzx_mat, adj_zero]

theorem nzx_mem_GF (M : Maps D hn) (l : ratHerm D ρ) : M.nzx l.1 0 ∈ GF D n := by
  have h := nzx_rat M l.1 l.2 0
  rwa [rat_zero'] at h

end GlobalTheory.CompanionTheory.ZUnf.Centre

namespace GlobalTheory.CompanionTheory.ZUnf

theorem centre_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 :=
  fun M => ⟨Centre.nzx_add M, Centre.nzx_comm_sh M, Centre.nzx_comm_emb M,
    fun l => ⟨Centre.nzx_mem_GF M l, Centre.nzx_rat_mat M l⟩⟩

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCell
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SmallZ
open GlobalTheory.CompanionTheory.SwUnf.SmallCell

variable {D : D7} {n ρ p : ℕ}

theorem zinc_inl {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin ρ) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl a)) = u a := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = u a
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

theorem zinc_inr {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin p) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr a)) = 0 := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = 0
  rw [Equiv.symm_apply_apply, Sum.elim_inr]

theorem blockMatrix_inl_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem blockMatrix_inl_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin ρ) (j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem blockMatrix_inr_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin p) (j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blockMatrix_inr_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

def rk2 {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) : Mx D m m :=
  τ • ((rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1) ⬝ (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) +
    adj (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) ⬝ adj (rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1))

theorem rank_two_matrix_apply {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) (i j : Fin m) :
    rk2 τ v r i j = τ * (incA D (v i) * incA D (r j) + cA D (incA D (r i)) * cA D (incA D (v j))) := by
  simp only [rk2, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
  rfl

theorem rk_term (τ : AE D) (a b c d : D.host.E) (h1 : a = 0 ∨ b = 0) (h2 : c = 0 ∨ d = 0) :
    τ * (incA D a * incA D b + cA D (incA D c) * cA D (incA D d)) = 0 := by
  have e1 : incA D a * incA D b = 0 := by
    rcases h1 with rfl | rfl
    · rw [map_zero (incA D), zero_mul]
    · rw [map_zero (incA D), mul_zero]
  have e2 : cA D (incA D c) * cA D (incA D d) = 0 := by
    rcases h2 with rfl | rfl
    · rw [map_zero (incA D), map_zero (cA D), zero_mul]
    · rw [map_zero (incA D), map_zero (cA D), mul_zero]
  rw [e1, e2, add_zero, mul_zero]

theorem rank_two_embedding_small (hn : ρ + p = n) (τ : AE D) (v r : Fin ρ → D.host.E) :
    rk2 τ (zinc hn v) (zinc hn r) = bl hn (rk2 τ v r) 0 0 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [blockMatrix_inl_inl, rank_two_matrix_apply, rank_two_matrix_apply, zinc_inl, zinc_inl, zinc_inl, zinc_inl]
  · rw [blockMatrix_inl_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inr (zinc_inr hn r j)) (Or.inr (zinc_inr hn v j))
  · rw [blockMatrix_inr_inl, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))
  · rw [blockMatrix_inr_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))

theorem small : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  intro D n ρ p hn ψ hψ β hβ W hW
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : β.1 *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hβ h)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
  let r : Fin ρ → D.host.E := Pi.single i0 ((β.1 *ᵥ v) i0)⁻¹
  let V0 : Matrix (Fin ρ) (Fin 1) D.host.E := Matrix.replicateCol _ v
  let R0 : Matrix (Fin 1) (Fin ρ) D.host.E := Matrix.replicateRow _ r
  have hbV : β.1 ⬝ V0 = Matrix.replicateCol _ (β.1 *ᵥ v) := by
    ext i j
    simp [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hS0 : R0 ⬝ β.1 ⬝ V0 = (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
    rw [Matrix.mul_assoc, hbV]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [R0, r, Matrix.mul_apply, Pi.single_apply, inv_mul_cancel₀ (show (β.1 *ᵥ v) i0 ≠ 0 from hi0)]
  have hS : (rat R0 : Mx D 1 ρ) ⬝ (rat β.1 : Mx D ρ ρ) ⬝ (rat V0 : Mx D ρ 1) = 1 := by
    rw [← rat_mul, ← rat_mul, hS0]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [rat]
  obtain ⟨x0, hx0⟩ := hψ.2.2.2
  obtain ⟨t, ht⟩ := exists_scalar (D := D) x0
  have hν : adj (rk2 (algebraMap (AF D.host.F) (AE D) t) v r) = rk2 (algebraMap (AF D.host.F) (AE D) t) v r := by
    unfold rk2
    rw [adj_smul, cA_algebraMap', adj_add, adj_mul, adj_mul, adj_adj, adj_adj, add_comm]
  refine ⟨⟨_, hν⟩, ?_, ?_⟩
  · have h := trace_val (rat β.1) (adj_rat_herm β) (rat V0) (rat R0) (algebraMap (AF D.host.F) (AE D) t) hS
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ _))) ≠ 1
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ (algebraMap (AF D.host.F) (AE D) t • _)))) ≠ 1
    rw [h, ht]
    exact hx0
  · intro γ u hγ x hx hW' hu
    refine cell_absorb (rat (Matrix.replicateCol (Fin 1) (zinc hn v))) (rat (Matrix.replicateRow (Fin 1) (zinc hn r)))
      (algebraMap (AF D.host.F) (AE D) t) ((rank_two_embedding_small hn _ v r).symm) γ u hu ?_
    have hv : lowerC x *ᵥ zinc hn v = 0 := by
      rw [← hW'] at hvW
      exact hvW
    have h0 : (HMul.hMul (lowerC x) (Matrix.replicateCol (Fin 1) (zinc hn v)) : Matrix (Fin n) (Fin 1) D.host.E) = 0 := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [hx, lowerC_map]
    change (rat (lowerC x) : Mx D n n) ⬝ (rat (Matrix.replicateCol (Fin 1) (zinc hn v)) : Mx D n 1) = 0
    rw [← rat_mul, h0]
    ext i j
    simp [rat]

end GlobalTheory.CompanionTheory.ZUnf.SmallZ
end
end

