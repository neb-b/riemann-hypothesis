module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0759
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowersDiagonalAtTBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0748
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaGLMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
section
namespace GlobalTheory.CompanionTheory.LeviMatchingWords

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := GlobalTheory.CompanionTheory.MatchWordS.matchLMWordSOf

end GlobalTheory.CompanionTheory.LeviMatchingWords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MT PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RegPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open GlobalTheory.CompanionTheory.MatchPow in
theorem hasVals_nrm (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a : ℕ}
    {y : Fin a → ℤ} (hy : StrictAnti y) {δ : GLw a w} (hδ : dcos a w (tdiag ϖ y) δ ≠ 0) :
    HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨m, -, τ, hτ, e⟩ := GlobalTheory.CompanionTheory.ThetaContraction.contr_tw hU w hw ϖ hϖ a y hy δ hδ
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.CompanionTheory.TwSide.exists_diagT_of_mem_TO hτ
  have hdu : m⁻¹ * δ * thL a w m = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) fun i => ϖ ^ y i * v i := by
    rw [e, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (((ϖ ^ y i * v i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y i := by
    intro i
    simp only [Units.val_mul]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ.1,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  rw [← GlobalTheory.CompanionTheory.MatchLinear.charpoly_nrmL_twConj hU a w δ m, hdu, GlobalTheory.CompanionTheory.TwSide.nrmL_diagT hw, GlobalTheory.SmGL.val_diagT,
    Matrix.charpoly_diagonal]
  exact ⟨fun i => _, rfl, fun i => ⟨Units.ne_zero _, GlobalTheory.CompanionTheory.TwSide.ordL_norm_entry hU _ y hord i⟩⟩


open GlobalTheory.CompanionTheory.MatchPow in
theorem mpow_entT {w : Pl E} {n : ℕ} (a : ℕ) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, fun s => ?_⟩
    funext y
    have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
      (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
    rw [pow_zero, one_mul]
    exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e, mconv_entT GlobalTheory.CompanionTheory.DcosProduct.dcosMul n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem regPowT : RegPowT := by
  intro E _ _ _ hU n d _ hm a ha m w hT y hy
  obtain ⟨hw, -, hϖ, hc⟩ := hm.T w hT
  rw [GlobalTheory.CompanionTheory.MatchLMB2.trace_test_function_eq d ha hT m] at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨J', _, c', x', hx', e⟩ := mpow_entT a hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w)
    (fun j => hc j.1 j.2) m
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.qT_eq d s, GlobalTheory.CompanionTheory.MatchLMPlaces.mpow_scale, e s] at hs
  have h1 : entT n w (d.ϖ w) a c' x' s y ≠ 0 := fun h => hs (by simp [h])
  by_cases hA : MT.admitted n a s
  swap
  · exact absurd (dif_neg hA) h1
  unfold entT at h1
  rw [dite_eq_left hA] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hd2 : dcos (n - a) w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.2)) y.2 ≠ 0 := right_ne_zero_of_mul hj
  have hd1 : dcos a w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.1)) y.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hj)
  obtain ⟨u₁, hQ₁, hu₁⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.1) hd1
  obtain ⟨u₂, hQ₂, hu₂⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.2) hd2
  rw [hQ₁, hQ₂]
  exact GlobalTheory.CompanionTheory.SymmetricIndexRegularity.localization_quotient_separated_dvd (fun z => ordL z) (hx' j).1 _ _ hA.2.2.2.1 hA.2.2.2.2 (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ s)
    (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ sᶜ) (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_disj n _ _ s (by have := hA.2.2.1; omega)) u₁ u₂
    (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.RegPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ScalWall

open PositivityTheory.RgEis ResidueKilled.Tr GlobalTheory.CompanionTheory.SiegelFrame

theorem pos_eq_norm_cosetSum {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (l : G' → ℝ) (hc : Conv Γ' P' l)
    (hl : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, l (γ * y) = l y) (g : G) :
    pos Γ' P' l (Φ g) = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (l (Φ x)) : ℂ)) g‖ := by
  have hs : HasSum (fun q : PositivityTheory.RgEis.Cos P' Γ' => Real.exp (l (PositivityTheory.RgEis.rep q * Φ g)))
      (PositivityTheory.RgEis.pos Γ' P' l (Φ g)) := (hc (Φ g)).hasSum
  have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ Γ P Γ' P' hΓ hP (fun y => Real.exp (l y))
    (fun γ hγ hγP y => by simp only [hl γ hγ hγP y]) (Φ g) _ hs
  have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ => ((Real.exp (l (Φ (PositivityTheory.RgEis.rep q * g))) : ℝ) : ℂ))
      ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (by simpa only [map_mul] using h2)
  have h4 : GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (l (Φ x)) : ℝ) : ℂ)) g
      = ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) := h3.tsum_eq
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (hs.nonneg fun _ => (Real.exp_pos _).le)]

theorem fin_along {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (K' : Subgroup G') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))) := by
  have e : (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))
      = (LinearMap.funLeft ℂ ℂ (⇑Φ.symm)) '' (Set.range fun k : K' => fun x => f (x * Φ.symm k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k y
    simp [LinearMap.funLeft_apply, map_mul]
  rw [e, ← Submodule.map_span]
  exact Module.Finite.map _ _

theorem tScal : TScal := by
  unfold ResidueKilled.Tr.TScal ResidueKilled.Tr.Scal
  intro hSec hWL G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η N hK hPar hHt hΓ hP hW f hf hlaw hfin
  have hcrat : ∀ γ ∈ Γ', γ ∈ P' → c γ = 1 := by
    obtain ⟨_, _, ⟨_, _, h, _⟩⟩ := hPar
    exact h
  have hηl : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g := by
    obtain ⟨h, _, _, _⟩ := hHt
    exact h
  have hηr : ∀ γ ∈ Γ', γ ∈ P' → η γ = 0 := by
    obtain ⟨_, _, h, _⟩ := hHt
    exact h
  have hβ : PositivityTheory.RgEis.IsHt Γ' K' P' (fun g => N * η g) := by
    obtain ⟨h1, h2, h3, h4⟩ := hHt
    exact ⟨fun p hp g => by simp only [h1 p hp g, mul_add], fun g k hk => by simp only [h2 g k hk],
      fun γ hγ hγP => by simp only [h3 γ hγ hγP, mul_zero], continuous_const.mul h4⟩
  have hlaw' : ∀ p ∈ P', ∀ x : G', (fun y => f (Φ.symm y)) (p * x)
      = c p * Complex.exp (0 * ↑(η p)) * (fun y => f (Φ.symm y)) x := by
    intro p hp x
    have hp' : Φ.symm p ∈ P := (hP (Φ.symm p)).mpr (by simpa using hp)
    simp only [map_mul, zero_mul, Complex.exp_zero, mul_one]
    rw [hlaw _ hp']
    simp
  have hfin' := fin_along Φ.toMulEquiv K' f hfin
  obtain ⟨R, D, H, hD, hDz, hHd, hHc, hconv1, hconv2, hbd, hsum⟩ :=
    GlobalTheory.CompanionTheory.SiegelFrame.scalar_wall hSec hWL Γ' K' P' c η (fun g => N * η g) hK hPar hHt hβ hW
      (fun y => f (Φ.symm y)) 0 (hf.comp (map_continuous Φ.symm)) hlaw' hfin'
  refine ⟨D, fun z g => H z (Φ g), R, hD, hDz, fun g => hHd (Φ g), ?_, ?_, ?_⟩
  · exact hHc.comp (continuous_fst.prodMk ((map_continuous Φ).comp continuous_snd))
  · intro z hz g
    show H z (Φ g) = _
    have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ.toMulEquiv Γ P Γ' P' hΓ hP
      (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
      (fun γ hγ hγP y => by
        have hγ' : Φ.symm γ ∈ P := (hP (Φ.symm γ)).mpr (by simpa using hγP)
        simp only [hηl γ hγP y, hηr γ hγ hγP, zero_add, map_mul]
        rw [hlaw _ hγ']
        simp [hcrat γ hγ hγP])
      (Φ g) _ (hsum z hz (Φ g))
    have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ =>
        D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g))) (H z (Φ g)) := by
      have e : (fun q : PositivityTheory.RgEis.Cos P Γ =>
          D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g)))
          = fun q => (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
              (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g) := by
        funext q
        have hm : Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g = Φ (PositivityTheory.RgEis.rep q * g) :=
          (map_mul Φ _ _).symm
        show _ = D z * (Complex.exp ((z - 0) * ↑(η (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
          * f (Φ.symm (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
        rw [hm, sub_zero, ContinuousMulEquiv.symm_apply_apply]
      rw [e]
      exact h2
    rw [← h3.tsum_eq, tsum_mul_left]
    rfl
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨M, fun z hz1 hz2 g => ?_⟩
    have hl2 : (fun x : G' => N * η x - b * η x) = fun x => (N - b) * η x := by
      funext x
      ring
    have hinv : ∀ (t : ℝ), ∀ γ ∈ Γ', γ ∈ P' → ∀ y, t * η (γ * y) = t * η y := by
      intro t γ hγ hγP y
      rw [hηl γ hγP y, hηr γ hγ hγP, zero_add]
    have e1 : PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (a * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => a * η x) (hconv1 a ha)
      (fun γ hγ hγP y => hinv a γ hγ hγP y) g
    have hc2 : PositivityTheory.RgEis.Conv Γ' P' (fun x => (N - b) * η x) := by
      rw [← hl2]
      exact hconv2 b hb
    have e2 : PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp ((N - b) * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => (N - b) * η x) hc2
      (fun γ hγ hγP y => hinv (N - b) γ hγ hγP y) g
    have key := hM z hz1 hz2 (Φ g)
    have e3 : PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)
        = PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g) := by
      rw [hl2]
    calc ‖H z (Φ g)‖ ≤ M * (PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
          + PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)) := key
      _ = _ := by
        rw [e3, e1, e2]
        try rfl

end GlobalTheory.CompanionTheory.ScalWall

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent
section
noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

end Blocks

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
end

