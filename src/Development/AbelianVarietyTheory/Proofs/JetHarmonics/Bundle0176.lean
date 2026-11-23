module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLif
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContractionMapsAtRepresentatives
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePower
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.polyLift_ahat Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.MirrorToda.polyLift_ahatv Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.LiftR.polyLift_rh Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ _root_.GlobalTheory.HatNF.MirrorLift.polyLift_rhv Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacing
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory.PlaceOfLocalBesselType

theorem isType_of_isHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hU : ∀ i : Fin k, U (i.val + 1) = u i) : Q.IsType k r z π U := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', h1, h2, h3, h4, h5, -⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  exact ⟨h1, h2, h3, h4, h5, GlobalTheory.ThA.capParam_of_isHCTypeW k r z u U Wp π hz hT hπ hU⟩

noncomputable def ext {k : ℕ} (u : Fin k → ℝ) (i : ℕ) : ℝ := if h : i - 1 < k then u ⟨i - 1, h⟩ else 0

theorem ext_succ {k : ℕ} (u : Fin k → ℝ) (i : Fin k) : ext u (i.val + 1) = u i := by
  simp [ext]

theorem add_one_le {a b c l : ℝ} (ha : ∃ m : ℤ, a = m + c) (hb : ∃ m : ℤ, b = m + c) (h1 : a < l) (h2 : l < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have h : (m : ℝ) < n := by linarith
  have h' : m + 1 ≤ n := by exact_mod_cast h
  have h'' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
  linarith

end GlobalTheory.PlaceOfLocalBesselType

namespace GlobalTheory

open PlaceOfLocalBesselType

theorem exists_place_of_locBessel : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  intro k r L μsec lam0 hk h2 hsec hI hI'
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.exists_normalised_localBesselDatum k r L μsec hk1 hsec
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of Bs
  have hT := isType_of_isHCTypeW k r L.z L.u (ext L.u) L.Wp L.π L.hz.1 L.hz.2 L.hπ (ext_succ L.u)
  have hT' := isType_of_isHCTypeW k r L.z' L.u' (ext L.u') L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ' (ext_succ L.u')
  have hZ := GlobalTheory.capelliParam_mem_int_add_half k r L.Wp L.z L.π _ L.hz.1 L.hz.2 hT
  have hZ' := GlobalTheory.capelliParam_mem_int_add_half k r L.Wq L.z' L.π' _ L.hz'.1 L.hz'.2 hT'
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk1⟩
  have hOK : (⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ : M.Par).OK := by
    refine ⟨hk1, L.hz.2, L.hz'.2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ' i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      dsimp only at hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < k := by omega
      have m1 : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have m2 : j + 1 + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨a1, a2⟩ := hI.1 j hj
      obtain ⟨b1, b2⟩ := hI'.1 j hj
      rw [← ext_succ L.u] at a1 a2
      rw [← ext_succ L.u'] at b1 b2
      dsimp only at a1 a2 b1 b2
      have c1 := add_one_le (hZ _ m2) (hZ _ m1) a2 a1
      have c2 := add_one_le (hZ _ m2) (hZ' _ m1) a2 b1
      have c3 := add_one_le (hZ' _ m2) (hZ _ m1) b2 a1
      have c4 := add_one_le (hZ' _ m2) (hZ' _ m1) b2 b1
      simp only [M.Par.lo, M.Par.hi]
      rcases max_choice (ext L.u (j + 1 + 1)) (ext L.u' (j + 1 + 1)) with e | e <;>
        rcases min_choice (ext L.u (j + 1)) (ext L.u' (j + 1)) with e' | e' <;> rw [e, e'] <;> linarith
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hBs
  obtain ⟨Cb, hCb⟩ := GlobalTheory.ThA.plExists
  obtain ⟨p, -, hp, -⟩ := hCb L.Wp L.Wq ⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ Bs ν' m₀ 1 le_rfl hk1 h2
    (by rw [e5]; exact L.hμW.2) (by rw [e6]; exact L.hμW'.2) e7 hF
    (by rw [e1, e2, e3, e4]; exact ⟨hOK, L.hz.1, L.hz'.1, rfl, rfl, hT, hT'⟩)
  refine ⟨ext L.u, ext L.u', p, fun i => ⟨ext_succ _ i, ext_succ _ i⟩, ?_⟩
  rw [hp]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVecPol

theorem integrable_inner_of_memLp {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun c => inner ℂ (u c) (v c)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with c h1 h2
  rw [h1, h2]

theorem integral_inner_expand {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (a : ℂ) :
    ∫ c, inner ℂ (u c + a • v c) (u c + a • v c) ∂μ =
      ∫ c, inner ℂ (u c) (u c) ∂μ + a * ∫ c, inner ℂ (u c) (v c) ∂μ +
        (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (u c) ∂μ +
        a * (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (v c) ∂μ := by
  have h1 := integrable_inner_of_memLp hu hu
  have h2 := (integrable_inner_of_memLp hu hv).const_mul a
  have h3 := (integrable_inner_of_memLp hv hu).const_mul ((starRingEnd ℂ) a)
  have h4 := (integrable_inner_of_memLp hv hv).const_mul (a * (starRingEnd ℂ) a)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have h12 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c)) μ := h1.add h2
  have h123 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c) +
      (starRingEnd ℂ) a * inner ℂ (v c) (u c)) μ := h12.add h3
  rw [← integral_add h12 h3, ← integral_add h123 h4]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

theorem beta_eq_integral_inner_tv : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H H' w hD hH hH' hw
  have hS : ∀ (a : ℂ) (x y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base x → KB.CptCoef p.T.base y →
      KB.CptCoef p.T.base (x + a • y) := fun a x y hx hy => Formalism.FourierDecayAlt.P.PBL.cpt_add hx (Formalism.FourierDecayAlt.P.PBL.cpt_smul a hy)
  have hcc : ∀ x : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base x → ∀ (A : ℝ) (m : ℕ), B.InCC A m x := by
    intro x hx
    obtain ⟨ε, -, h⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hx
    exact h.2.1
  refine GlobalTheory.polarisation_on_subspace (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (KB.CptCoef p.T.base)
    (fun x y => B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) x w) y)
    (fun x y => ∫ c, inner ℂ (tv p y w c) (tv p x w c)) hS ?_ ?_ ?_ H H' hH hH'
  · intro a x y hx hy
    have hs := _root_.GlobalTheory.beta_foldCapelli_sesquilinear P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w (B.AB P.k P.r) le_rfl a
    have hz := hS a x y hx hy
    have e1 := (hs x y (x + a • y) x hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc _ hz _ _) (hcc x hx _ _)).1
    have e2 := (hs x y x y hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    have e3 := (hs y y x y hy.1 hy.1 (hcc y hy _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    beta_reduce
    rw [e1, e2, e3]
    ring
  · intro a x y hx hy
    have hx2 := (_root_.GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt hP Wp Wq P p Cb x w hD hx hw).1
    have hy2 := (_root_.GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt hP Wp Wq P p Cb y w hD hy hw).1
    have e : ∀ c, tv p (x + a • y) w c = tv p x w c + a • tv p y w c := fun c =>
      GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb a x y w c hD hw hx hy
    beta_reduce
    simp only [e]
    exact integral_inner_expand hx2 hy2 a
  · intro x hx
    beta_reduce
    rw [(_root_.GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt hP Wp Wq P p Cb x w hD hx hw).2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    simp

end GlobalTheory.TopVecPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TvApproxTendstoL2Cutoff
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem tv_approx_tendsto_L2 : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (∀ n : ℕ, MemLp (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w) 2 volume) ∧ MemLp (tv p (D.cutF p.T.base χ f ε) w) 2 volume ∧ Tendsto (fun n : ℕ => eLpNorm (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w - tv p (D.cutF p.T.base χ f ε) w) 2 volume) atTop (𝓝 0) := by
  intro hP Cb
  obtain ⟨C₁, h₁⟩ := _root_.GlobalTheory.LevelZeroApprox.beta_approx
  obtain ⟨C₂, h₂⟩ := _root_.GlobalTheory.TopVec.tv_approx_tendsto Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hCb hχ hf hA hthr hw hlen ε hε
  have hpos : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC
    refine le_trans ?_ hthr
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC hpos
  obtain ⟨-, K, hK⟩ := h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hA (hmono _ (le_max_left _ _)) hlen
    ε ε hε hε
  have hpt := h₂ Wp Wq P p f χ A N w hCb hχ hf hA (hmono _ (le_max_right _ _)) hw hlen ε hε
  have hcpt := Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P p.T.base hχ hf hε
  have hL : ∀ n : ℕ, MemLp (tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) 2 volume := fun n =>
    (_root_.GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt hP Wp Wq P p Cb _ w hCb (hcpt n) hw).1
  refine ⟨hL, ?_⟩
  refine GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto _ volume _
    (fun n => tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) _ K hL (Eventually.of_forall hpt) ?_
  intro n m hnm
  have hsub : KB.CptCoef p.T.base
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) :=
    Formalism.FourierDecayAlt.P.PBN.cpt_sub p.T.base (hcpt n) (hcpt m)
  have hlin : ∀ c, tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w c -
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c =
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c := by
    intro c
    have h := _root_.GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb (-1) _ _ w c hCb hw (hcpt n) (hcpt m)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    exact h.symm
  have hβ := (_root_.GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt hP Wp Wq P p Cb _ w hCb hsub hw).2
  have hb : ‖B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m)‖ ≤
      K / ((n : ℝ) + 1) := hK n m hnm
  rw [hβ, Complex.norm_real] at hb
  simp only [hlin]
  exact (le_abs_self _).trans hb

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.WigSh

theorem par_gap_right (P : M.Par) (hP : P.OK) :
    ∀ i ∈ Finset.Icc 1 (P.k - 1), ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨a, ha⟩ := hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  obtain ⟨c, hc⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hg := hP.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  have h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (1 : ℤ) ≤ a - c := by exact_mod_cast h3
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ) := ⟨(a - c - 1).toNat, by omega⟩
  refine ⟨N, ?_⟩
  have h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ) := by rw [hN]
  push_cast at h5
  linarith

theorem amapsShExists : GlobalTheory.WigSh.AmapsShExists := by
  obtain ⟨c₃, hc⟩ := GlobalTheory.WigSh.contraction_maps_at_representatives
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ
    hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum
  have h0 := p.hT 0 (Nat.zero_le _)
  have h1 := pp.hT 0 (Nat.zero_le _)
  have h2 := pm.hT 0 (Nat.zero_le _)
  have hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up' := hpz' ▸ pp.hP.2.2.2.2.2.2
  have hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um' := hmz' ▸ pm.hP.2.2.2.2.2.2
  have hμp : pp.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1
      (h1.2.2.trans h0.2.2.symm)
  have hμm : pm.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1
      (h2.2.2.trans h0.2.2.symm)
  obtain ⟨Ap', Am', hAp, hAm, hlow⟩ := GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z'
    p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos
    p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩ :=
    hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm
      p.hF hAp hAm hlow
  refine ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩
  intro A₀ f hA₀ hf
  obtain ⟨hfp, hfm⟩ := hfac A₀ f hA₀ hf
  refine ⟨?_, ?_, he, hbp, hbm⟩
  · intro γ hγ hG
    have h := hfp γ hγ hG
    unfold KB.Pl.V
    rw [hpν, hpm]
    exact h
  · intro γ hγ hG
    have h := hfm γ hγ hG
    unfold KB.Pl.V
    rw [hmν, hmm]
    exact h

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficients
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

theorem tendsto_list_map_sum_real {α : Type*} (l : List α) (u : α → ℕ → ℝ) (v : α → ℝ)
    (h : ∀ x ∈ l, Tendsto (u x) atTop (𝓝 (v x))) :
    Tendsto (fun n => (l.map fun x => u x n).sum) atTop (𝓝 (l.map v).sum) :=
  tendsto_list_sum l h

theorem wordBound_decay : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  intro a ha Cb
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.HatNF.vecV_cut_polyOp
  obtain ⟨c₂, hc₂⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_op
  refine ⟨5 * max Cb 8 + max Cb 8 ^ 2 + 1 + |max c₁ c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p N w hDD hw hwN
  obtain ⟨C, J, Θs, hC, hpoly, hB⟩ := _root_.GlobalTheory.HatNF.wordBound_cptCoef a ha Wp Wq P0 p w hw
  refine ⟨C, J, Θs, hC, hpoly, ?_⟩
  rintro φ f ⟨e₀, A, hφ, hf, hfA, hA⟩ e c hc hG
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb8 : (8 : ℝ) ≤ max Cb 8 := le_max_right _ _
  have hCb0 : (0 : ℝ) ≤ max Cb 8 := by linarith
  have hwN' : (w.length : ℝ) ≤ N := by exact_mod_cast hwN
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (2 * (P0.r : ℝ) + 2) * e₀ := by positivity
  have hcut' : ∀ n g, Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    simp [Formalism.FourierDecayAlt.P.CutBP.cutN, Formalism.FourierDecayAlt.P.JCx2.pdPsi, Formalism.FourierDecayAlt.P.JCx2.pdPhi, Formalism.FourierDecayAlt.P.JCx2.pdChi,
      Formalism.FourierDecayAlt.P.JCx2.pdSq]
  have hmono : ∀ c : ℝ, c ≤ max c₁ c₂ → ∀ B' : ℝ,
      max c₁ c₂ * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) + 1) ≤ B' →
      c * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) + 1) ≤ B' := by
    intro c hc B' hB
    rw [hXn]
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  obtain ⟨δ₀, hδ₀, hφ0⟩ := hφ.2.1
  set γ := TBB.bigPt P0.r c with hγ
  set δ : ℝ := min δ₀ (TBB.Gp p γ / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ < TBB.Gp p γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := ⟨_, Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation⟩
  have hmul : ∀ n, mulG p.T.base φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n) =
      fun g => Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g • mulG p.T.base φ f g := by
    intro n
    funext g
    simp only [mulG, Formalism.FourierDecayAlt.P.CutBP.apx, D.cutF]
    by_cases hg : Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀
    · simp [hφ0 _ hg]
    · rw [hχ.2.2 _ ((one_le_div hδ).2 (hδ1.trans (not_lt.1 hg)))]
      simp only [Complex.ofReal_one, one_smul]
      exact smul_comm _ _ _
  have hn := fun n => hB φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)
    ⟨hφ.1, Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P0 p.T.base hχ hf hδ n⟩ e c hc hG
  simp only [hmul] at hn
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ hn
  · refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
    have hcongr : ∀ G, p.V (p.Θ.Θ w e G) γ = D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) γ :=
      fun G => Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ γ
        (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    rw [hcongr]
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
        _ ≤ max Cb 8 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
          rw [hXn]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
            (by linarith)
        _ ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwN' hCb0) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o :=
      hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Nat.cast_nonneg _))
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    obtain ⟨hck, bF, hbF⟩ := GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P0 p.T.base e₀ o φ f A hφ hf (hfA o)
    have hv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀ → mulG p.T.base φ f g = 0 := by
      intro g hg
      simp [mulG, hφ0 _ hg]
    have hth := hmono c₂ (le_max_right _ _)
      (A - (2 * (P0.r : ℝ) + 2) * ((e₀ : ℝ) + o) - 1 - ((κ : ℝ) + 3 * ((P0.r : ℝ) + 1) * o)) (by linarith [hthr])
    have key := hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ γ (mulG p.T.base φ f) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r)
      nf fib o κ Dop δ₀ _ bF hfib hIn hδ₀ hv hck hbF hcut' hth
    exact key.congr fun n => (hcongr _).symm
  · refine Tendsto.const_mul _ (tendsto_list_map_sum_real Θs
      (fun Θ n => ‖B.hsVec (p.V (B.opApply Θ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)) γ)‖)
      (fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) γ)‖) fun Θ hΘ => ?_)
    refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    rw [← GlobalTheory.HatNF.vec_opApply_cutF_eq Wp Wq P0 p Θ f χ δ γ hχ hδ hδ2]
    set o : ℕ := w.length * (2 * P0.r + P0.k + 1) with ho
    set κ : ℕ := w.length * (8 * (P0.r + 1) * (2 * P0.r + P0.k + 1)) with hκ
    have hoR : (o : ℝ) = w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by rw [ho]; push_cast; ring
    have hκR : (κ : ℝ) = 8 * ((P0.r : ℝ) + 1) * o := by rw [hoR, hκ]; push_cast; ring
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      rw [hoR]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o := by
      rw [hκR]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb8 (by linarith)) (Nat.cast_nonneg _)
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    have h3 : (0 : ℝ) ≤ 3 * ((P0.r : ℝ) + 1) * o := by positivity
    exact hc₁ Wp Wq P0 p o κ Θ (D.cutF p.T.base χ f δ) (A - 2 * ((P0.r : ℝ) + 1) * o) (hpoly Θ hΘ)
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf δ)
      (Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hfA hδ _ o (by linarith))
      (hmono c₁ (le_max_left _ _) _ (by linarith [hthr])) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r) (fun _ _ => rfl) γ

end GlobalTheory.HatNF
end

