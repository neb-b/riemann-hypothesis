module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGLStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_absDetPow_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  first | exact @GlobalTheory.TwistSph.isSpherical_twist_absPow | exact GlobalTheory.TwistSph.isSpherical_twist_absPow | (intros; apply GlobalTheory.TwistSph.isSpherical_twist_absPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalising
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lattice_count_diag_mul : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D κ _ _ m n T S hST L hL
  obtain ⟨M, hM0, hM⟩ := _root_.GlobalTheory.denom_bound_mul D.host.E κ (Fin m) T
  obtain ⟨N, C₁, hC₁, hcount⟩ := _root_.GlobalTheory.WeightedCount.weighted_count D (κ × Fin n) (M * L) (Nat.mul_pos hM0 hL)
  obtain ⟨C₂, hC₂, hnorm⟩ := _root_.GlobalTheory.tGnorm D κ m n T
  refine ⟨N, C₂ ^ N * C₁, mul_nonneg (pow_nonneg (by linarith) _) hC₁, ?_⟩
  intro s hs B hB
  set e : Matrix (Fin m) (Fin n) D.host.E → (κ × Fin n → D.host.E) := fun ξ p => (T * ξ) p.1 p.2 with he
  have he_inj : Function.Injective e := by
    intro ξ ξ' h
    have h' : T * ξ = T * ξ' := Matrix.ext fun k j => congrFun h (k, j)
    calc ξ = S * T * ξ := by rw [hST, Matrix.one_mul]
      _ = S * T * ξ' := by rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc]
      _ = ξ' := by rw [hST, Matrix.one_mul]
  set s' : κ × Fin n → ℝ := fun p => s p.1 with hs'
  have hs'pos : ∀ p, 0 < s' p := fun p => hs p.1
  have hc := hcount s' hs'pos
  set G : (κ × Fin n → D.host.E) → ℝ≥0∞ := {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s' k) ^ N)⁻¹)) with hG
  have hterm : ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C₂ ^ N) * G (e ξ) := by
    intro ξ
    by_cases hξ : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)
    · rw [Set.indicator_of_mem (by exact hξ : ξ ∈ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      have hmem : e ξ ∈ {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)} := by
        intro p
        have := hM L (fun i => ξ i p.2) (fun i => hξ i p.2) p.1
        simpa [he, Matrix.mul_apply] using this
      rw [hG, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
      apply ENNReal.ofReal_le_ofReal
      have hA := hnorm s hs B hB ξ
      set W := ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ with hW
      set A := ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 with hAdef
      have hW0 : 0 ≤ W := by positivity
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun p _ => div_nonneg (by positivity) (hs p.1).le)
      have h1 : 1 + A ≤ C₂ * (1 + W) := by nlinarith
      have hp1 : 0 < (1 + A) ^ N := by positivity
      have hp2 : 0 < (1 + W) ^ N := by positivity
      have h2 : (1 + A) ^ N ≤ C₂ ^ N * (1 + W) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 N
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]
      linarith
    · rw [Set.indicator_of_notMem (by exact hξ : ξ ∉ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      exact bot_le
  calc _ ≤ ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ENNReal.ofReal (C₂ ^ N) * G (e ξ) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₂ ^ N) * ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, G (e ξ) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ∑' η, G η := by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective he_inj G
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ENNReal.ofReal (C₁ * ∏ p, max 1 (s' p) ^ Module.finrank ℚ D.host.E) := by gcongr
    _ = ENNReal.ofReal (C₂ ^ N * C₁ * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), mul_assoc]
      congr 2
      rw [Fintype.prod_prod_type]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp only [hs', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield D]
      ring_nf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqIntegralCoords
section
namespace GlobalTheory.LatticeIntegralCoordinates

theorem exists_basis_of_lattice (O E V : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V]
    [IsScalarTower O E V] (L : Submodule O V) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
      ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap O E).range := by
  classical
  haveI : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c v h
    rw [← algebraMap_smul E c v] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective O E) (by simpa using h)
    · right; exact h
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O L := inferInstance
  let bL := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (bL i : V)
  have hli : LinearIndependent O v :=
    bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent E v := hli.localization E (nonZeroDivisors O)
  have hL : Submodule.span O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_top, Submodule.range_subtype]
  have htop : ⊤ ≤ Submodule.span E (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    exact Submodule.span_subset_span O E _ (hL.ge hx)
  let b0 := Module.Basis.mk hliE htop
  have hb0 : ∀ j, b0 j = v j := fun j => Module.Basis.mk_apply hliE htop j
  have hcard := Module.finrank_eq_card_basis b0
  let e := Fintype.equivFinOfCardEq hcard.symm
  refine ⟨b0.reindex e, fun y => ⟨fun hy i => ?_, fun hy => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hL.ge hy)
    have h1 : ∑ j, c j • v j = ∑ j, algebraMap O E (c j) • b0 j :=
      Finset.sum_congr rfl fun j _ => by rw [hb0, algebraMap_smul]
    rw [Module.Basis.repr_reindex_apply, h1, b0.repr_sum_self]
    exact ⟨_, rfl⟩
  · rw [← b0.sum_repr y]
    refine L.sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := hy (e j)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at hc
    rw [← hc, algebraMap_smul, hb0]
    exact L.smul_mem c (bL j).2

theorem lattice_eq_integral_coords :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
      [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (L : Submodule K.O V),
      L.FG → Submodule.span K.E (L : Set V) = ⊤ →
      ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V,
        ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap K.O K.E).range :=
  fun K V _ _ _ _ _ L hfg hspan => exists_basis_of_lattice K.O K.E V L hfg hspan

end GlobalTheory.LatticeIntegralCoordinates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CM.LieMetricConj

variable {K : Type} [Field K]

theorem form_conj_of_single {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ)
    (e : ∀ i j, h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)))
    (a b : Fin g → K) : h.form ((starRingEnd ℂ).comp s) a b = starRingEnd ℂ (h.form s a b) := by
  have key : ∀ t : K →+* ℂ, h.form t a b =
      ∑ j, t (b j) * starRingEnd ℂ (∑ i, t (a i) * h.form t (Pi.single j 1) (Pi.single i 1)) := by
    intro t
    rw [LieMetric.form_sum_right h t a b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm t (Pi.single j 1) a, LieMetric.form_sum_right h t (Pi.single j 1) a]
  rw [key ((starRingEnd ℂ).comp s), key s]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, RingHom.comp_apply, e, Complex.conj_conj]

end GlobalTheory.CM.LieMetricConj

namespace GlobalTheory.CM.LieMetricConj

open GlobalTheory.ConjUnif

variable {K : Type} [Field K] [NumberField K]

theorem conj_conj_comp (s : K →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
  RingHom.ext fun x => by simp

theorem single_conj (hU : ThetaUnifAV) {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K))
    (H : F.IsHerm h) (s : K →+* ℂ) (i j : Fin F.P₀.g) :
    h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H ((starRingEnd ℂ).comp s)
  obtain ⟨A'', _, ψc, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψc : A''.left ⟶ Q'.A.left),
      IsGrpPullback A'' Q'.A cj ψc :=
    ⟨_, _, _, isGrpPullback_pullback Q'.A cj⟩
  let Q'' : Out.PolAV (Sp ℂ) := pullPol Q' hc
  have hQ : IsPolFibre (starRingEnd ℂ) Q' Q'' ψc := ⟨rfl, hc, ⟨idIso _, idIso_isGen (pull_isLB Q'.isLB ψc)⟩⟩
  have a'' : IsPolFibre s F.P₀ Q'' (ψc ≫ ψ') := by
    rw [← conj_conj_comp s]
    exact PolFibre.comp a' hQ
  choose v'' hv'' using fun k => (existsUnique_isVecOver hc.1 (v' k)).exists
  have ht : ∀ k, IsTangent (v' k) := fun k => (c' k).1.isTangent a'.2.1 (F.basis.1 k)
  have c'' : ∀ k, IsVecOver s (ψc ≫ ψ') (F.v k) (v'' k) ∧ (conjPull hc u').IsDiff (star (W' k)) (v'' k) := by
    intro k
    refine ⟨?_, cj_isDiff hc (pullId u') (ht k) (hv'' k) (c' k).2⟩
    rw [← conj_conj_comp s]
    exact (PolFibre.vec_iff a'.2.1.1 hc.1.w (c' k).1).1 (hv'' k)
  have e := LieMetric.hermForm_eq hU a a'' b (conjPull_isAH hc u' b') F.basis.1 c c'' j i
  rw [d, d', e]
  unfold hermForm
  rw [map_mul, Complex.conj_ofReal, star_star]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

theorem form_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K)))
    (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ)
    (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) :=
  fun _ _ _ _ F h H σ a b => form_conj_of_single h σ (single_conj thetaUnifAV_all F h H σ) a b

end GlobalTheory.CM.LieMetricConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfFiltrationSymbolDetNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem linearIndependent_of_symbol_det_ne_zero :
    ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → (∀ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0) → LinearIndependent E (fun k : J => v k) → LinearIndependent E fun k : {k // k ∈ Set.range ix ∨ k ∈ J} => v k := by
  classical
  intro E A' _ _ _ r d I _ _ U sym hmono hker ix J v hv hJ hdet hJli
  have hle : ∀ b c : ℕ, b ≤ c → c ≤ r → U c ≤ U b := by
    intro b c hbc hcr
    induction c, hbc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hbc ih => exact (hmono c (by omega)).trans (ih (by omega))
  let h : (Σ a, I a) ⊕ J → Fin d := Sum.elim ix (fun k => k.1)
  have hinj : Function.Injective h := by
    rintro (q|k) (q'|k') heq
    · exact congrArg Sum.inl (ix.injective heq)
    · exact ((hJ _ k'.2).1 ⟨q, heq⟩).elim
    · exact ((hJ _ k.2).1 ⟨q', heq.symm⟩).elim
    · exact congrArg Sum.inr (Subtype.ext heq)
  let e : (Σ a, I a) ⊕ J → {k // k ∈ Set.range ix ∨ k ∈ J} := fun x =>
    ⟨h x, by rcases x with q | k; exacts [Or.inl ⟨q, rfl⟩, Or.inr k.2]⟩
  have hb : Function.Bijective e := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨k, hk | hk⟩
    · obtain ⟨q, rfl⟩ := hk
      exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have key : LinearIndependent E (fun x : (Σ a, I a) ⊕ J => v (h x)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ q, g (Sum.inl q) • v (ix q)) + ∑ k : J, g (Sum.inr k) • v k = 0 := by
      rw [Fintype.sum_sum_type] at hg; exact hg
    have hA : ∀ n, ∀ a : Fin r, (a : ℕ) = n → ∀ i, g (Sum.inl ⟨a, i⟩) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro a ha i
      subst ha
      obtain ⟨G, hG⟩ := LinearMap.exists_extend (sym a)
      have hGv : ∀ x (hx : x ∈ U a), G x = sym a ⟨x, hx⟩ := fun x hx =>
        LinearMap.congr_fun hG ⟨x, hx⟩
      have hker' : ∀ x ∈ U ((a : ℕ) + 1), G x = 0 := fun x hx => by
        rw [hGv x (hmono a a.isLt hx)]
        exact (hker a ⟨x, _⟩).mpr hx
      have hJ0 : ∑ k : J, g (Sum.inr k) • G (v k) = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [hker' _ (hle ((a : ℕ) + 1) r (by have := a.isLt; omega) le_rfl (hJ k.1 k.2).2), smul_zero]
      have hS : ∑ q : (Σ b, I b), g (Sum.inl q) • G (v (ix q))
          = ∑ i : I a, g (Sum.inl ⟨a, i⟩) • sym a ⟨v (ix ⟨a, i⟩), hv ⟨a, i⟩⟩ := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single a]
        · exact Finset.sum_congr rfl fun i _ => by rw [hGv]
        · intro b _ hba
          apply Finset.sum_eq_zero
          intro i _
          rcases lt_or_gt_of_ne hba with hlt | hlt
          · rw [ih b (Fin.lt_iff_val_lt_val.mp hlt) b rfl i, zero_smul]
          · have h1 := Fin.lt_iff_val_lt_val.mp hlt
            have h2 := b.isLt
            rw [hker' _ (hle ((a : ℕ) + 1) (b : ℕ) (by omega) (by omega) (hv ⟨b, i⟩)), smul_zero]
        · intro hn; exact absurd (Finset.mem_univ a) hn
      have hGg := congrArg G hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, map_zero] at hGg
      rw [hS, hJ0, add_zero] at hGg
      have hM : Matrix.mulVec (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i)
          (fun i' => g (Sum.inl ⟨a, i'⟩)) = 0 := by
        funext j
        have hj := congrFun hGg j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [← hj]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet a) hM) i
    have hJs : ∑ k : J, g (Sum.inr k) • v k = 0 := by
      have h0 : ∑ q : (Σ a, I a), g (Sum.inl q) • v (ix q) = 0 :=
        Finset.sum_eq_zero fun ⟨b, i⟩ _ => by rw [hA _ b rfl i, zero_smul]
      rw [h0, zero_add] at hg'; exact hg'
    rintro (⟨b, i⟩ | k)
    · exact hA _ b rfl i
    · exact Fintype.linearIndependent_iff.mp hJli (fun k => g (Sum.inr k)) hJs k
  refine (linearIndependent_equiv (Equiv.ofBijective e hb)).mp ?_
  exact key

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogEvalSubLeBlockSphereMeanMultidegree
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.LelongBlocksMulti

theorem log_eval_sub_le_blockSphereMean : ∀ (B N : ℕ) (a : Fin B → ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ), A.det ≠ 0 → IsMultiHomogeneous a h → ∀ p : Fin B × Fin N → ℂ, (∀ i, frameNorm A (fun j => p (i, j)) = 1) → eval p h ≠ 0 → Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2 ≤ blockSphereMean B N (linSubst A h) := by
  intro B N a A h hA hh p hp hne
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos B with rfl | hB
    · have hev : ∀ z : BlockSphere 0 0, eval (blockPoint z) (linSubst A h) = eval p h := by
        intro z
        rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
        refine congrArg (fun v => eval v h) (funext fun x => ?_)
        exact x.2.elim0
      have hc : (fun z : BlockSphere 0 0 => Real.log ‖eval (blockPoint z) (linSubst A h)‖) =
          fun _ => Real.log ‖eval p h‖ := funext fun z => by rw [hev z]
      unfold blockSphereMean blockSphereProb
      rw [hc, MeasureTheory.Measure.pi_of_empty _ (fun i => i.elim0)]
      simp
    · have := hp ⟨0, hB⟩
      simp [frameNorm] at this
  · let q : Fin B → Fin N → ℂ := fun i => A⁻¹.mulVec (fun j => p (i, j))
    have hq : ∀ i, ‖(WithLp.toLp 2 (q i) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
      intro i
      rw [EuclideanSpace.norm_eq]
      exact hp i
    let u : BlockSphere B N := fun i =>
      ⟨WithLp.toLp 2 (q i), mem_sphere_zero_iff_norm.mpr (hq i)⟩
    have hev : eval (blockPoint u) (linSubst A h) = eval p h := by
      rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
      refine congrArg (fun v => eval v h) (funext fun x => ?_)
      obtain ⟨b, j⟩ := x
      have h1 : A.mulVec (q b) = fun j => p (b, j) := by
        simp only [q]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]
      exact congrFun h1 j
    have key := blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hN B
      a (linSubst A h) u (GlobalTheory.HeightUnique.linSubst_homog A hh) (by rw [hev]; exact hne)
    rw [hev] at key
    calc Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2
        = Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) / 2 * (harmonic (N - 1) : ℝ) := by ring
      _ ≤ _ := by push_cast at key ⊢; exact key

end GlobalTheory.LelongBlocksMulti
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def ktype (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W}
  zero_mem' g := by
    have e : (fun k : Kinf E a => (cptRep E a k 0).1 g) = 0 := by funext k; simp
    rw [e]; exact W.zero_mem
  add_mem' {ψ ψ'} h h' g := by
    have e : (fun k : Kinf E a => (cptRep E a k (ψ + ψ')).1 g) =
        (fun k : Kinf E a => (cptRep E a k ψ).1 g) + fun k : Kinf E a => (cptRep E a k ψ').1 g := by
      funext k; simp
    rw [e]
    exact W.add_mem (h g) (h' g)
  smul_mem' c ψ h g := by
    have e : (fun k : Kinf E a => (cptRep E a k (c • ψ)).1 g) = c • fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; simp
    rw [e]
    exact W.smul_mem c (h g)


variable (E a) in
def killed (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  ⨅ τ, ⨅ u, LinearMap.ker (Polynomial.aeval (cap τ u) (q τ u))


variable (E a) in
def space (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ))
    (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  leftInv E a ⊓ fixL E a L ⊓ ktype E a W ⊓ killed E a q ⊓ tame E a

theorem mem_killed {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ killed E a q ↔ ∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0 := by
  simp [killed, Submodule.mem_iInf]

theorem mem_space {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ space E a L W q ↔ (∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g) ∧ (∀ k ∈ L, finRep E a k ψ = ψ) ∧
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W) ∧
      (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) ∧ ψ ∈ tame E a := by
  rw [space, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, mem_killed]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩

end GlobalTheory.CapKilled

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormExtensionAdelesEqOneOfMulConjEqOneStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_extensionAdeles_eq_one_of_mul_conj_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z * cA σ z = 1 → Algebra.norm (AF F) z = 1 := by
  first | exact @GlobalTheory.NormOne.norm_eq_one | exact GlobalTheory.NormOne.norm_eq_one | (intros; apply GlobalTheory.NormOne.norm_eq_one <;> assumption)
end

