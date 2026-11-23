module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
section
namespace I195MixedCoordinates_b252ee61f962e28100fad012

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

end I195MixedCoordinates_b252ee61f962e28100fad012

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.ThetaOf

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem exists_symplO_eq (d : HypDec S S₀ ρ) (T : HSp D) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E} (hξ : ξ ≠ 0)
    (t : AF D.host.F) : ∃ a, symplO S T (d.extX T (rat ξ)) (d.extY T a) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hv : T.gram * ξ ≠ 0 := fun h => hξ (by
    rw [← Matrix.nonsing_inv_mul_cancel_left T.gram ξ (gram_isUnit_det T), h, Matrix.mul_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, (T.gram * ξ) i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Matrix.ext h)
  let c : AE D := t ⊗ₜ[D.host.F] ((2 * D.host.xi0 * (T.gram * ξ) i j)⁻¹)
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have h := d.hO_ext T (rat ξ) 0 0 (adj (Matrix.single j i c)) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_adj, gA, ← rat_mul,
    Matrix.trace_single_mul, smul_eq_mul]
  have e : incA D D.host.xi0 * (c * rat (T.gram * ξ) i j) = t ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (1 / 2)) := by
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.xi0) * (c * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (T.gram * ξ) i j)) = _
    simp only [c, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [map_div₀, map_one, map_ofNat]
    field_simp
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem integral_char_eq_zero {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (χ : Mx D m n → ℂ) (hmul : ∀ a b, χ (a + b) = χ a * χ b)
    (hγ : ∀ γ ∈ ratMx D m n, χ γ = 1) {u : Mx D m n} (hu : χ u ≠ 1) : ∫ a in 𝓕, χ a ∂μ = 0 := by
  have h1 := covolOne_integral_add h χ (fun γ hg a => by rw [hmul, hγ γ hg, one_mul]) u
  simp only [hmul, integral_mul_const] at h1
  by_contra h0
  exact hu (mul_left_cancel₀ h0 (h1.trans (mul_one _).symm))

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_left]; ring

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_right]; ring

theorem continuous_symplO {S T : HSp D} {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  simp only [symplO_eq_add]
  exact (GlobalTheory.OrientedHeis.continuous_symplOH hx hy).add (GlobalTheory.OrientedHeis.continuous_symplOH hx hy)

theorem integral_pair (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E}
    (hξ : ξ ≠ 0) : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) ∂μ = 0 := by
  obtain ⟨t, ht⟩ := hψ.1.2.2.2
  obtain ⟨u, hu⟩ := exists_symplO_eq d T hξ t
  refine integral_char_eq_zero h _ (fun a b => ?_) (fun γ hγ => ?_) (u := u) (by rw [hu]; exact ht)
  · rw [map_add (f := _), symplO_add_right, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T _).2 (ratMx_mul (rat_mem _) (rat_mem _)) _
      (ratMx_mul hγ (rat_mem _))

theorem bound_translates (hψ : IsStdChar D ψ (-1)) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) : Continuous φ ∧ ∀ Q : Set (Mx D m n), IsCompact Q →
      ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨hc, K, hK, hb⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n φ hφ
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajLoc.summable_bound D θ hθ m n
  obtain ⟨C, hC⟩ := hb N
  refine ⟨hc, fun Q hQ => ?_⟩
  obtain ⟨b, hs, hb⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hs.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem theta_series (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {φ : Mx D T.rank ρ → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {f : WO S T → ℂ}
    (hf : ∀ w : WO S T, f w = ψ (-(symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (w ⬝ d.jY)))) *
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
        ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    Continuous f ∧ ∀ x, (_root_.I195MixedCoordinates_b252ee61f962e28100fad012.source d) T ψ μ 𝓕 f x 0 = φ x := by
  obtain ⟨hc, hb⟩ := bound_translates hψ hφ
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hjX : Continuous fun w : WO S T => (w ⬝ d.jX : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  have hjY : Continuous fun w : WO S T => (w ⬝ d.jY : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  constructor
  · obtain ⟨i1, i2, -⟩ := lattice_Mx D T.rank S.rank
    obtain ⟨j1, -⟩ := lattice_Mx D T.rank ρ
    rw [funext hf]
    refine (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp hjX) (hY.comp hjY)).neg).mul ?_
    refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨Q, hQ, hw⟩ := exists_compact_mem_nhds w
    obtain ⟨b, hs, hb⟩ := hb _ (hQ.image hjX)
    refine ContinuousOn.continuousAt (continuousOn_tsum (fun ξ => Continuous.continuousOn ?_) hs fun ξ y hy => ?_) hw
    · exact (hψc.comp (continuous_symplO (hX.comp (hjX.add continuous_const)) (hY.comp hjY))).mul
        (hc.comp (hjX.add continuous_const))
    · rw [norm_mul, hn, one_mul]
      exact hb _ ⟨y, hy, rfl⟩ ξ
  · intro x
    obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
    haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
    haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
    haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
    haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
    obtain ⟨b, hs, hb⟩ := hb {x} isCompact_singleton
    have hone : μ.real 𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]
    have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) f)) 0 =
        ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) := by
      intro a
      have e1 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jX : Mx D T.rank ρ) = x := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pY_jX,
          Matrix.mul_one, Matrix.mul_zero, zero_add]
      have e2 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jY : Mx D T.rank ρ) = a := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY, HypDec.pY_jY,
          Matrix.mul_one, Matrix.mul_zero, add_zero]
      rw [d.integrandS_eq, map_zero, add_zero, hf, e1, e2, ← mul_assoc, ← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.extX T), symplO_add_left,
        symplOH_skew S T (d.extX T x), symplO_eq_add S T (d.extX T x)]
      congr 2
      ring
    have hF := hasSum_integral_of_summable_integral_norm (μ := μ.restrict 𝓕)
      (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
        ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ)) (fun ξ => ?_) ?_
    · rw [_root_.I195MixedCoordinates_b252ee61f962e28100fad012.source]
      simp only [HypDec.extX_apply, HypDec.extY_apply, map_zero, Matrix.zero_mul] at key ⊢
      simp only [key]
      refine hF.unique ?_
      have h0 : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * φ (x + rat 0) ∂μ = φ x := by
        simp only [rat_zero, map_zero, symplO_eq_add, symplOH_zero_left, add_zero, AddChar.map_zero_eq_one, one_mul,
          setIntegral_const, hone, one_smul]
      rw [← h0]
      refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
        ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) ∂μ) 0 fun ξ hξ => ?_
      rw [integral_mul_const, integral_pair hψ d T h hξ, zero_mul]
    · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
      exact (hψc.comp (continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
    · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb x rfl ξ) hs

theorem theta_series_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → Continuous f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 h φ hφ f hf
  obtain ⟨h1, h2⟩ := theta_series hψ (dblDec A) B h hφ hf
  exact ⟨h1, funext h2⟩

end GlobalTheory.Core.Rk.ThetaOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TensorSrc

theorem op_prod {X Y : Type} (L : Module.End ℂ (X → ℂ)) (M : Module.End ℂ (Y → ℂ)) (f : X → ℂ) (g : Y → ℂ) (u : X)
    (v : Y) : L (fun u' => M (fun v' => f u' * g v') v) u = L f u * M g v := by
  have h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u' := by
    intro u'
    have : (fun v' => f u' * g v') = f u' • g := by funext v'; simp
    rw [this, map_smul]; simp [mul_comm]
  have h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f := by
    funext u'; simp [h1]
  rw [h2, map_smul]; simp [mul_comm]

theorem tensorSource : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorSource ψ d T := by
  intro D ψ hψ S A B d T
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.BoxSlice.main D ψ hψ S A B T d
  have hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v := by
    intro fA fB u v
    simp [OrthDec.boxS]
  refine ⟨h1, h2, h3, h4, _root_.GlobalTheory.DenseSum.unifLimit_prodSpan D ψ hψ S A B T d, ?_, ?_⟩
  · intro χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB
    funext x
    obtain ⟨⟨u, v⟩, rfl⟩ := (d.resS T).symm.surjective x
    rw [_root_.GlobalTheory.TensorScalarOne.tensor_scalar_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]
    simp only [hb]
    exact op_prod _ _ fA fB u v
  · intro χA χB χT omS omA omB hS hA hB a b h f hf v
    refine ⟨?_, fun u => _root_.GlobalTheory.TensorScalarOne.tensor_scalar_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩
    have := (h4 _ ((_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v
    simpa using this

end GlobalTheory.TensorSrc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSet
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchy
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensCauchy

open GlobalTheory.Size

section

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f + f') =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f + GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')

theorem word_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} (h : f ∈ thetaLevel ψ S T U) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f ∈ thetaLevel ψ S T U := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    exact GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (f : WO S T → ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (d + l.length) f := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    refine (GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))
    congr 1
    simp only [List.length_cons]
    omega

end

theorem uniformCauchySeqOn_word : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l
  obtain ⟨d₀, C, hb⟩ := GlobalTheory.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hη : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨J, hJ⟩ := hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)
  refine ⟨J, fun i hi j hj w _ => ?_⟩
  have hd : u i - u j ∈ thetaLevel ψ S T U := Submodule.sub_mem _ (hu i) (hu j)
  have he := word_add hψ hθ l hd.1 (hu j).1
  rw [sub_add_cancel] at he
  have h1 := (hb _ (word_mem hψ hθ l hd) w).trans
    (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)
  rw [dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.ThetaDensCauchy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmField
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertTwo

theorem valued_two_eq_one : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  intro D v w hi
  have hu : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).2 rfl
  have hc : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hi hu
  have h : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hc
  rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
    ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 h

end GlobalTheory.InertTwo
end
end

