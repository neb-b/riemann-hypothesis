module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentDescentOrOpenCell
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem antitone_comp_of_adjacent {h N : ℕ} (b : Fin N → Fin h) (w : Equiv.Perm (Fin N))
    (hstep : ∀ i j : Fin N, (j : ℕ) = i + 1 → b (w j) ≤ b (w i)) :
    Antitone (b ∘ w) := by
  intro x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [Fin.mk_le_mk] at hxy
  revert hy
  induction y, hxy using Nat.le_induction with
  | base => intro hy; exact le_rfl
  | succ n hxn ih =>
    intro hy
    have hn : n < N := by omega
    exact le_trans (hstep ⟨n, hn⟩ ⟨n + 1, hy⟩ rfl) (ih hn)

theorem blk_comp_wOpen_antitone {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    Antitone (blk (stdBlocks d hd) ∘ wOpen d hd) := by
  intro x y hxy
  have hm := Tuple.monotone_sort (wKey d hd) hxy
  simp only [Function.comp, wKey] at hm
  rcases Prod.Lex.toLex_le_toLex.mp hm with h | ⟨h, -⟩
  · exact (OrderDual.toDual_lt_toDual.mp h).le
  · exact le_of_eq (OrderDual.toDual_inj.mp h).symm

theorem pm_mem_parab_of_blk_eq (k : Type) [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (v : Equiv.Perm (Fin N)) (hv : ∀ q, blk (stdBlocks d hd) (v q) = blk (stdBlocks d hd) q) :
    pm k v ∈ parab k (stdBlocks d hd) := by
  show (↑(pm k v) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (stdBlocks d hd))
  intro i j hij
  have hne : v⁻¹ i ≠ j := by
    intro hj
    subst hj
    have hb := hv (v⁻¹ i)
    have hvi : v (v⁻¹ i) = i := by simp
    rw [hvi] at hb
    rw [← hb] at hij
    exact lt_irrefl _ hij
  change (Equiv.toPEquiv v⁻¹).toMatrix i j = 0
  rw [PEquiv.toMatrix_apply]
  simpa using hne

theorem cell_eq_of_blk_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (w w' : Equiv.Perm (Fin N))
    (hw : ∀ p, blk (stdBlocks d hd) (w p) = blk (stdBlocks d hd) (w' p)) :
    cell k d hd w = cell k d hd w' := by
  have key : ∀ u u' : Equiv.Perm (Fin N),
      (∀ p, blk (stdBlocks d hd) (u p) = blk (stdBlocks d hd) (u' p)) → cell k d hd u ⊆ cell k d hd u' := by
    intro u u' hu g hg
    simp only [cell, Set.mem_ofPred_eq] at hg ⊢
    obtain ⟨p, hp, n, hn, rfl⟩ := hg
    have hv : ∀ q, blk (stdBlocks d hd) ((u * u'⁻¹) q) = blk (stdBlocks d hd) q := by
      intro q
      rw [Equiv.Perm.mul_apply, hu]
      simp
    have hpm : pm k u = pm k (u * u'⁻¹) * pm k u' := by
      unfold pm
      rw [← map_mul, inv_mul_cancel_right]
    refine ⟨p * pm k (u * u'⁻¹), (parab k (stdBlocks d hd)).mul_mem hp (pm_mem_parab_of_blk_eq k d hd _ hv),
      n, hn, ?_⟩
    rw [hpm]
    simp only [mul_assoc]
  exact Set.Subset.antisymm (key w w' hw) (key w' w fun p => (hw p).symm)

theorem exists_adjacent_blk_lt_or_cell_eq_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)),
    (∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)) ∨
      cell k d hd w = cell k d hd (wOpen d hd) := by
  intro k _ _ _ _ h N d hd w
  by_cases hex : ∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)
  · exact Or.inl hex
  · right
    simp only [not_exists, not_and, not_lt] at hex
    have hA := antitone_comp_of_adjacent (blk (stdBlocks d hd)) w hex
    have hB := blk_comp_wOpen_antitone d hd
    have hU := Tuple.unique_monotone (f := fun q => OrderDual.toDual (blk (stdBlocks d hd) q))
      (σ := w) (τ := wOpen d hd) (monotone_toDual_comp_iff.mpr hA) (monotone_toDual_comp_iff.mpr hB)
    refine cell_eq_of_blk_eq k d hd w (wOpen d hd) fun p => ?_
    exact OrderDual.toDual_inj.mp (congrFun hU p)

end GlobalTheory.CompanionTheory.Rodier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegral
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.BinaryDil

theorem fibre_unit_dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 0 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf 1) minf → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ s t : Ainf F, IsUnit t → minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s)) = ((∏ w, ‖e t w‖₊) ^ (2 * M - 2)) • (minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm e he s t ht
  have hloc : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  obtain ⟨i1, i2, i3, i4, i5, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set N : ℝ≥0 := ∏ w, ‖e t w‖₊ with hN
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have : IsUnit (e t) := ht.map e
    exact nnnorm_ne_zero_iff.2 (Pi.isUnit_iff.1 this w).ne_zero
  have hN2 : ∏ w, ‖e (t ^ 2) w‖₊ = N ^ 2 := by
    rw [hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [map_pow]
  have hs1 := _root_.GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam t ht
  have hs2 := _root_.GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t ^ 2) (ht.pow 2)
  rw [hN2] at hs2
  have hk := _root_.GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit F E σ hσ M 2 b lam hlam t ht _ hs1
  let g : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) := Matrix.of fun _ _ => algebraMap (Ainf F) (Ainf F ⊗[F] E) t
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact ht.map (algebraMap (Ainf F) (Ainf F ⊗[F] E))
  have hrm : (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) =
      fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    funext X p i
    simp only [GlobalTheory.CompanionTheory.SW.rmul, Fin.sum_univ_one, g, Matrix.of_apply]
    rw [Subsingleton.elim p 0, mul_comm]
  have hsig : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) t) = algebraMap (Ainf F) (Ainf F ⊗[F] E) t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j, by
      intro i j
      have := S.2 i j
      show sigR (Ainf F) σ (_ * _) = _ * _
      rw [map_mul, this, map_pow, map_pow, hsig]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j =
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
    have : Continuous τ := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    exact this.measurable
  have hc := _root_.GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf F E σ hσ 2 b lam hlam (t ^ 2) (ht.pow 2) _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, map_pow, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have key := _root_.GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul F E σ hσ M J hJ (Ainf F) hloc 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk) hc (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)
  have hτs : τ (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s) = GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    change algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (s ⊗ₜ[F] (1 : E)) = (t ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs, hrm] at key
  have e1 : (N ^ (2 * M)) * (N⁻¹ ^ (2 * M)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e2 : (N ^ (2 * M)) * (N ^ 2)⁻¹ = N ^ (2 * M - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hN0), mul_one]
    simp
  have key2 := congrArg (fun μ' => (N ^ (2 * M)) • μ') key
  simp only [smul_smul] at key2
  rw [e1, e2, one_smul] at key2
  exact key2

theorem dilation_inf_binary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hm θ hθ ε hε s φ hφ
  obtain ⟨-, e, -, he, -, habs, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Fin 1 → Fin 2 → Ainf F ⊗[F] E) := hB 1 2
  set t : Ainf F := θ ε with ht_def
  have ht : IsUnit t := (isUnit_iff_ne_zero.2 hε.ne').map θ
  have key := fibre_unit_dilation F E σ hσ 2 J hJ (by norm_num) d b li hli.1 mi hm e he s t ht
  set n := Module.finrank ℚ F with hn
  have hw : ∀ w, ‖e t w‖₊ = ε.toNNReal := by
    intro w
    have h1 := (PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hσ.1).2 θ hθ ε w
    have h2 := habs t w
    apply NNReal.eq
    rw [coe_nnnorm, Real.norm_eq_abs, h2, Real.coe_toNNReal _ hε.le]
    rw [show ‖t w‖ = ‖θ ε w‖ from rfl, h1, abs_of_pos hε]
  have hN : ∏ w, ‖e t w‖₊ = ε.toNNReal ^ n := by
    have hc : Fintype.card (InfinitePlace F) = n := by
      have := hσ.1
      rw [hn, IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, hc]
  have hs : θ (ε ^ 2) * s = t ^ 2 * s := by rw [map_pow]
  have hD : Continuous (fun (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hf : Measurable (fun X => ENNReal.ofReal (φ X)) := hφ.measurable.ennreal_ofReal
  rw [hs, key, lintegral_smul_measure, lintegral_map hf hD.measurable, hN]
  have hdil : ∀ X, PositivityTheory.Rg.Mass.dil θ ε X = fun p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    intro X
    funext p i
    simp [PositivityTheory.Rg.Mass.dil, Algebra.TensorProduct.algebraMap_apply, ht_def]
  simp only [hdil]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, Real.coe_toNNReal _ hε.le]
  ring

end GlobalTheory.CompanionTheory.BinaryDil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellHeightStratification
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Parabolic DoubleCoset

namespace GlobalTheory.CompanionTheory.Rodier.CellOrder

def blkNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : ℕ :=
  ((blk (stdBlocks d hd) i : Fin h) : ℕ)

def idxNat {N : ℕ} (i : Fin N) : ℕ := i

theorem card_filter_le_of_antitone {N : ℕ} (β : Fin N → ℕ) (u w : Equiv.Perm (Fin N))
    (hu : Antitone (β ∘ u)) (a b : ℕ) :
    (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card ≤
      (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)).card := by
  classical
  by_cases hsub : ∀ j : Fin N, (j : ℕ) ≤ b → a ≤ β (u j)
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hsub j hj.1⟩
  · push Not at hsub
    obtain ⟨i, hib, hia⟩ := hsub
    have hdown : ∀ j : Fin N, a ≤ β (u j) → (j : ℕ) ≤ b := by
      intro j hj
      by_contra hjb
      push Not at hjb
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]
        omega
      exact absurd (le_trans hj (hu hij)) (not_le.2 hia)
    have e1 : (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)) =
        Finset.univ.filter fun j : Fin N => a ≤ β (u j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hdown j h, h⟩⟩
    rw [e1]
    calc (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card
        ≤ (Finset.univ.filter fun j : Fin N => a ≤ β (w j)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj.2
      _ = (Finset.univ.filter fun j : Fin N => a ≤ β (u j)).card := by
          apply Finset.card_bij' (fun j _ => u.symm (w j)) (fun j _ => w.symm (u j)) <;> simp_all

theorem exists_diag_mul_unip {k : Type} [Field k] {N : ℕ} (b : GL (Fin N) k)
    (hb : b ∈ blockUpper k N (idxNat (N := N))) :
    ∃ t : GL (Fin N) k, (∀ i j, i ≠ j → (t : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∃ n ∈ unipB k (Fin N), b = t * n := by
  classical
  have hb' : (b : Matrix (Fin N) (Fin N) k).BlockTriangular id := fun i j h => hb h
  have hdet : ∏ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular hb']
    exact (Matrix.isUnits_det_units b).ne_zero
  have hD : ∀ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  let D : Fin N → k := fun i => (b : Matrix (Fin N) (Fin N) k) i i
  let t : GL (Fin N) k := ⟨Matrix.diagonal D, Matrix.diagonal D⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hD i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (hD i)⟩
  refine ⟨t, fun i j hij => Matrix.diagonal_apply_ne _ hij, t⁻¹ * b, ?_, (mul_inv_cancel_left t b).symm⟩
  have hval : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal D⁻¹ * (b : Matrix (Fin N) (Fin N) k) := rfl
  have hP : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular
      (GlobalTheory.SmGL.blk (GlobalTheory.SmGL.points (Fin N))) := by
    rw [hval]
    exact (Matrix.blockTriangular_diagonal _).mul (fun i j h => hb h)
  show t⁻¹ * b ∈ GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.points (Fin N))
  unfold GlobalTheory.SmGL.unipRad
  rw [Subgroup.mem_map]
  refine ⟨⟨t⁻¹ * b, hP⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  apply Units.ext
  ext x y
  change ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a a = (1 : Matrix Unit Unit k) x y
  rw [hval, Matrix.diagonal_mul, Subsingleton.elim x y, Matrix.one_apply_eq]
  exact inv_mul_cancel₀ (hD a)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem parab_eq_blockUpper :
    parab k (stdBlocks d hd) = blockUpper k N (blkNat d hd) := by
  ext g
  exact Iff.rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unipB_le_blockUpper : unipB k (Fin N) ≤ blockUpper k N (idxNat (N := N)) := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hg
  exact fun i j h => p.2 h

theorem cell_eq_doubleCoset (w : Equiv.Perm (Fin N)) :
    cell k d hd w = doubleCoset (pm k w) (blockUpper k N (blkNat d hd) : Set (GL (Fin N) k))
      (blockUpper k N (idxNat (N := N))) := by
  ext g
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨p, hp, n, hn, rfl⟩
    rw [parab_eq_blockUpper] at hp
    exact ⟨p, hp, n, unipB_le_blockUpper k hn, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨t, ht, n, hn, rfl⟩ := exists_diag_mul_unip q hq
    refine ⟨p * (pm k w * t * (pm k w)⁻¹), ?_, n, hn, by group⟩
    rw [parab_eq_blockUpper]
    refine Subgroup.mul_mem _ hp ?_
    unfold pm
    rw [GroundTheory.Automorphic.Parabolic.conj_permGL_mem_blockUpper_iff]
    intro i j hij
    exact ht i j (fun h => by subst h; exact lt_irrefl _ hij)

theorem antitone_blkNat_wOpen : Antitone (blkNat d hd ∘ wOpen d hd) := by
  intro i j hij
  have hm := Tuple.monotone_sort (wKey d hd) hij
  simp only [Function.comp_apply] at hm ⊢
  unfold wOpen blkNat
  unfold wKey at hm
  rcases (Prod.Lex.toLex_le_toLex).1 hm with h1 | ⟨h1, -⟩
  · exact (Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h1)).le
  · exact le_of_eq (congrArg Fin.val (OrderDual.toDual_inj.1 h1)).symm

theorem cellRank_le_wOpen (w : Equiv.Perm (Fin N)) (a b : ℕ) :
    cellRank (blkNat d hd) idxNat (pm k w) a b ≤
      cellRank (blkNat d hd) idxNat (pm k (wOpen d hd)) a b := by
  unfold pm
  rw [GroundTheory.Automorphic.Parabolic.cellRank_permGL, GroundTheory.Automorphic.Parabolic.cellRank_permGL]
  exact card_filter_le_of_antitone (blkNat d hd) (wOpen d hd) w (antitone_blkNat_wOpen d hd) a b

theorem cells_cover_height :
    (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ,
      (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧
      (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧
      ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  refine ⟨fun g => ?_, GroundTheory.Automorphic.Parabolic.cellHeight (blkNat d hd) idxNat, fun w g hg => ?_,
    fun w => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
      (F := k) (β := blkNat d hd) (γ := idxNat) g
    refine ⟨w, ?_⟩
    rw [cell_eq_doubleCoset]
    exact hw
  · rw [cell_eq_doubleCoset] at hg
    exact GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset hg
  · rw [cell_eq_doubleCoset]
    exact GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset _
  · by_contra hle
    push Not at hle
    have hr := GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
      (fun a b => cellRank_le_wOpen k d hd w a b) hle
    have hmem := GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq hr
    apply hw
    rw [cell_eq_doubleCoset, cell_eq_doubleCoset, DoubleCoset.doubleCoset_eq_of_mem hmem]

theorem cells_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ, (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧ (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧ ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  intro k _ _ _ _ h N d hd
  exact cells_cover_height k d hd

end GlobalTheory.CompanionTheory.Rodier.CellOrder
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExists
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ScalarEx

theorem exists_scalarBy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  intro k _ _ _ _ x t
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  exact ⟨(ω t : ℂ), fun v => hω t v⟩

end GlobalTheory.CompanionTheory.ScalarEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainmentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_open_ideal_containment : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | exact GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image <;> assumption)
end

