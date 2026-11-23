module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_small_of_mem_nhds {t : Set (FiniteAdeleRing R K)}
    (ht : t ∈ nhds (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v : HeightOneSpectrum R, Valued.v (y v) ≤ v.intValuation r) → y ∈ t := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  let t' : Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) := t
  have h1' : t' ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := ht
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ :=
    PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small_finset (R := R) (K := K) I W (fun v _ => hW0 v)
  refine ⟨r, hr, fun y hy => ?_⟩
  have hint : ∀ v : HeightOneSpectrum R,
      y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨y v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hy v))
  have hmem := hIu hz
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z = y := by
    ext v; rfl
  rw [← e]
  exact hmem

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem exists_nat_mul_mem_of_mem_nhds {F : Type} [Field F] [NumberField F] {t : Set (Af F)}
    (ht : t ∈ nhds (0 : Af F)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ b ∈ GlobalTheory.HolDict.ShortVec.intRing F, (M₀ : Af F) * b ∈ t := by
  obtain ⟨r, hr, h⟩ := exists_small_of_mem_nhds (R := 𝓞 F) (K := F) ht
  have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {r}) hr
    (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hm
  have hdvd : r ∣ ((m.natAbs : ℕ) : 𝓞 F) := by
    refine hm.trans ((map_dvd (algebraMap ℤ (𝓞 F)) (Int.dvd_natAbs.mpr dvd_rfl)).trans ?_)
    simp
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, fun b hb => h _ fun v => ?_⟩
  have hb' : evalV F v b ∈ v.adicCompletionIntegers F := Subring.mem_iInf.mp hb v
  change Valued.v (evalV F v ((m.natAbs : Af F) * b)) ≤ _
  have e : ((m.natAbs : ℕ) : Fv F v) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * c)) := by
    rw [← hc]; simp
  rw [map_mul, map_natCast, e, Valuation.map_mul, PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R, map_mul]
  calc v.intValuation r * v.intValuation c * Valued.v (evalV F v b)
      ≤ v.intValuation r * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl (v.intValuation_le_one c))
          ((mem_adicCompletionIntegers _ _ _).mp hb')
    _ = v.intValuation r := by simp

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable def singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) (c : Af D.host.F) : WO V W :=
  Matrix.of fun i' j' => if i = i' then if j = j' then
    pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k else 0 else 0

theorem continuous_singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : Continuous (singleEntry D V W i j k) := by
  have hp : Continuous (fun c : Af D.host.F => pairA D.host.F 0 c) := by
    unfold pairA; fun_prop
  have ht : Continuous (fun c : Af D.host.F =>
      (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) := by
    have e : (fun c : Af D.host.F =>
        (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) =
        fun c => pairA D.host.F 0 c •
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D) := by
      funext c; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)))
  unfold singleEntry
  refine continuous_pi fun i' => continuous_pi fun j' => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact ht
  · exact continuous_const
  · exact continuous_const

theorem singleEntry_zero (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : singleEntry D V W i j k 0 = 0 := by
  ext i' j'
  have h0 : pairA D.host.F 0 0 = 0 := rfl
  simp [singleEntry, h0]

theorem exists_nat_mul_mem_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)),
    IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧
      ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
        (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) →
        (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  intro D V W U hU
  have hnhds : (⋂ x : Fin W.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E),
      singleEntry D V W x.1 x.2.1 x.2.2 ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) := by
    refine Filter.iInter_mem.mpr fun x => ?_
    refine (continuous_singleEntry D V W x.1 x.2.1 x.2.2).continuousAt.preimage_mem_nhds ?_
    rw [singleEntry_zero]
    exact hU.mem_nhds U.zero_mem
  obtain ⟨M₀, hM₀, hM⟩ := exists_nat_mul_mem_of_mem_nhds hnhds
  refine ⟨M₀, hM₀, fun a ha => ?_⟩
  have hsum : (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) =
      ∑ i, ∑ j, ∑ k, singleEntry D V W i j k ((M₀ : Af D.host.F) * a i j k) := by
    ext i' j'
    simp [singleEntry, Matrix.sum_apply]
  rw [hsum]
  refine U.sum_mem fun i _ => U.sum_mem fun j _ => U.sum_mem fun k _ => ?_
  have := hM _ (ha i j k)
  exact Set.mem_iInter.mp this (i, j, k)

end GlobalTheory.OpenSubAdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDualComplementSandwich
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

theorem exists_left_inv {K : Type} [Field K] {n a : ℕ} (M : Matrix (Fin n) (Fin a) K) (h : M.rank = a) :
    ∃ L : Matrix (Fin a) (Fin n) K, L * M = 1 := by
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have e2 : Module.finrank K (LinearMap.range M.mulVecLin) = a := h
    rw [e2, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

variable {D : D7} (V W : HSp D)

def pr {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E) (x : WO V W) :
    Mx D a b :=
  rat Aᴴ * gA W * x * giA V * rat Bᴴ

theorem hO_emb_right {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x : WO V W) (y : Mx D a b) : hO V W x (GlobalTheory.IsoMean.emb V W A B y) = (adj y * pr V W A B x).trace := by
  have adj_mul {l m n : ℕ} (u : Mx D l m) (v : Mx D m n) : adj (u * v) = adj v * adj u :=
    Formalism.UG.cT_mul (cA D) u v
  have ht (u v : WO V W) : hO V W u v = (giA V * (adj v * (gA W * u))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  rw [ht]
  have e : adj (GlobalTheory.IsoMean.emb V W A B y) = rat Bᴴ * (adj y * rat Aᴴ) := by
    show adj (rat A * y * rat B) = _
    rw [adj_mul, adj_mul, ← rat_conjTranspose, ← rat_conjTranspose]
  rw [e, pr]
  rw [show giA V * (rat Bᴴ * (adj y * rat Aᴴ) * (gA W * x)) =
      (giA V * rat Bᴴ) * (adj y * (rat Aᴴ * gA W * x)) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem hO_emb_left {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (s : Mx D a b) (z : WO V W) : hO V W (GlobalTheory.IsoMean.emb V W A B s) z = (adj (pr V W A B z) * s).trace := by
  change hO V W (rat A * s * rat B) z = _
  have adj_mul {l m n : ℕ} (u : Mx D l m) (v : Mx D m n) : adj (u * v) = adj v * adj u :=
    Formalism.UG.cT_mul (cA D) u v
  have ht (u v : WO V W) : hO V W u v = (giA V * (adj v * (gA W * u))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  rw [ht]
  have e : adj (pr V W A B z) = rat B * (giA V * (adj z * (gA W * rat A))) := by
    rw [pr]
    simp only [adj_mul, adj_giA, adj_gA, ← rat_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e]
  rw [show giA V * (adj z * (gA W * (rat A * s * rat B))) =
      (giA V * (adj z * (gA W * rat A)) * s) * rat B by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pr_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) :
    pr V W P Q (GlobalTheory.IsoMean.emb V W P' Q' s) = s := by
  change rat Pᴴ * gA W * (rat P' * s * rat Q') * giA V * rat Qᴴ = s
  have e1 : rat Pᴴ * gA W * rat P' = 1 := by
    change rat Pᴴ * rat W.gram * rat P' = 1
    rw [show rat Pᴴ * rat W.gram * rat P' = rat (Pᴴ * W.gram * P') by simp only [rat, Matrix.map_mul], hA, rat_one]
  have e2 : rat Q' * giA V * rat Qᴴ = 1 := by
    change rat Q' * rat V.gram⁻¹ * rat Qᴴ = 1
    rw [show rat Q' * rat V.gram⁻¹ * rat Qᴴ = rat (Q' * V.gram⁻¹ * Qᴴ) by simp only [rat, Matrix.map_mul], hB, rat_one]
  calc _ = (rat Pᴴ * gA W * rat P') * s * (rat Q' * giA V * rat Qᴴ) := by simp only [Matrix.mul_assoc]
    _ = s := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem pr_sub {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x x' : WO V W) : pr V W A B (x - x') = pr V W A B x - pr V W A B x' := by
  simp only [pr, Matrix.mul_sub, Matrix.sub_mul]

theorem pr_rat {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    {x : WO V W} (hx : x ∈ ratMx D W.rank V.rank) : pr V W A B x ∈ ratMx D a b := by
  obtain ⟨M, rfl⟩ := mem_ratMx.1 hx
  exact ⟨Aᴴ * W.gram * M * V.gram⁻¹ * Bᴴ, by show rat _ = _; simp only [pr, gA, giA, rat, Matrix.map_mul]⟩

theorem trace_adj_mul {a b : ℕ} (y s : Mx D a b) : (adj y * s).trace = ∑ i, ∑ j, cA D (y i j) * s i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

end GlobalTheory.PerfectCompl

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

variable {D : D7}

theorem trace_nondeg (z : AE D) (h : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (w * z) = 0) : z = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨e0, he0⟩ := GlobalTheory.RatAnnih.tensor_rat (R := AF D.host.F) z fun e => ⟨0, by rw [map_zero]; exact h _⟩
  subst he0
  by_cases hne : e0 = 0
  · rw [hne, TensorProduct.tmul_zero]
  · exfalso
    have h1 := h ((1 : AF D.host.F) ⊗ₜ[D.host.F] e0⁻¹)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hne, GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul,
      ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, D.sp.cm.deg2] at h1
    have := NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F (h1.trans (map_zero _).symm)
    norm_num at this

theorem sum_single_left {a b : ℕ} (i : Fin a) (j : Fin b) (t : AE D) (s : Mx D a b) :
    ∑ i', ∑ j', cA D (Matrix.single i j t i' j') * s i' j' = cA D t * s i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_single_right {a b : ℕ} (i : Fin a) (j : Fin b) (u : AE D) (y : Mx D a b) :
    ∑ i', ∑ j', cA D (y i' j') * Matrix.single i j u i' j' = cA D (y i j) * u := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (V W : HSp D)

theorem symplO_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s y : Mx D a b) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ∑ i, ∑ j, cA D (y i j) * s i j) := by
  rw [symplO_eq, hO_emb_right, pr_emb V W hA hB, trace_adj_mul]

theorem symplO_emb_any {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E}
    {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) (z : WO V W) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) z =
      symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q (pr V W P' Q' z)) := by
  rw [symplO_eq, symplO_eq, hO_emb_left, hO_emb_right, pr_emb V W hA hB]

theorem emb_rat {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E)
    (γ : Matrix (Fin a) (Fin b) D.host.E) :
    GlobalTheory.IsoMean.emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
  simp [GlobalTheory.IsoMean.emb, ratW, Matrix.map_mul]

end GlobalTheory.PerfectCompl


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PerfectCompl.exists_dual_complement : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ x : WO V W, ∃ s : Mx D a b, ∀ y : Mx D a b, symplO V W (x - GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ s : Mx D a b, (∀ y : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → s = 0) ∧ (∀ s : Mx D a b, (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) ↔ s ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, (∀ s : Mx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) → γ = 0) := by
  intro D V W a b P Q hP hQ ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨L, hL⟩ := GlobalTheory.PerfectCompl.exists_left_inv P hP
  obtain ⟨L', hL'⟩ := GlobalTheory.PerfectCompl.exists_left_inv Qᵀ (by rw [Matrix.rank_transpose]; exact hQ)
  have hR : Q * L'ᵀ = 1 := by
    have := congrArg Matrix.transpose hL'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hA : Pᴴ * W.gram * (W.gram⁻¹ * Lᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (GlobalTheory.MixModel.gram_isUnit_det W), ← conjTranspose_mul, hL,
      conjTranspose_one]
  have hB : (L'ᵀ)ᴴ * V.gram * V.gram⁻¹ * Qᴴ = 1 := by
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (GlobalTheory.MixModel.gram_isUnit_det V), ← conjTranspose_mul, hR, conjTranspose_one]
  clear hL hL' hR
  obtain ⟨P', Q', hA, hB⟩ : ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E),
      Pᴴ * W.gram * P' = 1 ∧ Q' * V.gram⁻¹ * Qᴴ = 1 := ⟨_, _, hA, hB⟩
  refine ⟨P', Q', ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨GlobalTheory.PerfectCompl.pr V W P Q x, fun y => ?_⟩
    rw [GlobalTheory.MixModel.symplO_eq, GlobalTheory.PerfectCompl.hO_emb_right, GlobalTheory.PerfectCompl.pr_sub, GlobalTheory.PerfectCompl.pr_emb V W hA hB, sub_self,
      Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
  · intro s hs
    ext i j
    rw [Matrix.zero_apply]
    apply GlobalTheory.PerfectCompl.trace_nondeg
    intro w
    have h := hs (Matrix.single i j (cA D (incA D D.host.xi0⁻¹ * w)))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_left, cA_cA] at h
    rw [← h]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul]
  · intro s
    constructor
    · intro h
      have hx : GlobalTheory.IsoMean.emb V W P' Q' s ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun z hz => ?_
        rw [GlobalTheory.PerfectCompl.symplO_emb_any V W hA hB]
        exact h _ (GlobalTheory.PerfectCompl.pr_rat V W _ _ hz)
      have := GlobalTheory.PerfectCompl.pr_rat V W P Q hx
      rwa [GlobalTheory.PerfectCompl.pr_emb V W hA hB] at this
    · rintro ⟨s0, rfl⟩ γ ⟨γ0, rfl⟩
      rw [GlobalTheory.PerfectCompl.emb_rat, GlobalTheory.PerfectCompl.emb_rat]
      obtain ⟨c, hc⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (P' * s0 * Q') (P * γ0 * Q)
      rw [hc]
      exact hψ.1.2.2.1 c
  · rintro γ ⟨g, rfl⟩ h
    by_contra hne
    have hex : ∃ i j, g i j ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      ext i j
      show incA D (g i j) = 0
      rw [hall i j, map_zero]
    obtain ⟨i, j, hij⟩ := hex
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    apply hx0
    have hc : star (g i j) ≠ 0 := star_ne_zero.2 hij
    have h1 := h (Matrix.single i j
      (x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_right] at h1
    have e0 : ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b) g) i j = incA D (g i j) := rfl
    rw [e0] at h1
    have e3 : incA D D.host.xi0 * (cA D (incA D (g i j)) *
        x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))) =
        x0 • incA D (algebraMap D.host.F D.host.E (1 / 2)) := by
      rw [GlobalTheory.DualPairCheck.cA_incA, mul_smul_comm, mul_smul_comm, ← map_mul, ← map_mul]
      congr 2
      field_simp [GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, hc]
    have t : Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E (1 / 2))) = 1 := by
      have := GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul (F := D.host.F) (E := D.host.E) (AF D.host.F)
        (algebraMap D.host.F D.host.E (1 / 2))
      rw [Algebra.trace_algebraMap, D.sp.cm.deg2] at this
      refine this.trans ?_
      norm_num
    rw [e3, map_smul, t, smul_eq_mul, mul_one] at h1
    exact h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
end
end

