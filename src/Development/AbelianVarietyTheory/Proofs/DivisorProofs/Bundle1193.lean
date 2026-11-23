module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParameters
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPolarisedTopChernCoeffTransgressionTelescope
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, _root_.GlobalTheory.GoodTop.mixTop_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  first | exact @GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | exact GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | (intros; apply GlobalTheory.GraphLocal.sum_notMem_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_sum_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι]
    (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) →
    (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  intro n r _ _ ι _ ρ G₀ G₁ v hd h1
  have hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0 := by
    intro w
    have e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_sum, h1]; simp
    have hs := dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v)
      (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))
    rw [e, dbar_const] at hs
    rw [← ContinuousLinearMap.sum_apply, ← hs]; rfl
  have hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r),
      mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
    intro K₁ K₀ j L L'; simpa using _root_.GlobalTheory.GoodTop.mixTop_position_linear K₁ K₀ L L' 1 1 j
  have hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0 := by
    intro K₁ K₀ j; simpa using _root_.GlobalTheory.GoodTop.mixTop_position_linear K₁ K₀ 0 0 0 0 j
  have hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0 := by
    funext a b
    simp only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]
    rfl
  unfold corrC
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  let F : EndValuedForm11Coeffs n r →+ ℂ :=
    { toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j)
      map_zero' := hzero _ _ _
      map_add' := fun L L' => hadd _ _ _ L L' }
  have hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) =
      F (∑ i, cutForm (ρ i) G₀ G₁ v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  rw [hF, hc, map_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  let M : GL (Fin n) L → Matrix (Fin n) (Fin n) L := fun x => x.val
  have weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
    have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) L)) p p := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

  have weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
    have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) L)) (w p) (w p) := by rw [mul_inv_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single p (fun b _ hb => by
        rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

  have weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
    intro p a hpa
    have hne : (M x) a (w⁻¹ a) ≠ 0 := by
      intro h0
      have := weylRep_mul_inv_diag hx (w⁻¹ a)
      rw [show w (w⁻¹ a) = a by simp] at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) L)) p (w⁻¹ a) := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
    rw [Finset.sum_eq_single a (fun b _ hb => by
        rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
    exact (mul_eq_zero.1 h).resolve_right hne

  have weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L)
      (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
    have hi := weylRep_inv hx
    dsimp only [M]
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
      (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
      Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

  dsimp only [M] at weylRep_inv_mul_diag weylRep_mul_inv_diag weylRep_conj_apply
  have mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L) :
      u ∈ cell x ↔ u ∈ unipB L (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
    dsimp only [M]
    rw [mem_cell, mem_unipBLower]
    refine and_congr_right fun hu => ?_
    rw [mem_unipB] at hu
    constructor
    · rintro ⟨hl, -⟩ a b hab hw
      have h := hl _ _ hw
      rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
      have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
      have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
      rw [show w (w⁻¹ a) = a by simp] at h1
      rw [show w (w⁻¹ b) = b by simp] at h2
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
        · exact h
      · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
    · intro h
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · rw [weylRep_conj_apply hx]
        rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
        · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
        · rw [hu.1 _ _ hl, mul_zero, zero_mul]
      · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

  rw [cellU, Subgroup.mem_subgroupOf, mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.DegGrowth

open MvPolynomial

theorem expand (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Ψ ((X 0 + C t * X 1) ^ D) = ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  intro hC k _ Y _ p D hX L A
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).2
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  have hiso0 : (comb ![L, A] ![1, 0]).Isometric L := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, Fin.sum_univ_two]
  have hlin0 : (lin fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ)) = (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp [lin, Fin.sum_univ_two]
  have h0 : Ψ (X 0 ^ D) = gdeg L D := by
    rw [← hlin0, hΨ.1, hiso0.gdeg_eq]
  have hn_eq (n : ℕ) : gdeg ((L.pow n).tens A) D = Ψ ((C (n : ℝ) * X 0 + C 1 * X 1) ^ D) := by
    rw [← (hiso n).gdeg_eq, ← hΨ.1, hlin]
  set f : ℝ → ℝ := fun t => Ψ ((X 0 + C t * X 1) ^ D) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Ψ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = gdeg L D := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hn_eq, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.DegGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1Projective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpaceDegree

theorem topSelf_O1_str : ∀ (k : Type) [Field k] (N : ℕ),
    letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 :=
  fun k _ N => GlobalTheory.NefNumericsModel.selfIntersection_O1 k N

end GlobalTheory.ProjSpaceDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChange
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_changeFrame {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n} (h₀ : MContDiffAt 2 G₀ v) (u₀ : IsUnit (G₀ v).det)
    (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) (hA : MContDiffAt 2 A v) (hAu : IsUnit (A v).det)
    (hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) :
    corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  unfold corrC
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.T.polarisedTopChernCoeff_conj (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) (A v) hAu]
  congr 1
  funext i a b
  unfold intersection_update_fsHerm_neg_one
  split_ifs
  · exact curv_changeFrame h₁ u₁ hA hAu hA0 _ _
  · simp only [cutForm]
    rw [conn_changeFrame (h₁.of_le one_le_two) u₁ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      conn_changeFrame (h₀.of_le one_le_two) u₀ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      ← Matrix.mul_sub, add_sub_add_right_eq_sub, ← Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  · exact curv_changeFrame h₀ u₀ hA hAu hA0 _ _

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParametersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | exact GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | (intros; apply GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
end

