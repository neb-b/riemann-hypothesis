module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixForm
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep

theorem prod_base_split {K : Type} [Fintype K] {σ : Type} (blk : σ → Option K) (p : σ) (k₀ : K)
    (hp : blk p = some k₀) (f : K → ℝ)
    (hf : ∀ k, (¬ ∀ p', blk p' ≠ some k) → k ≠ k₀ → f k = 1) :
    ∏ k, f k = (∏ k : NonPluckerBlocks blk, f k.1) * f k₀ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun k => ∀ p', blk p' ≠ some k]
  congr 1
  · exact Finset.prod_subtype _ (by simp) f
  · refine Finset.prod_eq_single_of_mem k₀ ?_ ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => e p hp⟩
    · intro k hk e
      exact hf k (Finset.mem_filter.1 hk).2 e

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z I₀ C B hp hC hx hz hor hw
  obtain ⟨h, a, hb, hd, ha, hstep, hzk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx.1 hz hor
  obtain ⟨hHb, hHd, hHm⟩ := hC h a _ hb hd ha hstep hw
  have hL : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  have hor' := hor
  obtain ⟨c0, hc0, e0⟩ := hor'
  have hbz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [e0]
    exact ((TorusAct.main _ _ _ M.x _ c0 hc0).2 hL).1
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k h0
    have hl : BM.Rb.lift x₀ x₀ ⟨k, (BM.F l).c k⟩ = 0 := by
      have e1 := congrFun e0 ⟨k, (BM.F l).c k⟩
      rw [h0] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_left (hc0 k)
    refine (BM.good l x₀ hx.1).1 k ?_
    show mConeMap (BM.Rb.lift x₀ x₀) (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, hl, map_zero, zero_mul]
  let c : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then
    (basePart M.blk z ⟨⟨k, hk⟩, (BM.F l).c ⟨k, hk⟩⟩)⁻¹ else if k = k₀ then (plk M (BM.F l) k₀ z I₀)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M.blk, c k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
  have hck : c k₀ = (plk M (BM.F l) k₀ z I₀)⁻¹ := (dif_neg hk₀).trans (if_pos rfl)
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : ∀ p', M.blk p' ≠ some k
    · rw [hcb ⟨k, hk⟩]
      exact inv_ne_zero (hne ⟨k, hk⟩)
    · by_cases e : k = k₀
      · rw [e, hck]
        exact inv_ne_zero hw
      · rw [show c k = 1 from (dif_neg hk).trans (if_neg e)]
        exact one_ne_zero
  have hz₂ := ((TorusAct.main K ι Φ y z c hc).2 hz).1
  have hval := ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc _)).2 hbz).2
  have hbp : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) =
      fun q : Σ k, baseIdx ι M.blk k => c q.1.1 * basePart M.blk z q := rfl
  have hso : SameOrbit (basePart M.blk (fun q : Σ k, ι k => c q.1 * z q)) (BM.Rb.lift x₀ x₀) := by
    refine ⟨fun k => c k.1 * c0 k, fun k => mul_ne_zero (hc _) (hc0 k), ?_⟩
    rw [hbp, e0]
    funext q
    exact (mul_assoc _ _ _).symm
  have hnorm : ∀ k, basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbp]
    show c k.1 * basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1
    rw [hcb k, inv_mul_cancel₀ (hne k)]
  have hlog := (BM.induced l x₀ hx p _ hz₂ hso hnorm _ hHb hHd).1 k₀ hp (fun m => by
    rw [hbp, hzk m, hck]
    simp only [hval]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [mul_left_comm a, ← hHm I, mul_left_comm, ← mul_assoc _ _ (plk M (BM.F l) k₀ z I₀), mul_comm _ (plk M (BM.F l) k₀ z I₀),
      mul_inv_cancel_left₀ hw])
  have hs := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at hs
  have hdy : M.dy p k₀ = 1 := (dif_neg hk₀).trans (if_pos hp)
  have hdy0 : ∀ k, (¬ ∀ p', M.blk p' ≠ some k) → k ≠ k₀ → M.dy p k = 0 := fun k hk e =>
    (dif_neg hk).trans (if_neg fun e' => e (Option.some_injective _ (hp.symm.trans e')).symm)
  have hsplit := prod_base_split M.blk p k₀ hp (fun k => ‖c k‖ ^ M.dy p k)
    (fun k hk e => by simp only [hdy0 k hk e, zpow_zero])
  have hPQ : (∏ k, ‖c k‖ ^ M.dy p k) * ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ = 1 := by
    rw [hsplit, hdy, zpow_one, hck, norm_mul, baseMono, norm_prod, norm_inv]
    simp only [norm_zpow]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcb k, norm_inv, _root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hne k)))]
  have hpos := (BM.hom p).pos (fun q => c q.1 * z q) hz₂.1
  have hQ : ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ ≠ 0 := fun e => by
    rw [e, mul_zero] at hPQ
    exact zero_ne_one hPQ
  have hh : (BM.hom p).h z =
      ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ * (BM.hom p).h fun q => c q.1 * z q := by
    rw [hs, ← mul_assoc, mul_comm ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖, hPQ, one_mul]
  rw [hh, Real.log_mul hQ hpos.ne', hlog, add_comm]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepCols_ne_empty_of_le {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hN := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at hm
    simp at hm
  · have hlt : 0 < N := by omega
    have hm : (⟨0, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at hm
    simp at hm

theorem exists_plk_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hp hx hz hO
  obtain ⟨h, a, hb, -, ha, hpl, hzk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx hz hO
  by_contra hcon
  push_neg at hcon
  have hmin : ∀ I, minorIJ h I (stepCols N j p.2) = 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · have e := hpl I hI
      rw [hcon I hI] at e
      exact (mul_eq_zero.1 e.symm).resolve_left ha
    · exact ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le).2.1 h I hb hI).resolve_right
        (stepCols_ne_empty_of_le M.j_le p.2)
  obtain ⟨m, hm⟩ := hz.1 k₀
  exact hm (by rw [hzk m]; simp [hmin])

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degreeGeneric_of_degree :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement → GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement := by
  intro hDeg K _ _ ι _ P e L hP hL
  classical
  rw [hDeg K ι P e L 2 hP hL Nat.prime_two,
    GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e (fun j => (L j).a) 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermAppendSnoc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem exists_perm_append_snoc {α : Type*} {d r : ℕ} (A : Fin d → α) (B : Fin r → α) (c : α)
    (h : d + r + 1 = d + 1 + r) :
    ∃ σ : Equiv.Perm (Fin (d + r + 1)),
      ((Fin.append (Fin.snoc (α := fun _ => α) A c) B) ∘ Fin.cast h) ∘ σ =
        Fin.snoc (α := fun _ => α) (Fin.append A B) c := by
  let g : ℕ → ℕ := fun i => if i < d then i else if i = d + r then d else i + 1
  have hg : ∀ i, i < d + r + 1 → g i < d + r + 1 := by
    intro i hi
    simp only [g]
    split_ifs <;> omega
  let f : Fin (d + r + 1) → Fin (d + r + 1) := fun i => ⟨g i, hg i i.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : g a = g b := congrArg Fin.val hab
    have ha := a.2
    have hb := b.2
    apply Fin.ext
    simp only [g] at hab'
    split_ifs at hab' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  funext j
  simp only [Function.comp, Equiv.ofBijective_apply]
  induction j using Fin.lastCases with
  | last =>
    have e : Fin.cast h (f (Fin.last (d + r))) = Fin.castAdd r (Fin.last d) := by
      apply Fin.ext
      simp [f, g]
    rw [e, Fin.append_left, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    rw [Fin.snoc_castSucc]
    induction j using Fin.addCases with
    | left i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.castAdd r i))) = Fin.castAdd r (Fin.castSucc i) := by
        apply Fin.ext
        simp [f, g]
      rw [e, Fin.append_left, Fin.append_left, Fin.snoc_castSucc]
    | right i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.natAdd d i))) = Fin.natAdd (d + 1) i := by
        apply Fin.ext
        have := i.2
        simp [f, g]
        split_ifs <;> omega
      rw [e, Fin.append_right, Fin.append_right]

theorem isSmoothHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (c : ℝ) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) :=
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _ from contDiffOn_const

theorem isPullHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (c : ℝ) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c) := by
  refine ⟨?_, fun _ => rfl⟩
  funext k'
  show (0 : K' → ℤ) k' = Function.extend κ (0 : K → ℤ) 0 k'
  classical
  rw [Function.extend_def]
  split_ifs <;> rfl

theorem ptsIntegral_projection : PFStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ) (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'), IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) = (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (imageZ v P') (pot L) (fun _ => 1) := by
  intro hPF hEx K _ ι _ K' _ ι' _ κ v P' d r G J L L' N hb hP' hZ hJ hL hLL hN
  obtain ⟨I, hI⟩ := hEx
  have hn : d + r + 1 = d + 1 + r := by omega
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hb (hLL j) (hL j)
  let c : ℝ := -Real.log ((2 : ℕ) : ℝ)
  let cZ : HermLine ι := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  let cZ' : HermLine ι' := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  have hcZ' : IsSmoothHerm cZ' := isSmoothHerm_constLine c
  have hcZ : IsSmoothHerm cZ := isSmoothHerm_constLine c
  have hAN : ∀ j, IsSmoothHerm (Fin.append L' N j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hL' i
    | right i => rw [Fin.append_right]; exact hN i

  have hpf := hPF I hI K ι K' ι' κ v P' (d + 1) r G J (Fin.snoc (α := fun _ => HermLine ι) L cZ)
    (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N hb (hn ▸ hP') hZ hJ
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hcZ
      | cast i => rw [Fin.snoc_castSucc]; exact hL i)
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_last]; exact isPullHerm_constLine κ v c
      | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hLL i)
    hN

  obtain ⟨σ, hσ⟩ := exists_perm_append_snoc L' N cZ' hn
  have hcast : ∀ {m n : ℕ} (e : n = m) (M : Fin m → HermLine ι'),
      I K' ι' P' m M = I K' ι' P' n (M ∘ Fin.cast e) := by
    intro m n e M
    subst e
    rfl
  have hsmooth : ∀ j, IsSmoothHerm
      ((Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N ∘ Fin.cast hn) j) := by
    intro j
    have hall : ∀ i, IsSmoothHerm (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N i) := by
      intro i
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hcZ'
        | cast i => rw [Fin.snoc_castSucc]; exact hL' i
      | right i => rw [Fin.append_right]; exact hN i
    exact hall _
  have hleft : I K' ι' P' (d + 1 + r) (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N) =
      I K' ι' P' (d + r + 1) (Fin.snoc (α := fun _ => HermLine ι') (Fin.append L' N) cZ') := by
    rw [hcast hn, ← hσ]
    exact ((hI K' ι').1 P' (d + r + 1) _ σ hP' hsmooth).symm

  have h2 : Nat.Prime 2 := Nat.prime_two
  have hconsL := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K' ι' (I K' ι') (hI K' ι') P' (d + r)
    (Fin.append L' N) 2 hP' hAN h2).2
  have hconsR := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K ι (I K ι) (hI K ι) (imageZ v P') d L 2 hZ hL h2).2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
    exact (Real.log_pos this).ne'
  rw [hleft] at hpf
  have e1 : Real.log ((2 : ℕ) : ℝ) * ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) =
      Real.log ((2 : ℕ) : ℝ) * ((J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) *
        ptsIntegral (imageZ v P') (pot L) (fun _ => 1)) := by
    rw [← hconsL]
    refine hpf.trans ?_
    rw [hconsR]
    ring
  exact mul_left_cancel₀ hlog e1

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open Set Manifold GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

theorem exists_smooth_weight_const_near_embeddings :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F]
      [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ), (∀ sg, 0 < Λ sg) →
      (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) →
      ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ,
        LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg := by
  intro K _ ι _ Ω _ F _ _ _ y Λ hpos huniq
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg =>
    {z | z ∈ mcPts (mCoordIdeal y) ∧ LiesOver y sg z}
  let C : (F →+* ℂ) → Set ((Σ k, ι k × ι k) → ℂ) := fun sg => projPt '' S sg
  have hSmul : ∀ sg z (c : K → ℂ), (∀ k, c k ≠ 0) → z ∈ S sg → (fun p => c p.1 * z p) ∈ S sg :=
    fun sg z c hc hz => ⟨mcPts_smul (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz.1,
      liesOver_smul hz.2 c⟩
  have hC : ∀ sg, IsCompact (C sg) := by
    intro sg
    have hK : IsCompact (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
      have : S sg ∩ {z | ∀ k, blockNormSq z k = 1} =
          ({z | ∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom ℂ) f) = 0} ∩
            {z | LiesOver y sg z}) ∩ {z | ∀ k, blockNormSq z k = 1} := by
        ext z
        simp only [S, mcPts, mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
          by_contra hcon
          push_neg at hcon
          have := h3 k
          simp [blockNormSq, hcon] at this
      rw [this]
      exact ((isClosed_zeros _).inter (GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg)).inter
        isCompact_sphere.isClosed
    have heq : C sg = projPt '' (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine Subset.antisymm ?_ (image_mono inter_subset_left)
      rintro e ⟨z, hz, rfl⟩
      obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1.1
      exact ⟨_, ⟨hSmul sg z c hc hz, hc1⟩, projPt_smul c hc z⟩
    rw [heq]
    exact hK.image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hdisj : ∀ sg tg, sg ≠ tg → Disjoint (C sg) (C tg) := by
    intro sg tg hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨hzP, hzs⟩, rfl⟩ ⟨w, ⟨hwP, hwt⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (liesOver_smul hzs c) hwt)
  have hsep : ∀ sg, ∃ χ : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ᶠ e in 𝓝ˢ (⋃ tg ∈ Finset.univ.erase sg, C tg), χ e = 0) ∧
      (∀ᶠ e in 𝓝ˢ (C sg), χ e = 1) := by
    intro sg
    obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
      (isClosed_biUnion_finset fun tg _ => (hC tg).isClosed) (hC sg).isClosed
      (Set.disjoint_iUnion₂_left.2 fun tg htg => hdisj tg sg (Finset.ne_of_mem_erase htg))
    exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, h0, h1⟩
  choose χ hχs hχ0 hχ1 using hsep
  let g : ((Σ k, ι k × ι k) → ℂ) → ℝ := fun e => ∑ sg, Real.log (Λ sg) * χ sg e
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    ContDiff.sum fun sg _ => contDiff_const.mul (hχs sg)
  have hloc : ∀ sg, ∀ e ∈ C sg, ∀ᶠ e' in 𝓝 e, g e' = Real.log (Λ sg) := by
    intro sg e he
    have : ∀ tg, ∀ᶠ e' in 𝓝 e, χ tg e' = if tg = sg then 1 else 0 := by
      intro tg
      by_cases htg : tg = sg
      · subst htg
        simpa using (hχ1 tg).filter_mono (nhds_le_nhdsSet he)
      · simp only [htg, if_false]
        exact (hχ0 tg).filter_mono (nhds_le_nhdsSet
          (Set.mem_iUnion₂.2 ⟨sg, Finset.mem_erase.2 ⟨Ne.symm htg, Finset.mem_univ _⟩, he⟩))
    filter_upwards [Filter.eventually_all.2 this] with e' he'
    simp only [g, he', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let u : ((Σ k, ι k) → ℂ) → ℝ := fun z => g (projPt z)
  have hu_smul : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
      (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z := by
    intro c z hc
    simp only [u, projPt_smul c hc]
  refine ⟨HermLine.ofWeight (fun z => -u z) hu_smul, rfl, ?_, ?_⟩
  · have h1 := hg.comp_contDiffOn (contDiffOn_projPt (ι := ι))
    have hu := h1.neg.neg
    exact Real.contDiff_exp.comp_contDiffOn hu
  · intro z hz sg hsg
    have hzC : projPt z ∈ C sg := ⟨z, ⟨hz, hsg⟩, rfl⟩
    have hcont : ContinuousAt projPt z :=
      contDiffOn_projPt.continuousOn.continuousAt (GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isOpen_blockNonzero.mem_nhds hz.1)
    filter_upwards [Filter.Tendsto.eventually hcont (hloc sg _ hzC)] with w hw1
    change Real.exp (-(-u w)) = Λ sg
    simp only [u, hw1, neg_neg, Real.exp_log (hpos sg)]

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntryStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pMat_stepCols_entry : ∀ (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep), j ≤ N → keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧ ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 → pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibility
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem re_pot : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly :=
  @PositivityTheory.Xgp.t_re_pot

end GlobalTheory.CompanionTheory.Ar.PB
end

