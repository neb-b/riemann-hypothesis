module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjNormalizerEqConstMulHaar
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem lintegral_conj_eq_const_mul :
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure N) (b : G), IsClosed (N : Set G) → ν.IsHaarMeasure → (∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) → ∃ κ : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N ν b hN hν h
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let e := GlobalTheory.ResLine.conjNormalEquiv N b h
  haveI : (ν.map e).IsHaarMeasure := e.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map e) ν
  have he : Measurable e := e.continuous.measurable
  refine ⟨(Measure.haarScalarFactor (ν.map e) ν : ℝ≥0∞), fun g hg => ?_⟩
  have hg' : Measurable fun u : N => g u := hg.comp measurable_subtype_coe
  have h1 := lintegral_map (μ := ν) hg' he
  rw [hc, lintegral_smul_measure] at h1
  exact h1.symm

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTwoStepUnfoldingSemidirectLattice
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem countable_subgroupOf_of_countable {G : Type} [Group G] (Λ M : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf M) := by
  refine Function.Injective.countable (f := fun δ : Λ.subgroupOf M => (⟨δ.1.1, δ.2⟩ : Λ)) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun l : Λ => (l : G)) h))

theorem tsum_split_lattice {G : Type} [Group G] (N M Λ : Subgroup G) (disj : ∀ g ∈ N, g ∈ M → g = 1)
    (dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m) (f : G → ℝ≥0∞) :
    ∑' δ : Λ.subgroupOf M, ∑' γ : Λ.subgroupOf N, f ((γ.1 : G) * (δ.1 : G)) = ∑' l : Λ, f l := by
  let p : Λ.subgroupOf M × Λ.subgroupOf N → Λ := fun z => ⟨(z.2.1 : G) * (z.1.1 : G), Λ.mul_mem z.2.2 z.1.2⟩
  have hb : Function.Bijective p := by
    constructor
    · rintro ⟨δ, γ⟩ ⟨δ', γ'⟩ h
      have h1 : (γ.1 : G) * (δ.1 : G) = (γ'.1 : G) * (δ'.1 : G) := congrArg Subtype.val h
      have h2 : (γ'.1 : G)⁻¹ * γ.1 = (δ'.1 : G) * (δ.1 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : (γ'.1 : G)⁻¹ * γ.1 = 1 :=
        disj _ (N.mul_mem (N.inv_mem γ'.1.2) γ.1.2) (h2 ▸ M.mul_mem δ'.1.2 (M.inv_mem δ.1.2))
      have h4 : (γ'.1 : G) = γ.1 := inv_mul_eq_one.1 h3
      have h5 : (δ.1 : G) = δ'.1 := by rw [h4] at h1; exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext (Subtype.ext h5)) (Subtype.ext (Subtype.ext h4.symm))
    · rintro ⟨l, hl⟩
      obtain ⟨u, hu, m, hm, hu', hm', e⟩ := dec l hl
      exact ⟨(⟨⟨m, hm⟩, hm'⟩, ⟨⟨u, hu⟩, hu'⟩), Subtype.ext e.symm⟩
  rw [← ENNReal.tsum_prod, ← (Equiv.ofBijective p hb).tsum_eq]
  rfl

theorem lintegral_two_step_unfolding : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ x in D, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π ∂μ = ν DN * π DM * ∫⁻ x, φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM S μ D hμ hD φ hφ
  haveI := countable_subgroupOf_of_countable Λ M
  haveI := countable_subgroupOf_of_countable Λ N
  haveI : LocallyCompactSpace N := S.closedN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := S.closedM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := S.haarN
  haveI := S.haarM
  have hN := (_root_.GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold N ν (Λ.subgroupOf N) DN S.haarN S.domN S.finN).2
  have hM := (_root_.GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold M π (Λ.subgroupOf M) DM S.haarM S.domM S.finM).2
  have hC := _root_.GlobalTheory.ResLine.lintegral_conj_eq_of_semiLat G N M Λ ν π DN DM S
  have A : ∀ x : G, ∫⁻ m : M, ∫⁻ u : N, φ (u * m * x) ∂ν ∂π =
      ∫⁻ b in DM, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂π := by
    intro x
    rw [hM _ (Measurable.lintegral_prod_right' (f := fun z : M × N => φ (z.2 * z.1 * x)) (hφ.comp (by fun_prop)))]
    refine lintegral_congr fun b => ?_
    have h1 : ∀ δ : Λ.subgroupOf M, ∫⁻ u : N, φ (u * ((b⁻¹ * δ : M) : G) * x) ∂ν =
        ∫⁻ c in DN, ∑' γ : Λ.subgroupOf N, φ ((b : G)⁻¹ * (c : G)⁻¹ * ((γ.1 : G) * (δ.1 : G) * x)) ∂ν := by
      intro δ
      have h2 := hC b b.2 (fun g => φ ((b : G)⁻¹ * g * δ.1 * x)) (hφ.comp (by fun_prop))
      have h3 := hN (fun u : N => φ ((b : G)⁻¹ * u * δ.1 * x)) (hφ.comp (by fun_prop))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] at h2 h3 ⊢
      rw [h2, h3]
    simp only [h1]
    rw [← lintegral_tsum]
    swap
    · exact fun δ => (Measurable.tsum fun γ => hφ.comp (by fun_prop)).aemeasurable
    refine lintegral_congr fun c => ?_
    exact tsum_split_lattice N M Λ S.disj S.dec fun g => φ ((b : G)⁻¹ * (c : G)⁻¹ * (g * x))
  simp only [A]
  have B : ∀ y : G, ∫⁻ x in D, ∑' l : Λ, φ (y * (l * x)) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro y
    rw [lintegral_tsum, ← lintegral_mul_left_eq_self φ y,
      hD.lintegral_eq_tsum'' fun x => φ (y * x)]
    · rfl
    · exact fun l => (hφ.comp (by fun_prop)).aemeasurable
  rw [lintegral_lintegral_swap (Measurable.aemeasurable (Measurable.lintegral_prod_right'
    (f := fun z : (G × M) × N => ∑' l : Λ, φ ((z.1.2 : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1.1)))
    (Measurable.tsum fun γ => hφ.comp (by fun_prop))))]
  have C : ∀ b : M, ∫⁻ x in D, ∫⁻ c in DN, ∑' l : Λ, φ ((b : G)⁻¹ * (c : G)⁻¹ * (l * x)) ∂ν ∂μ =
      ν DN * ∫⁻ x, φ x ∂μ := by
    intro b
    rw [lintegral_lintegral_swap (Measurable.aemeasurable
      (f := fun z : G × N => ∑' l : Λ, φ ((b : G)⁻¹ * (z.2 : G)⁻¹ * (l * z.1)))
      (Measurable.tsum fun γ => hφ.comp (by fun_prop)))]
    simp only [B]
    rw [setLIntegral_const, mul_comm]
  simp only [C]
  rw [setLIntegral_const]
  ring

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventually
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory

theorem eq_one_of_forall_norm_pow_sub_one_lt (w : ℂ) (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2) : w = 1 := by
  by_contra hw
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
  have hre : ∀ k : ℕ, 1 / 2 < (w ^ k).re := by
    intro k
    have h1 := (Complex.abs_re_le_norm (w ^ k - 1)).trans_lt (h k)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_lt.1 h1).1]
  have hsum : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, w ^ k).re := by
    rw [Complex.re_sum]
    have := Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hre k).le)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hnorm : (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, w ^ k‖ :=
    hsum.trans (Complex.re_le_norm _)
  have hgeom : ‖∑ k ∈ Finset.range N, w ^ k‖ * ‖w - 1‖ < 1 / 2 := by
    rw [← norm_mul, geom_sum_mul]; exact h N
  have : (N : ℝ) / 2 * ‖w - 1‖ < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm hd.le) hgeom
  have h2 : (N : ℝ) * ‖w - 1‖ < 1 := by linarith
  rw [div_lt_iff₀ hd] at hN
  linarith


open Filter Topology in
theorem psiLoc_eventually_trivial_integers {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) :
    ∀ᶠ v in Filter.cofinite, ∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1 := by
  classical
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F)
      (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
        (fun v => ⟨(y v).1, (y v).2⟩))
  have hι : Continuous ι := by
    have hs : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) =>
        RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
          (fun v => ⟨(y v).1, (y v).2⟩)) :=
      RestrictedProduct.isEmbedding_structureMap.continuous
    exact continuous_const.prodMk hs
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      refine Prod.ext rfl ?_
      show RestrictedProduct.structureMap _ _ _ _ = (0 : Af F)
      refine af_ext fun w => ?_
      rfl
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  have key : ∀ v, v ∉ I → ∀ x ∈ v.adicCompletionIntegers F, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x - 1‖ < 1 / 2 := by
    intro v hv x hx
    let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨x, hx⟩
    have hy : y ∈ (I : Set _).pi u := by
      intro a ha
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      have : y a = 0 := Pi.single_eq_of_ne hav _
      rw [this]; exact (hu a ha).2
    have hmem := hsub hy
    have hιy : ι y = LinearMap.inr F (Ainf F) (Af F) (singleFin v x) := by
      refine congrArg (LinearMap.inr F (Ainf F) (Af F)) (af_ext fun w => ?_)
      by_cases e : w = v
      · subst e; rw [evalV_singleFin_self]
        show ((y w : w.adicCompletion F)) = x
        simp [y]
      · rw [evalV_singleFin_ne e]
        show ((y w : w.adicCompletion F)) = 0
        simp [y, Pi.single_eq_of_ne e]
    simpa [hιy, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc] using hmem
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ x ∈ v.adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1}.Finite := by
    refine (I.finite_toSet).subset fun v hv => ?_
    by_contra hvI
    apply hv
    intro x hx
    refine eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_
    have hnx : n • x ∈ v.adicCompletionIntegers F := nsmul_mem hx n
    have := key v hvI (n • x) hnx
    have hpow : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (n • x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x ^ n := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc, map_nsmul]
      exact AddChar.map_nsmul_eq_pow ψ n _
    rwa [hpow] at this
  exact Filter.eventually_cofinite.2 hfin

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockMem

variable {D : D7}

theorem hatId_mul_mem (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ hatId D 𝔪) (hy : y ∈ OhE D) :
    x * y ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => simp [zero_mem]
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def hatIdeal (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Ideal (OhE D) where
  carrier := {x | (x : AE D) ∈ hatId D 𝔪}
  add_mem' := fun {x y} hx hy => by
    show ((x : AE D) + (y : AE D)) ∈ hatId D 𝔪
    exact add_mem hx hy
  zero_mem' := by
    show ((0 : OhE D) : AE D) ∈ hatId D 𝔪
    exact zero_mem _
  smul_mem' := fun c x hx => by
    show (c : AE D) * (x : AE D) ∈ hatId D 𝔪
    rw [mul_comm]; exact hatId_mul_mem 𝔪 hx c.2

def liftM {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    Matrix (Fin d) (Fin d) (OhE D) :=
  Matrix.of fun i j => ⟨g i j, hg i j⟩

theorem liftM_map {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    (liftM g hg).map (OhE D).subtype = g := by
  ext i j; rfl

def blk (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

theorem blk_lt {a d : ℕ} (i j : Fin d) : blk a j < blk a i ↔ j.1 < a ∧ a ≤ i.1 := by
  unfold blk; split_ifs <;> omega

theorem cond_iff {d : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ) (g : Matrix (Fin d) (Fin d) (AE D))
    (hg : ∀ i j, g i j ∈ OhE D) :
    (∀ i j : Fin d, j.1 < a → a ≤ i.1 → g i j ∈ hatId D 𝔪) ↔
      ((liftM g hg).map (Ideal.Quotient.mk (hatIdeal D 𝔪))).BlockTriangular (blk a) := by
  constructor
  · intro h i j hij
    rw [blk_lt] at hij
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h i j hij.1 hij.2
  · intro h i j hj hi
    have := h ((blk_lt i j).2 ⟨hj, hi⟩)
    simp only [Matrix.map_apply] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this

theorem bt_transfer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    {X Y : Matrix (Fin d) (Fin d) R} (h : Y * X = 1) (b : Fin d → ℕ) (hX : (X.map f).BlockTriangular b) :
    (Y.map f).BlockTriangular b := by
  have h' : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ f.map_zero f.map_one]
  letI : Invertible (X.map f) := ⟨Y.map f, h', mul_eq_one_comm.mp h'⟩
  have := Matrix.blockTriangular_inv_of_blockTriangular hX
  rwa [Matrix.inv_eq_left_inv h'] at this

theorem mem_iff (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d) :
    h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  refine ⟨fun hh => ?_, fun hh => Subgroup.subset_closure hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hne : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hne, zero_mem]
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have iy := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · exact hatId_mul_mem 𝔪 (hx.2 i l hl hi) (iy l j).1
    · rw [mul_comm]
      exact hatId_mul_mem 𝔪 (hy.2 l j hj (not_lt.1 hl)) (ix i l).1
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hX : ∀ i j, ((x : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => (ix i j).1
    have hY : ∀ i j, (((x⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => by simpa using (ix i j).2
    rw [cond_iff 𝔪 a _ hY]
    have hXc := (cond_iff 𝔪 a _ hX).1 hx.2
    set X := liftM _ hX
    set Y := liftM _ hY
    have hYX : Y * X = 1 := by
      have key : (Y * X).map (OhE D).subtype = (1 : Matrix (Fin d) (Fin d) (OhE D)).map (OhE D).subtype := by
        rw [Matrix.map_mul, liftM_map, liftM_map, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      exact Matrix.map_injective (fun u v huv => Subtype.ext huv) key
    exact bt_transfer (Ideal.Quotient.mk (hatIdeal D 𝔪)) hYX (blk a) hXc

end GlobalTheory.FunObj.StdDatum.BlockMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem mem_unipRad_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr u
  have hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    simp only [adMat]; exact Matrix.map_mul
  have hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) =
      adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
    have e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) =
        C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
      rw [← fr.sum]; abel
    rw [e, ← hmap, ← hmap]
    simp only [adMat]; exact Matrix.map_add _ (map_add _) _ _
  have hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]
  have hdual : u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin j) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J u).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
    constructor
    · intro hg
      simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
        sub_eq_iff_eq_add, zero_add]
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨h1, -, h3⟩ := hg
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, fr.cd, Matrix.mul_one, Matrix.one_mul, sub_self]
        choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
          (funext fun j => congrFun (congrFun hT j) k)
        refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
        rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
        ext i k
        exact congrFun (ha k) i
      | one => exact ⟨by simp, 0, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a1, A, a2⟩ := ha
        obtain ⟨b1, B, b2⟩ := hb
        refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
        rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
          add_assoc]
      | inv a _ ha =>
        obtain ⟨a1, A, a2⟩ := ha
        have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
          conv_lhs => rw [← a1]
          rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        refine ⟨i1, -A, ?_⟩
        have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
        rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
          inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
        rw [Matrix.mul_neg]
        conv_rhs => rw [this]
        abel
    · rintro ⟨h1, B, h2⟩
      refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
      · have hg : cT (sigR (AF F) σ) (matHom _ σ J u).1 * adMat F J * (matHom _ σ J u).1 = adMat F J := u.2
        have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
        conv_lhs => rw [← h1, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J u).1)]
        exact congrArg _ hg
      · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
            fun i => inclR (F := F) (AF F) (x i) := by
          funext i
          have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
          rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
          exact this.symm
        rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]
  rw [hdual]
  set M := (matHom _ σ J u).1
  constructor
  · rintro ⟨h1, B, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩
    have := congrArg (· * adMat F Z) h2
    rw [Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc] at this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rintro ⟨h1, b, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩
    have h1' : (M - 1) * adMat F C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    have h2' : (M - 1) * adMat F Z = adMat F C * b := by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]

end GlobalTheory.SphEis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreVanishingLineBundleInvMixFixedDifferenceStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ d : ℤ, ∃ N : ℕ, ∀ a b : ℕ, N ≤ a + b → (a : ℤ) - b = d → ∀ j : ℕ, ¬ NV A (mix A L a b) (j + 1) := by
  first | exact @GlobalTheory.AmpleGen.exists_not_NV_mix | exact GlobalTheory.AmpleGen.exists_not_NV_mix | (intros; apply GlobalTheory.AmpleGen.exists_not_NV_mix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentativesStatement
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_tsum_unfold_of_cosetRepresentatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G), μ.IsHaarMeasure → Λ ≤ Γ → (∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) → IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Λ D μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  first | exact @GlobalTheory.ResLine.setLIntegral_tsum_unfold | exact GlobalTheory.ResLine.setLIntegral_tsum_unfold | (intros; apply GlobalTheory.ResLine.setLIntegral_tsum_unfold <;> assumption)
end

