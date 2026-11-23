module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.StdLoc

theorem idx_alg (q : ℝ) (hq : q ≠ 0) (c a a' : ℕ) :
    q ^ (c * (a + a') ^ 2) * glVol q (a + a') /
      (q ^ (c * a ^ 2) * glVol q a * (q ^ (c * a' ^ 2) * glVol q a') * (q ^ c) ^ (a * a')) = blockIdx q c a a' := by
  rw [blockIdx]
  have e : c * (a + a') ^ 2 = c * a ^ 2 + c * a' ^ 2 + c * a * a' + c * a * a' := by ring
  have e2 : (q ^ c) ^ (a * a') = q ^ (c * a * a') := by rw [← pow_mul, mul_assoc]
  rw [e, pow_add, pow_add, pow_add, e2]
  have h1 : q ^ (c * a ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (c * a' ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h3 : q ^ (c * a * a') ≠ 0 := pow_ne_zero _ hq
  by_cases ha : glVol q a = 0
  · simp [ha]
  by_cases hb : glVol q a' = 0
  · simp [hb]
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

theorem glVol_add (q : ℝ) (a' a : ℕ) :
    glVol q (a' + a) = glVol q a' * ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, glVol, Finset.prod_Icc_succ_top (by omega), ← glVol, ih, Finset.prod_Icc_succ_top (by omega), mul_assoc, add_assoc]

theorem glVol_pos {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < glVol q n :=
  Finset.prod_pos fun i hi => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by simp at hi; omega)))

theorem stdLoc_product {q : ℝ} (hq : 1 < q) (c a a' : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹))⁻¹ * blockIdx q c a a' * ((q ^ (c * a * a'))⁻¹ * glVol q a) = 1 := by
  have h1 := glVol_pos hq a
  have h2 := glVol_pos hq a'
  have h3 : (0 : ℝ) < q ^ (c * a * a') := pow_pos (by linarith) _
  have h4 : 0 < ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
    have := glVol_add q a' a
    have h5 := glVol_pos hq (a' + a)
    rw [this] at h5
    exact pos_of_mul_pos_right h5 h2.le
  rw [blockIdx, add_comm a a', glVol_add]
  generalize ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) = P at h4 ⊢
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

open UniqueFactorizationMonoid

theorem absNorm_eq_prod {E : Type} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm 𝔪 : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset, (Ideal.absNorm w : ℝ) ^ (normalizedFactors 𝔪).count w := by
  have h1 : (normalizedFactors 𝔪).prod = 𝔪 := by
    have := prod_normalizedFactors h𝔪
    exact associated_iff_eq.1 this
  conv_lhs => rw [← h1]
  rw [map_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
  simp

theorem relIndex_blockLevel {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ)
    (h𝔪 : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (ha : a ≤ P.d) (hJ : IsBlockLevel P 𝔪 a) :
    ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a (P.d - a) := by
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.LevelRed.exists_levelRed D 𝔪 h𝔪 P.d
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪) (((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) = ((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    have h2 := _root_.GlobalTheory.MaxLevelLift.exists_intG_cong D 𝔪 h𝔪 hcop P.d (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    obtain ⟨k, hk, hk'⟩ := h2
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)
  have hsub : P.J.subgroupOf (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).comap ρ := by
    have h0 : ∀ x : AE D, x - inc D ((0 : 𝓞 D.host.E) : D.host.E) = x := fun x => by simp
    refine Subgroup.ext fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (k : GA D P.d) ∈ P.J := h
      show ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d
      refine (mem_blockPar _).2 fun i j hj hi => ?_
      have h1 := ((hJ _).1 h').2 i j hj hi
      rw [← h0 ((((k : GA D P.d) : GL (Fin P.d) (AE D)) : Matrix (Fin P.d) (Fin P.d) (AE D)) i j)] at h1
      exact ((hρ k i j 0).2 h1).trans (map_zero _)
    · have h' : ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d := h
      show (k : GA D P.d) ∈ P.J
      refine (hJ _).2 ⟨k.2, fun i j hj hi => ?_⟩
      have h1 := (hρ k i j 0).1 (((mem_blockPar _).1 h' i j hj hi).trans (map_zero _).symm)
      rwa [h0] at h1
  have hR : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hR]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  have hidx : P.J.relIndex (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index := by
    show (P.J.subgroupOf (intG D P.d)).index = _
    rw [hsub, Subgroup.index_comap_of_surjective _ hsurj]
  have hcm := (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).card_mul_index
  have hP0 : (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hI : ((blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index : ℝ) =
      (Nat.card (GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : ℝ) / (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) := by
    rw [eq_div_iff hP0, mul_comm]; exact_mod_cast hcm
  rw [hidx, hI, GlobalTheory.T.card_blockParabolicSubgroupGL _ a P.d ha, hR]
  push_cast
  rw [_root_.GlobalTheory.CardGLQuot.card_GL_quot_prod _ 𝔪 h𝔪, _root_.GlobalTheory.CardGLQuot.card_GL_quot_prod _ 𝔪 h𝔪, _root_.GlobalTheory.CardGLQuot.card_GL_quot_prod _ 𝔪 h𝔪, absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
  rw [ha', Nat.add_sub_cancel_left]
  exact idx_alg _ hq _ _ _

end GlobalTheory.StdLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.ThetaSchurF

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem half_add_half (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y = symplOF σ JS JT ξ₀ x y := by
  simp only [symplOHF, ← add_mul, ← map_add (f := _)]
  norm_num

theorem symplOF_add_left (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  simp only [symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOF_add_right (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  simp only [symplOF, hOF, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOF_zero_right (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  simp [symplOF, hOF]

theorem continuous_symplOF_left (y : WOF F E nS nT) : Continuous fun x => symplOF σ JS JT ξ₀ x y := by
  have h := GlobalTheory.HeisThetaF.continuous_symplOHF_left (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) y
  have e : (fun x => symplOF σ JS JT ξ₀ x y) = fun x => symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y :=
    funext fun x => (half_add_half x y).symm
  rw [e]
  exact h.add h

theorem mul_star_psi (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF F) : ψ a * star (ψ a) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hψ a]
  simp

theorem heis_rat (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT)
    (x : WOF F E nS nT) : heisOF σ JS JT ξ₀ ψ γ f x = ψ (symplOF σ JS JT ξ₀ x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have hs : symplOHF σ JS JT ξ₀ (ratWF γ) x = -symplOHF σ JS JT ξ₀ x (ratWF γ) := by
    simp only [symplOHF]
    rw [hskew, mul_neg]
  show ψ (symplOHF σ JS JT ξ₀ x (ratWF γ)) * f (x + ratWF γ) = ψ (symplOF σ JS JT ξ₀ x (ratWF γ)) * f x
  rw [add_comm x, hf.quasi, hs, neg_neg, ← mul_assoc, ← AddChar.map_add_eq_mul, half_add_half]

theorem prod_periodic (hψ : ∀ a, ‖ψ a‖ = 1) {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f)
    (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT) (x : WOF F E nS nT) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratWF γ + x) * star (f' (ratWF γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x))

theorem scalar_eq (hψ : ∀ a, ‖ψ a‖ = 1) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ)
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hn : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    (f f' : WOF F E nS nT → ℂ) (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') :
    ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ (g : WOF F E nS nT → ℂ), g ∈ GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C :=
    fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => by
      have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
        rintro _ ⟨γ, rfl⟩ w
        exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ, one_mul])
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
      refine ⟨C, fun w => ?_⟩
      obtain ⟨γ, hγ, h⟩ := hKc w
      rw [← hp γ hγ w]
      exact hC _ h
  exact GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => hg.cont.measurable) hb M hM hn f f' hf hf'

theorem prod_eq (hψ : IsCharAF F ψ)
    (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    (hann : ∀ x : WOF F E nS nT, (∀ γ ∈ ratLF F E nS nT, ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT)
    (hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w f))
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hc : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → M (heisOF σ JS JT ξ₀ ψ w f) = heisOF σ JS JT ξ₀ ψ w (M f))
    (hn : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f →
        ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f')
    (x : WOF F E nS nT) : M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hint : ∀ g g', IsThetaFunOF σ JS JT ξ₀ ψ g → IsThetaFunOF σ JS JT ξ₀ ψ g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ.2.1 hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WOF F E nS nT) (ratLF F E nS nT) K hK hKc
    (ratLF F E nS nT) (fun γ x => ψ (symplOF σ JS JT ξ₀ x γ))
    (fun γ => hψ.1.comp (continuous_symplOF_left _))
    (fun γ x y => by simp only [symplOF_add_left, AddChar.map_add_eq_mul])
    (fun γ γ' x => by simp only [AddSubgroup.coe_add, symplOF_add_right, AddChar.map_add_eq_mul])
    (fun x => by simp only [AddSubgroup.coe_zero, symplOF_zero_right, AddChar.map_zero_eq_one])
    (fun γ x => hψ.2.1 _)
    (fun x => by
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by
      rw [prod_periodic hψ.2.1 hf hf' hγ, prod_periodic hψ.2.1 (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplOF σ JS JT ξ₀ x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisOF σ JS JT ξ₀ ψ γ f) x * star (M f' x) - heisOF σ JS JT ξ₀ ψ γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heis_rat hskew hf γ.2, heis_rat hskew (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

end Lemmas

theorem schur : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := _root_.GlobalTheory.SymplSkew.symplOF_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := _root_.GlobalTheory.RatAnnihF.ratLF_annihilator F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchurF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePull

theorem unimod_comap_frame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  intro D V fr Λ hG hΛ v
  have hstar : ∀ x : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = x) → ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x := by
    rintro x ⟨b, rfl⟩
    exact ⟨Formalism.L2.Pj.barE D b, Formalism.L2.Pj.barE_eq_star D b⟩
  have hcT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 = fr.1ᴴ := by
    ext i j
    rfl
  have key : ∀ w : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star ((fr.1 *ᵥ w) i) * V.gram i j * (fr.1 *ᵥ v) j = ∑ j, star (w j) * v j := by
    intro w
    have e1 : ∀ x y : Fin V.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
      intro x y
      simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rfl
    rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← hcT, hG, Matrix.one_mulVec]
    rfl
  have hsum : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (w j) * v j) = ∑ j, star (v j) * w j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hsum' : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (v j) * w j) = ∑ j, star (w j) * v j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  change fr.1 *ᵥ v ∈ Λ ↔ ∀ w, fr.1 *ᵥ w ∈ Λ → ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j
  rw [hΛ.2]
  constructor
  · intro H w hw
    have := hstar _ (H _ hw)
    rwa [key, hsum] at this
  · intro H x hx
    have hw : fr.1 *ᵥ ((fr⁻¹).1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := hstar _ (H ((fr⁻¹).1 *ᵥ x) (by rw [hw]; exact hx))
    rw [hsum', ← key, hw] at this
    exact this

end GlobalTheory.FramePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewSelfDual_lattice_localised_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl (F := F)) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  first | exact @GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | exact GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | (intros; apply GlobalTheory.SkewLocDual.exists_smul_mem_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PsiFinRat

theorem psi_pairA_zero_algebraMap {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  obtain ⟨hchar, ⟨θ, hθ⟩, hall⟩ := hψ
  have hinf := hall θ hθ
  have hsplit : pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q) =
      algebraMap D.host.F (AF D.host.F) q +
        pairA D.host.F (-(algebraMap D.host.F (Ainf D.host.F) q)) 0 := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = algebraMap D.host.F (Ainf D.host.F) q + -(algebraMap D.host.F (Ainf D.host.F) q)
      rw [add_neg_cancel]
    · show algebraMap D.host.F (Af D.host.F) q = algebraMap D.host.F (Af D.host.F) q + 0
      rw [add_zero]
  rw [hsplit, AddChar.map_add_eq_mul, hchar.2.2.1, one_mul]
  have h1 := hinf (-(algebraMap D.host.F (Ainf D.host.F) q))
  simp only [psiInf] at h1
  rw [h1]
  have htm : ∀ τ, θ τ ((-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -tauE D τ (q : D.host.E) := by
    intro τ
    have e : (-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        -((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q)) := by
      have e0 : (algebraMap D.host.F (Ainf D.host.F) q) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q) :=
        (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes q |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F)
            (B := D.host.E)).commutes q).symm
      rw [TensorProduct.neg_tmul, e0]
    rw [e, map_neg, (hθ τ).1]
    rfl
  simp only [htm, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

end GlobalTheory.PsiFinRat
end
end

