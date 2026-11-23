module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId
section
open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentatives
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem repsBuild : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ N hN
  classical
  set t : GL (A ⊕ D) k := mtor ϖ (indic s) with ht
  let f : (Σ _ : GL D k, Matrix D A k) → GL (A ⊕ D) k :=
    fun x => lowU x.2 * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ x.1)

  have key : ∀ g₁ ∈ R, ∀ ν₁ ∈ N g₁, ∀ g₂ ∈ R, ∀ ν₂ ∈ N g₂,
      (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D → g₁ = g₂ ∧ ν₁ = ν₂ := by
    intro g₁ hg₁ ν₁ hν₁ g₂ hg₂ ν₂ hν₂ h
    obtain ⟨rfl, μ, hμ, hdiff⟩ := _root_.GlobalTheory.CosetDistinct.coset_uniq k A D ϖ hϖ s R hR κ κ' hκ g₁ hg₁ g₂ hg₂ ν₁ ν₂ h
    refine ⟨rfl, ?_⟩
    obtain ⟨hsmall, huniq⟩ := hN g₁ hg₁
    obtain ⟨ν', _, hν'⟩ := huniq ν₂ (hsmall ν₂ hν₂)
    have e2 : ν₂ = ν' := hν' ν₂ ⟨hν₂, 0, fun i a => by simp, by simp⟩
    have e1 : ν₁ = ν' := hν' ν₁ ⟨hν₁, μ, hμ, hdiff⟩
    rw [e1, e2]
  refine ⟨(R.sigma N).image f, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨⟨g, ν⟩, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_sigma] at hx
    obtain ⟨hg, hν⟩ := hx
    refine ⟨Subgroup.mul_mem _ (lowU_mem ((hN g hg).1 ν hν)) (emb_mem (hκ g hg).1), ?_⟩
    have h22 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)).1.toBlocks₂₂ = (κ g).1 := by
      rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
    show ((blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) : kˣ) : k) = _
    rw [blockDet_lowU_emb, h22, GeneralLinearGroup.val_det_apply]
  · intro j hj
    obtain ⟨g, hg, ν₀, hν₀, hall⟩ := _root_.GlobalTheory.LowerHecke.exists_lowU_diag_coset k A D ϖ hϖ s R hR κ κ' hκ j hj
    obtain ⟨ν', ⟨hν'N, μ, hμ, hdiff⟩, -⟩ := (hN g hg).2 ν₀ hν₀
    refine ⟨f ⟨g, ν'⟩, ⟨Finset.mem_image.2 ⟨(⟨g, ν'⟩ : Σ _ : GL D k, Matrix D A k), Finset.mem_sigma.2 ⟨hg, hν'N⟩, rfl⟩,
      hall ν' ⟨μ, hμ, hdiff⟩⟩, ?_⟩
    rintro j' ⟨hj', hmem⟩
    obtain ⟨⟨g₂, ν₂⟩, hx, rfl⟩ := Finset.mem_image.1 hj'
    rw [Finset.mem_sigma] at hx
    have hmem' : (f ⟨g, ν'⟩ * t)⁻¹ * (j * t) ∈ parahoric k A D := hall ν' ⟨μ, hμ, hdiff⟩
    have hc : (f ⟨g₂, ν₂⟩ * t)⁻¹ * (f ⟨g, ν'⟩ * t) ∈ parahoric k A D := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hmem')
      simpa [mul_assoc] using this
    obtain ⟨rfl, rfl⟩ := key g₂ hx.1 ν₂ hx.2 g hg ν' hν'N hc
    rfl
  · intro F
    rw [Finset.sum_image, Finset.sum_sigma]
    rintro ⟨g₁, ν₁⟩ h₁ ⟨g₂, ν₂⟩ h₂ heq
    rw [Finset.coe_sigma, Set.mem_sigma_iff] at h₁ h₂
    have hc : (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D := by
      rw [show f ⟨g₁, ν₁⟩ = f ⟨g₂, ν₂⟩ from heq, inv_mul_cancel]; exact Subgroup.one_mem _
    obtain ⟨rfl, rfl⟩ := key g₁ h₁.1 ν₁ h₁.2 g₂ h₂.1 ν₂ h₂.2 hc
    rfl

end GlobalTheory.LowerHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOneOfGood
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_weierstrassP_sub_eq_one_of_good :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 →
      ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → u + v ∉ L.lattice →
      u - v ∉ L.lattice → ‖ι (L.weierstrassP u)‖ ≤ 1 → ‖ι (L.weierstrassP v)‖ ≤ 1 →
      ‖ι (L.weierstrassP (u + v))‖ ≤ 1 → ‖ι (L.weierstrassP (u - v))‖ ≤ 1 →
      ‖ι (L.weierstrassP u) - ι (L.weierstrassP v)‖ = 1 := by
  intro L l _ hl ι hg2 hg3 hD u v hu hv huv hmuv hpu hpv hpuv hpmuv
  have hgood : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hg2
    · simpa using hg3
    · rw [map_sub, map_pow, map_mul, map_pow, map_ofNat]; exact hD
  have hred : ∀ z, z ∉ L.lattice → ‖ι (L.weierstrassP z)‖ ≤ 1 → GlobalTheory.Klein.Red ι L 0 z :=
    fun z hz hp => ⟨hz, by simpa using hp⟩
  have h := GlobalTheory.Klein.norm_weierstrassP_sub_eq_one l ι L 0 hgood u v (hred u hu hpu) (hred v hv hpv)
    (hred _ huv hpuv) (hred _ hmuv hpmuv)
  simpa [map_sub] using h

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZero
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem omegaK_quadratic : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  intro d hd
  have h4 : 4 ∣ d + 1 := by omega
  obtain ⟨k, hk⟩ := h4
  have hk' : (d + 1) / 4 = k := by omega
  rw [hk']
  have hdk : (d : ℂ) = 4 * k - 1 := by
    have : ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination this
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  unfold omegaK
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeSumTermAtCosetStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_hecke_sum_term_at_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  first | exact @GlobalTheory.ParHeckeTarget.coset_term | exact GlobalTheory.ParHeckeTarget.coset_term | (intros; apply GlobalTheory.ParHeckeTarget.coset_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SegmentsBoundsAndDoublingLFactor
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun

theorem prod_map_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂˣ) (F : ℂˣ → ℂ) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add (f := _), Multiset.prod_add, ih]

variable {K : Type} [Field K] [NumberField K]

theorem prod_fin_eq {N k t : ℕ} (w : HeightOneSpectrum (𝓞 K)) (z : ℕ → ℂˣ) (α : Fin N → ℂˣ)
    (hα : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, seg w (z i) t) (F : ℂˣ → ℂ) :
    ∏ j, F (α j) =
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range t, F (z i * npowU w (((t : ℂ) - 1) / 2 - l)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun j => F (α j)) = (Finset.univ.val.map α).map F from
      (Multiset.map_map _ _ _).symm, hα, prod_map_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [seg, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

theorem re_exp (t l : ℕ) : (((t : ℂ) - 1) / 2 - l).re = ((t : ℝ) - 1) / 2 - l := by
  simp

theorem npow_neg_nat (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    npow w (-(m : ℂ)) = (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ m)⁻¹ := by
  rw [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem prod_Icc_one (t : ℕ) (g : ℕ → ℂ) : ∏ n ∈ Finset.Icc 1 t, g n = ∏ l ∈ Finset.range t, g (l + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun l _ => by rw [add_comm]

theorem entry_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) (t l : ℕ) :
    ((z * npowU w (((t : ℂ) - 1) / 2 - l) : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (l + 1))⁻¹ := by
  rw [Units.val_mul, coe_npowU, mul_assoc, show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
    npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  congr 2
  push_cast
  ring

theorem entry_inv_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) {t l : ℕ} (hl : l < t) :
    (((z * npowU w (((t : ℂ) - 1) / 2 - l))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ)⁻¹ * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (t - 1 - l + 1))⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_mul, coe_npowU, mul_inv, mul_assoc,
    show (npow w (((t : ℂ) - 1) / 2 - l))⁻¹ = npow w (-(((t : ℂ) - 1) / 2 - l)) by
      rw [npow, npow, Complex.cpow_neg],
    show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  have e : ((t - 1 - l + 1 : ℕ) : ℂ) = t - l := by
    rw [show t - 1 - l + 1 = t - l by omega, Nat.cast_sub hl.le]
  rw [e]
  congr 2
  ring

end GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun GlobalTheory.LFun.SegFactor in
theorem GlobalTheory.LFun.seg_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  intro K _ _ w k t N z hz α hα
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm w
  have mem : ∀ j, ∃ i ∈ Finset.Icc 1 k, ∃ l < t, α j = z i * npowU w (((t : ℂ) - 1) / 2 - l) := by
    intro j
    have h1 : α j ∈ Finset.univ.val.map α := Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    rw [hα] at h1
    obtain ⟨i, hi, h2⟩ := Multiset.mem_sum.1 h1
    obtain ⟨l, hl, e⟩ := Multiset.mem_map.1 h2
    exact ⟨i, hi, l, Finset.mem_range.1 hl, e.symm⟩
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨i, -, l, hl, e⟩ := mem j
    have hn : ‖(α j : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2 - l) := by
      rw [e, Units.val_mul, norm_mul, hz, one_mul, coe_npowU, norm_npow, re_exp]
    have hl' : (l : ℝ) + 1 ≤ t := by exact_mod_cast hl
    have h0 : (0 : ℝ) ≤ l := l.cast_nonneg
    rw [hn, ← Real.rpow_neg (by linarith)]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hN.le (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)⟩
  · have eA : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor, prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - (β : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [entry_mul]
    have eB : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor]
      refine (prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - ((β⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)).trans ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹),
        ← Finset.prod_range_reflect (fun l => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ (l + 1))⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [entry_inv_mul w (z i) (Finset.mem_range.1 hl)]
    rw [eA, eB, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [mul_inv]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReduction
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem integral_of_mul_integral : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  intro L l _ hl ι h2 h3 hd z N hN hP
  have hg : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · simpa using h2
    · simpa using h3
    · simpa [map_sub, map_mul, map_pow, map_ofNat] using hd
  obtain ⟨-, -, -, G, hG, -⟩ := GlobalTheory.Klein.not_red_addSubgroup l ι L 0 hg
  by_contra hc
  have hz : z ∈ G := by
    rw [hG]; intro h; exact hc (by simpa using h.2)
  have hNz : (N : ℂ) * z ∈ G := by
    have := G.nsmul_mem hz N
    simpa [nsmul_eq_mul] using this
  rw [hG] at hNz
  exact hNz ⟨hN, by simpa using hP⟩

end GlobalTheory.Honda
end

