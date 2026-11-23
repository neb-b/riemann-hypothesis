module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOneStatement
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F), x * y = 1 → ‖(x : Fv F v)‖ = 1 := by
  first | exact @GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | exact GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one | (intros; apply GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain.VacVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

private theorem Jm_mul_Jm_eq_oneFormalDegree {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conjTranspose_Jm_eq_Jm {n : ℕ} (ε : Fin n → Bool) :
    Matrix.conjTranspose (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conj_cartan_involution_props {n : ℕ} (F J : Matrix (Fin n) (Fin n) ℂ) (hF : IsUnit F) (hJ : J * J = 1)
    (hJh : Matrix.conjTranspose J = J) :
    F⁻¹ * J * F * (F⁻¹ * J * F) = 1 ∧
      Matrix.conjTranspose (F⁻¹ * J * F) * (Matrix.conjTranspose F * J * F) * (F⁻¹ * J * F) =
        Matrix.conjTranspose F * J * F ∧
      Matrix.conjTranspose F * J * F * (F⁻¹ * J * F) = Matrix.conjTranspose F * F := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hdh : IsUnit (Matrix.conjTranspose F).det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
    exact Matrix.nonsing_inv_mul F hd
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hJh, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hdh, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]


open Matrix in
open scoped ComplexOrder in
theorem cart_isCartanInv {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  unfold IsCartanInv cart
  rw [← M.fr_gram τ]
  obtain ⟨h1, h2, h3⟩ := conj_cartan_involution_props _ _ (M.fr_unit τ) (Jm_mul_Jm_eq_oneFormalDegree (M.ε τ)) (conjTranspose_Jm_eq_Jm (M.ε τ))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hinj : Function.Injective (M.fr τ).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (M.fr_unit τ)
  simpa only [Matrix.mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

end GlobalTheory.Chain.VacVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactCoverIffRapidDecOne
section
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Height

variable {D : D7} (V : HSp D)

theorem isCompact_setOf_height_le (C : ℝ) : IsCompact {g : GA D V | height V g ≤ C} := by
  refine (GlobalTheory.AdelicU.isCompact_height_le (F := D.host.F) D.sp.cm.sig V.gram C.toNNReal).of_isClosed_subset
    (isClosed_le (continuous_height V) continuous_const) fun g hg => ?_
  exact NNReal.le_toNNReal_of_coe_le hg

variable {X : Type} [NormedAddCommGroup X]

end Height

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} [SFinite μG]
  [μG.IsMulLeftInvariant] [μR.IsHaarMeasure] [μR.IsInvInvariant]

end Quot

theorem quotientIntegral_trivial_count {G : Type} [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (f : G → ℂ) : IsQuotIntL1 (R := ⊥) (Measure.dirac 1) Measure.count f (∑ g, f g) := by
  rw [isQuotIntL1_bot]
  refine ⟨Integrable.of_finite, ?_⟩
  rw [integral_fintype]
  · simp
  · exact Integrable.of_finite

end GlobalTheory.Grow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsLocalLevelAtPrimeOfLevelDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

variable {D : D7}

def redLevGrp {κ : Type} [CommRing κ] {a : ℕ} (r t : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) :
    Subgroup (GL (Fin a) κ) where
  carrier := {kb | kb ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hr kb ∈ H}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    show Formalism.L2.DIV.ext1 _ _ 1 ∈ H
    rw [Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]; exact H.one_mem
  mul_mem' := by
    rintro x y ⟨hx, hxH⟩ ⟨hy, hyH⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e]; exact H.mul_mem hxH hyH
  inv_mem' := by
    rintro x ⟨hx, hxH⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr x⁻¹ = (Formalism.L2.DIV.upperLeftBlock hr x)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx)
    rw [e]; exact H.inv_mem hxH

def redLevChar {κ : Type} [CommRing κ] {a : ℕ} (r t s : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) (c : H →* ℂˣ)
    (cg : ℕ → κˣ →* ℂˣ) : redLevGrp r t hr H →* ℂˣ where
  toFun kb := Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr kb.1) *
    ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) kb.1)
  map_one' := by
    simp only [OneMemClass.coe_one]
    have h1 : Formalism.L2.DIV.upperLeftBlock hr (1 : GL (Fin a) κ) = 1 := Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    have h2 : ∀ c', Formalism.L2.DIV.dBlk (κ := κ) (n := a) (Formalism.L2.DIV.blkOf r t) c' 1 = 1 := fun _ =>
      Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    rw [h1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    simp [h2]
  map_mul' := by
    rintro ⟨x, hx, hxH⟩ ⟨y, hy, hyH⟩
    show Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr (x * y)) *
        ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) = _
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul c hxH hyH]
    have e2 : ∀ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) =
        cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) x) *
          cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) y) := fun i _ => by
      rw [Formalism.L2.DIV.diag_block_det_mul hx hy, map_mul]
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem exists_isLocLevel : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  intro D v φ PP r hred a L H c
  let f := Matrix.GeneralLinearGroup.map (n := Fin a) r
  refine ⟨(redLevGrp L.r L.t L.hr H).comap f,
    (redLevChar L.r L.t L.s L.hr H c (fun i => L.cg i PP)).comp
      ((f.subgroupComap (redLevGrp L.r L.t L.hr H))), ?_⟩
  intro k kb hk
  have hkb : kb = f k := by
    ext i j
    obtain ⟨h, e⟩ := (hred.2.2.1 _ _).1 (hk i j)
    rw [← e]
    rfl
  subst hkb
  exact ⟨Iff.rfl, fun _ => rfl⟩

end GlobalTheory.StepVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaxValuationIdealSplitPlaceAndConjugate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdealMax

theorem exists_max_of_int (D : D7) {v : FinPl D} (g : D.host.E →+* Fv D.host.F v)
    (hg : ∀ o : 𝓞 D.host.E, Valued.v (g (o : D.host.E)) ≤ 1) :
    ∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (g a') ≤ Valued.v (g a) := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (GlobalTheory.SplitHomLattice.ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact GlobalTheory.SplitHomLattice.ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (g a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), Valued.v (g a) ≤ Valued.v (g a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
    | smul o x _ hx =>
      rw [show o • x = (o : D.host.E) * x from rfl, map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' (hg o)).trans hx
  have hmem : a₀ ∈ D.host.AA := by
    show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  have h0 : a₀ ≠ 0 := by
    rintro rfl
    apply GlobalTheory.SplitHomLattice.ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [map_zero, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero g).1 this
  exact ⟨a₀, hmem, h0, fun a' ha' => hle a' ha'⟩

theorem star_int (D : D7) (o : 𝓞 D.host.E) : IsIntegral ℤ (star (o : D.host.E)) :=
  (o.2).map (starRingEnd D.host.E).toIntAlgHom

end GlobalTheory.SplitIdealMax

open GlobalTheory.SplitIdealMax in
theorem GlobalTheory.SplitIdealMax.exists_max_both : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  intro D v φ _ _
  refine ⟨exists_max_of_int D (GlobalTheory.PlaceRed.rdQh φ) fun o => GlobalTheory.PlaceRed.rdQ_int φ o,
    exists_max_of_int D ((GlobalTheory.PlaceRed.rdQh φ).comp (starRingEnd D.host.E)) fun o =>
      GlobalTheory.PlaceRed.rdQ_int φ ⟨star (o : D.host.E), star_int D o⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupLifts

theorem liftsExist_of_twist_empty :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  intro D V β L Λ N hB hQ hP

  refine _root_.GlobalTheory.ParahoricLift.liftsExist V β L Λ N hB ?_ ?_
  · intro PP hPP PP' hPP'
    rcases hPP' with h | h
    · exact hP PP hPP PP' h
    · simp [hQ] at h
  · simp [hQ]

end GlobalTheory.FiniteGroupLifts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodRowsLevel

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_lev_of_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {x : GL (Fin (Yc D 0).rank) (EAf D)}
    (hx : x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      levFn (R.βY 0) (R.dat0 P) x = levFn (R.βY 0) (R.dat0 R.triv) x := by
  have h1 : rTup (R.βY 0) (R.dat0 R.triv) x = 1 := Subgroup.mem_bot.1 hx.2
  have h1' : rTup (R.βY 0) (R.dat0 P) x = 1 := h1
  refine ⟨⟨hx.1, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    rfl

theorem isMultMap_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {S : MMap (R.MY 0)}
    (h : IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S) :
    IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) S := by
  refine ⟨h.aut, h.cusp, ?_, h.equiv, h.cont⟩
  intro v k hk g
  have hk2 : k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)).comap (finE (Yc D 0)) := hk
  rw [Subgroup.mem_inf, Subgroup.mem_comap] at hk2
  have hm := mem_lev_of_triv R P hk2.2
  have hk' : k ∈ levS _ (R.βY 0) (R.dat0 P) :=
    (show k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) from
      Subgroup.mem_inf.2 ⟨hk2.1, Subgroup.mem_comap.2 hm.1⟩)
  rw [h.lev v k hk' g]
  simp only [levChi]
  rw [hm.2]

theorem eeat_le_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv := by
  intro S hS
  rw [RealDat.EEat, goodPart, Submodule.mem_inf] at hS ⊢
  refine ⟨?_, hS.2⟩
  exact Submodule.span_mono (fun S' hS' => isMultMap_triv R P hS') hS.1

theorem eeat_sub_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM
  have h2 : ∀ P, R.EEat P ≤ LinearMap.range R.HE.e := fun P => by
    rw [hM.HE.2.1]; exact eeat_le_triv R P
  refine ⟨eeat_le_triv R, h2, ?_⟩
  intro P S hS S' hS'
  obtain ⟨x, rfl⟩ := h2 P hS
  obtain ⟨y, rfl⟩ := h2 P hS'
  rw [← hM.HE.2.2 x y]
  exact GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE x y

end GlobalTheory.GoodRowsLevel
end

