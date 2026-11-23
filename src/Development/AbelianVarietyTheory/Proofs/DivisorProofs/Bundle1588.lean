module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLocalFactorFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharApplyEqAdelicChar
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.StdCharEq

theorem trace_eq_infiniteTrace (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      GroundTheory.Global.infiniteTrace F x := by
  classical
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi,
    PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

theorem eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  intro F _ _ ψ hψ
  have hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) =
      (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ) := fun a b => by
    rw [← Circle.coe_mul]
    exact congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ) := fun x => by
    have h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x) :=
      GroundTheory.Global.adelicChar_infinite x
    rw [GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ) :=
    continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar
  have hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} :=
    isClosed_eq (hψ.1.comp hp) (hc.comp hp)
  have hrange : Set.range (algebraMap F (Af F)) ⊆
      {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    have h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1 := by
      have h := GroundTheory.Global.adelicChar_algebraMap (K := F) a
      exact (congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf] at h1
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd] at h2
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)
  have hall := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at hall
  intro x
  rw [GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]
  exact congrArg _ (hall (Set.mem_univ x.2))

end GlobalTheory.StdCharEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.PsiNontriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := GlobalTheory.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [GlobalTheory.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end GlobalTheory.PsiNontriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeGen

open Matrix GlobalTheory.SympChange

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

def upM (T : Matrix κ κ K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K := fromBlocks 1 T 0 1

theorem weylM_mem : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inr rfl)

theorem leviM_mem (A : Matrix κ κ K) (h : IsUnit A.det) :
    leviM A ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨A, h, rfl⟩))

theorem unipM_mem (S : Matrix κ κ K) (h : Sᵀ = S) :
    unipM S ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨S, h, rfl⟩))

theorem upM_eq (T : Matrix κ κ K) :
    upM T = weylM * unipM (-T) * (weylM * weylM * weylM) := by
  simp [upM, weylM, unipM, fromBlocks_multiply]

theorem upM_mem (T : Matrix κ κ K) (h : Tᵀ = T) :
    upM T ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  rw [upM_eq]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem (unipM_mem _ (by rw [transpose_neg, h])))
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem weylM_mem) weylM_mem)

theorem isSymp_mul {G H : Matrix (κ ⊕ κ) (κ ⊕ κ) K} (hG : IsSymp G) (hH : IsSymp H) :
    IsSymp (G * H) := by
  unfold IsSymp at *
  calc (G * H)ᵀ * weylM * (G * H) = Hᵀ * (Gᵀ * weylM * G) * H := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = weylM := by rw [hG, hH]

theorem isSymp_upM (T : Matrix κ κ K) (h : Tᵀ = T) : IsSymp (upM T) := by
  simp [IsSymp, upM, weylM, fromBlocks_transpose, fromBlocks_multiply, h]

theorem weyl_sq : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * weylM = -1 := by
  simp [weylM, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem exists_sym_isUnit (a c : Matrix κ κ K) (hs : aᵀ * c = cᵀ * a)
    (hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
    ∃ T : Matrix κ κ K, Tᵀ = T ∧ IsUnit (a + T * c).det := by
  classical
  let P : Finset κ → Prop := fun s => ∀ y, (∀ i ∉ s, (a *ᵥ y) i = 0) → a *ᵥ y = 0
  have hP0 : P ∅ := fun y hy => funext fun i => hy i (Finset.notMem_empty i)
  obtain ⟨s, hs_mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP0⟩⟩
  have hsP : P s := (Finset.mem_filter.1 hs_mem).2
  have key : ∀ z : κ → K, (∀ i ∈ s, z i = 0) → (∀ y, z ⬝ᵥ (a *ᵥ y) = 0) → z = 0 := by
    intro z hzs hzo
    funext j
    by_cases hj : j ∈ s
    · exact hzs j hj
    · have hnot : ¬ P (insert j s) := by
        intro hP'
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      simp only [P, not_forall] at hnot
      obtain ⟨y, hy, hne⟩ := hnot
      have hvj : (a *ᵥ y) j ≠ 0 := by
        intro h0
        apply hne
        apply hsP y
        intro i hi
        by_cases hij : i = j
        · rw [hij]; exact h0
        · exact hy i (by simp [hij, hi])
      have hsum : z ⬝ᵥ (a *ᵥ y) = z j * (a *ᵥ y) j := by
        unfold dotProduct
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases his : i ∈ s
          · rw [hzs i his, zero_mul]
          · rw [hy i (by simp [hij, his]), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have h0 := hzo y
      rw [hsum] at h0
      exact (mul_eq_zero.1 h0).resolve_right hvj
  set T : Matrix κ κ K := diagonal fun i => if i ∈ s then 1 else 0 with hTdef
  have hTe : ∀ w : κ → K, ∀ i, (T *ᵥ w) i = (if i ∈ s then 1 else 0) * w i := fun w i => by
    simp [hTdef, mulVec_diagonal]
  have hx : ∀ x, (a + T * c) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [add_mulVec, ← mulVec_mulVec] at hx
    have hx2 : ∀ i, (a *ᵥ x) i + (if i ∈ s then 1 else 0) * (c *ᵥ x) i = 0 := fun i => by
      rw [← hTe]; exact congrFun hx i
    have hax : a *ᵥ x = 0 := hsP x (fun i hi => by
      have := hx2 i
      rwa [if_neg hi, zero_mul, add_zero] at this)
    have hcs : ∀ i ∈ s, (c *ᵥ x) i = 0 := fun i hi => by
      have := hx2 i
      rwa [if_pos hi, one_mul, hax, Pi.zero_apply, zero_add] at this
    have horth : ∀ y, (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = 0 := fun y => by
      calc (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = x ⬝ᵥ ((cᵀ * a) *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x cᵀ, vecMul_transpose]
        _ = x ⬝ᵥ ((aᵀ * c) *ᵥ y) := by rw [hs]
        _ = (a *ᵥ x) ⬝ᵥ (c *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x aᵀ, vecMul_transpose]
        _ = 0 := by rw [hax, zero_dotProduct]
    exact hinj x hax (key _ hcs horth)
  refine ⟨T, by simp [hTdef], isUnit_iff_ne_zero.2 fun hdet => ?_⟩
  obtain ⟨v, hv, hmv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  exact hv (hx v hmv)

theorem symp_blocks {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d = 1 + cᵀ * b ∧ bᵀ * d = dᵀ * b := by
  simp only [IsSymp, weylM, fromBlocks_transpose, fromBlocks_multiply] at h
  obtain ⟨h11, h12, -, h22⟩ := fromBlocks_inj.1 h
  simp at h11 h12 h22
  refine ⟨(neg_add_eq_zero.1 h11).symm, ?_, (neg_add_eq_zero.1 h22).symm⟩
  rw [← h12]; abel

theorem mem_of_isUnit {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) (ha : IsUnit a.det) :
    fromBlocks a b c d ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  obtain ⟨e1, e2, e3⟩ := symp_blocks h
  have haa : a * a⁻¹ = 1 := mul_nonsing_inv a ha
  have hai : a⁻¹ * a = 1 := nonsing_inv_mul a ha
  have hT1 : a⁻¹ᵀ * aᵀ = 1 := by rw [← transpose_mul, haa, transpose_one]
  have hT2 : aᵀ * a⁻¹ᵀ = 1 := by rw [← transpose_mul, hai, transpose_one]
  set Y := c * a⁻¹ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, transpose_mul]
    calc a⁻¹ᵀ * cᵀ = a⁻¹ᵀ * cᵀ * (a * a⁻¹) := by rw [haa, Matrix.mul_one]
      _ = a⁻¹ᵀ * (cᵀ * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ᵀ * (aᵀ * c) * a⁻¹ := by rw [e1]
      _ = (a⁻¹ᵀ * aᵀ) * c * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c * a⁻¹ := by rw [hT1, Matrix.one_mul]
  have hd : d = a⁻¹ᵀ + Y * b := by
    calc d = (a⁻¹ᵀ * aᵀ) * d := by rw [hT1, Matrix.one_mul]
      _ = a⁻¹ᵀ * (aᵀ * d) := by rw [Matrix.mul_assoc]
      _ = a⁻¹ᵀ + (a⁻¹ᵀ * cᵀ) * b := by rw [e2, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = a⁻¹ᵀ + Y * b := by rw [← transpose_mul, ← hYdef, hY]
  set X := a⁻¹ * b with hXdef
  have hX : Xᵀ = X := by
    have e3' := e3
    rw [hd, Matrix.mul_add, transpose_add, Matrix.add_mul, transpose_mul, hY, transpose_transpose] at e3'
    simp only [← Matrix.mul_assoc] at e3'
    rw [hXdef, transpose_mul]
    exact add_right_cancel e3'
  have hG : fromBlocks a b c d = unipM Y * leviM a * upM X := by
    simp only [unipM, leviM, upM, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    congr 1
    · rw [hXdef, ← Matrix.mul_assoc, haa, Matrix.one_mul]
    · rw [hYdef, Matrix.mul_assoc, hai, Matrix.mul_one]
    · rw [hd, hXdef, hYdef, add_comm]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc a a⁻¹ b, haa, Matrix.one_mul]
  rw [hG]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (unipM_mem _ hY) (leviM_mem _ ha)) (upM_mem _ hX)

theorem mem_closure_gens : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  intro K _ _ κ _ _ G hG
  rw [← fromBlocks_toBlocks G] at hG ⊢
  set a := G.toBlocks₁₁
  set b := G.toBlocks₁₂
  set c := G.toBlocks₂₁
  set d := G.toBlocks₂₂
  obtain ⟨e1, -, -⟩ := symp_blocks hG

  have hL : (-(weylM * (fromBlocks a b c d)ᵀ * weylM)) * fromBlocks a b c d = 1 := by
    have h := hG
    unfold IsSymp at h
    have e : weylM * (fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d
        = weylM * ((fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, e, h, weyl_sq, neg_neg]
  have hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 := by
    intro x hax hcx
    have hv : fromBlocks a b c d *ᵥ Sum.elim x 0 = 0 := by
      rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hax, hcx, mulVec_zero, mulVec_zero]
      simp
    have h0 : Sum.elim x (0 : κ → K) = 0 := by
      rw [← Matrix.one_mulVec (Sum.elim x 0), ← hL, ← mulVec_mulVec, hv, mulVec_zero]
    funext i
    exact congrFun h0 (Sum.inl i)
  obtain ⟨T, hT, hu⟩ := exists_sym_isUnit a c e1 hinj
  have hH : upM T * fromBlocks a b c d = fromBlocks (a + T * c) (b + T * d) c d := by
    simp [upM, fromBlocks_multiply]
  have hHs : IsSymp (fromBlocks (a + T * c) (b + T * d) c d) := hH ▸ isSymp_mul (isSymp_upM T hT) hG
  have hinv : upM (-T) * upM T = (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) := by
    simp [upM, fromBlocks_multiply]
  have : fromBlocks a b c d = upM (-T) * fromBlocks (a + T * c) (b + T * d) c d := by
    rw [← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [this]
  exact Submonoid.mul_mem _ (upM_mem _ (by rw [transpose_neg, hT])) (mem_of_isUnit hHs hu)

end GlobalTheory.SympChangeGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  first | exact @GlobalTheory.LatParam.latAtV_param | exact GlobalTheory.LatParam.latAtV_param | (intros; apply GlobalTheory.LatParam.latAtV_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  first | exact @GlobalTheory.LatSplit.latAtV_decomp | exact GlobalTheory.LatSplit.latAtV_decomp | (intros; apply GlobalTheory.LatSplit.latAtV_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLocalFactorFinitePlaceStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_local_factor_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl (F := F))) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  first | exact @GlobalTheory.UnitaryTriSplit.factor_away | exact GlobalTheory.UnitaryTriSplit.factor_away | (intros; apply GlobalTheory.UnitaryTriSplit.factor_away <;> assumption)
end

