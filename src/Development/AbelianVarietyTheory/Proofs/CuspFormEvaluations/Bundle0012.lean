module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import ReciprocityTheory.SemistableReduction.Bundle0012
public import ReciprocityTheory.SemistableReduction.SemiDegCE
public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe
section
namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors

theorem relIndex_eq_of_hom {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup M'} (f : M →+ M')
    (hf : ∀ v ∈ A₂, f v ∈ B₂) (hker : ∀ v ∈ A₂, f v ∈ B₁ ↔ v ∈ A₁)
    (hsurj : ∀ u ∈ B₂, ∃ v ∈ A₂, u - f v ∈ B₁) : A₁.relIndex A₂ = B₁.relIndex B₂ := by
  have h1 : A₁ ⊓ A₂ = B₁.comap f ⊓ A₂ := by
    ext v
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    exact ⟨fun h => ⟨(hker v h.2).2 h.1, h.2⟩, fun h => ⟨(hker v h.2).1 h.1, h.2⟩⟩
  have h2 : B₁ ⊔ A₂.map f = B₁ ⊔ B₂ := by
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left fun u hu => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hf v hv
    · obtain ⟨v, hv, h⟩ := hsurj u hu
      exact AddSubgroup.mem_sup.2 ⟨_, h, f v, ⟨v, hv, rfl⟩, sub_add_cancel _ _⟩
  rw [← AddSubgroup.inf_relIndex_right, h1, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_left, h2,
    AddSubgroup.relIndex_sup_left]

theorem relIndex_pi_univ {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (L' L : ∀ i, AddSubgroup (G i)) :
    (AddSubgroup.pi Set.univ L').relIndex (AddSubgroup.pi Set.univ L) =
      ∏ i, (L' i).relIndex (L i) := by
  let f : (AddSubgroup.pi Set.univ L) →+ (∀ i, L i ⧸ (L' i).addSubgroupOf (L i)) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y =>
    ⟨⟨fun i => (y i).out, fun i _ => (y i).out.2⟩, funext fun i => (y i).out_eq⟩
  have hc : (AddSubgroup.pi Set.univ L').addSubgroupOf (AddSubgroup.pi Set.univ L) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    refine forall_congr' fun i => ?_
    change _ ↔ (QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ :
      L i ⧸ (L' i).addSubgroupOf (L i)) = 0
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem card_eq_relIndex_of_reps {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun y : R => (QuotientAddGroup.mk ⟨y, hR y y.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨?_, ?_⟩
  · intro y y' h
    have h1 : (y : M) - y' ∈ A := by
      simpa [AddSubgroup.mem_addSubgroupOf] using QuotientAddGroup.eq_iff_sub_mem.1 h
    exact Subtype.ext ((hR' y (hR y y.2)).unique ⟨y.2, by simp⟩ ⟨y'.2, h1⟩)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, ⟨hr, h⟩, -⟩ := hR' y y.2
    refine ⟨⟨r, hr⟩, (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm⟩
    simpa [AddSubgroup.mem_addSubgroupOf] using h

theorem exists_reps_of_relIndex_ne_zero {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : A.relIndex B ≠ 0) :
    ∃ R : Finset M, (∀ y ∈ R, y ∈ B) ∧ ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A := by
  classical
  haveI : Fintype (B ⧸ A.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => (q.out : M), ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact q.out.2
  · have key : ∀ q : B ⧸ A.addSubgroupOf B,
        y - (q.out : M) ∈ A ↔ QuotientAddGroup.mk ⟨y, hy⟩ = q := fun q => by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      simp [AddSubgroup.mem_addSubgroupOf]
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key q).1 h]

section Period

variable {E : Type} [Field E] [NumberField E]

end Period

section Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Index

section Modulus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable [IsGalois ℚ E]

variable {K : Type*} [Field K] [Algebra E K]

end Modulus

section IndexIdeal

open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_coe_eq_span_det_of_intVec_le (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ :=
    ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.lattice_split K n X hfg hstd
  let CF : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  refine ⟨∏ i, CF i, ?_, ?_⟩
  · rw [coe_prod_frac]
    change ∏ i, C i = _
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [prod_eq_span_prod]
      refine Submodule.span_mono fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine ⟨fun i => t i • z i, fun i => smul_mem_of_split hin i (ht i), ?_⟩
      have : (Matrix.of fun i => t i • z i) = Matrix.diagonal t * rowMat z := by
        ext i j
        simp [rowMat, Matrix.diagonal_mul]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, Matrix.det_diagonal, mul_one]
    · rintro _ ⟨v, hv, rfl⟩
      choose T hT hTv using fun i => hdec (v i) (hv i)
      have : Matrix.of v = Matrix.of T * rowMat z := by
        ext i j
        rw [Matrix.of_apply, hTv i]
        simp [rowMat, Matrix.mul_apply, Finset.sum_apply]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, mul_one, ← Matrix.det_transpose]
      exact det_mem_prod_sub C _ fun i j => hT j i
  · rw [hidx, map_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)

theorem exists_coe_eq_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by
  classical
  choose d hd0 hd using fun k : Fin n => exists_smul_mem_of_mem_span_fraction (K := K) Λ
    (Pi.single k (1 : K)) (hsp ▸ Submodule.mem_top)
  set δ : K := algebraMap (𝓞 K) K (∏ k, d k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ, Finset.prod_ne_zero_iff] using hd0
  let μ : (Fin n → K) →ₗ[𝓞 K] (Fin n → K) := (LinearMap.lsmul K _ δ).restrictScalars (𝓞 K)
  have hμ : ∀ x, μ x = δ • x := fun _ => rfl
  have hinj : Function.Injective μ := smul_right_injective _ hδ0
  have hsurj : Function.Surjective μ := fun x => ⟨δ⁻¹ • x, by rw [hμ, smul_inv_smul₀ hδ0]⟩
  have hstd : intVec K n ≤ Λ.comap μ := by
    intro x hx
    choose c hc using fun k => Submodule.mem_one.1 (mem_intVec.1 hx k)
    have : x = ∑ k, c k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, hμ, hδ, algebraMap_smul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Λ.smul_mem _ (hd k)
  have key : ∀ Y : Submodule (𝓞 K) (Fin n → K), Λ ≤ Y → Y.FG →
      ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Y) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex
        (Y.comap μ).toAddSubgroup : ℚ) = |Algebra.norm ℚ (δ ^ n)| := by
    intro Y hY hYfg
    obtain ⟨J, hJ, hN⟩ := exists_coe_eq_span_det_of_intVec_le (Y.comap μ)
      (Submodule.fg_of_fg_map_injective μ hinj
        (by rwa [Submodule.map_comap_eq_of_surjective hsurj]))
      (hstd.trans (Submodule.comap_mono hY))
    refine ⟨FractionalIdeal.spanSingleton _ (δ ^ n) * J, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, hJ, Submodule.span_mul_span,
        Set.singleton_mul]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨δ • v, hv, ?_⟩
        change _ = (δ • Matrix.of v).det
        rw [Matrix.det_smul, Fintype.card_fin]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨_, ⟨δ⁻¹ • v, fun i => ?_, rfl⟩, ?_⟩
        · rw [Submodule.mem_comap, hμ, Pi.smul_apply, smul_inv_smul₀ hδ0]
          exact hv i
        · change _ * (δ⁻¹ • Matrix.of v).det = _
          rw [Matrix.det_smul, Fintype.card_fin, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hδ0)]
    · rw [map_mul, mul_assoc, hN, mul_one, FractionalIdeal.absNorm_span_singleton]
  obtain ⟨J, hJ, hN⟩ := key Λ le_rfl (hfg.of_le hle)
  obtain ⟨J', hJ', hN'⟩ := key Λ' hle hfg
  have hn0 : |Algebra.norm ℚ (δ ^ n)| ≠ 0 :=
    abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (pow_ne_zero _ hδ0))
  have hidx : (Λ.comap μ).toAddSubgroup.relIndex (Λ'.comap μ).toAddSubgroup =
      Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup := by
    change (Λ.toAddSubgroup.comap μ.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.comap μ.toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have htower := AddSubgroup.relIndex_mul_relIndex (intVec K n).toAddSubgroup
    (Λ.comap μ).toAddSubgroup (Λ'.comap μ).toAddSubgroup hstd (Submodule.comap_mono hle)
  refine ⟨J, J', ?_, ?_, hJ, hJ', ?_⟩
  · rintro rfl
    rw [map_zero, zero_mul] at hN
    exact hn0 hN.symm
  · rintro rfl
    rw [map_zero, zero_mul] at hN'
    exact hn0 hN'.symm
  · rw [← htower, hidx, Nat.cast_mul, ← hN] at hN'
    refine mul_right_cancel₀ (right_ne_zero_of_mul (hN ▸ hn0)) ?_
    linear_combination -hN'

attribute [local instance] extModR

end IndexIdeal

section Main

open ReciprocityTheory.PGsh

attribute [local instance] extModR

end Main

end GlobalTheory.TensorLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2CanThEqInvSqrtTwoPowMulDetIm
section
open Complex Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.CanTh

noncomputable section

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}


variable (τ) in
def realPt : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ)
  map_add' p q := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, ofReal_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul,
      RingHom.id_apply, real_smul, mul_add, Finset.mul_sum, mul_left_comm]

theorem realPt_apply (p : Fin g ⊕ Fin g → ℝ) :
    realPt τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ) := rfl

theorem realPt_injective (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (realPt τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp0
  rw [realPt_apply] at hp0
  have him : ∀ i, ∑ j, (τ i j).im * p (.inr j) = 0 := by
    intro i
    have := congrArg (fun z => (z i).im) hp0
    simpa [mulVec, dotProduct] using this
  have hu : (fun i => p (.inr i)) = 0 := by
    by_contra hne
    have hpos := hp.dotProduct_mulVec_pos hne
    have hzero : (τ.map Complex.im) *ᵥ (fun i => p (.inr i)) = 0 := by
      funext i
      simpa [mulVec, dotProduct] using him i
    rw [hzero] at hpos
    simp at hpos
  have hu' : ∀ j, p (.inr j) = 0 := fun j => congrFun hu j
  have hre : ∀ i, p (.inl i) = 0 := by
    intro i
    have := congrArg (fun z => (z i).re) hp0
    simpa [mulVec, dotProduct, hu'] using this
  funext j
  rcases j with i | i
  · exact hre i
  · exact hu' i

theorem norm_canTh_realPt (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ)
    (p : Fin g ⊕ Fin g → ℝ) :
    ‖canTh τ a b (realPt τ p)‖ ^ 2 *
        Real.exp (-π * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re) =
      ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (realPt τ p)‖ ^ 2 *
        Real.exp (-2 * π * ((fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i))) := by
  have hQ : realPt τ p ⬝ᵥ imInv τ *ᵥ realPt τ p =
      hermForm (imInv τ) (realPt τ p) (realPt τ p) +
        2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)) := by
    have h := dot_imInv_eq_hermForm_add hp (fun i => p (.inr i)) (fun i => p (.inl i)) (realPt τ p)
    rw [realPt_apply] at h ⊢
    exact h
  have hIm : (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im =
      (fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i) := by
    rw [realPt_apply]
    simp [dotProduct, mulVec, Complex.mul_im, Finset.mul_sum, mul_comm, mul_left_comm]
  have hre : ((π : ℂ) / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p) +
      2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)))).re =
      π / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re -
        π * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im := by
    simp [Complex.mul_re]
    ring
  have key : ∀ A B C T : ℝ, 2 * A + B = C → Real.exp A ^ 2 * T * Real.exp B = T * Real.exp C := by
    intro A B C T h
    rw [← h, Real.exp_add, sq, ← Real.exp_add A A, two_mul]
    ring
  rw [canTh, hQ, norm_mul, mul_pow, Complex.norm_exp, hre, hIm]
  apply key
  ring

variable (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
  (φ : EuclideanSpace ℂ (Fin g) ≃ₗ[ℂ] (Fin g → ℂ))

def realCoord : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin g) :=
  ((realPt τ).linearEquivOfInjective (realPt_injective hs hp) (by
    simp [Module.finrank_pi_fintype, mul_two])).trans (φ.symm.restrictScalars ℝ)

theorem apply_realCoord (p : Fin g ⊕ Fin g → ℝ) : φ (realCoord hs hp φ p) = realPt τ p := by
  simp [realCoord]

def sumBasis : Module.Basis (Fin g ⊕ Fin g) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (Pi.basisFun ℝ _).map (realCoord hs hp φ)

def perBasis : Module.Basis (Fin (2 * Fintype.card (Fin g))) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (sumBasis hs hp φ).reindex (finSumFinEquiv.trans (finCongr (by simp [two_mul])))

theorem mem_lat_perBasis (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (perBasis hs hp φ) ↔
      ∃ m : Fin g ⊕ Fin g → ℤ, y = realCoord hs hp φ fun j => (m j : ℝ) := by
  have hsum : ∀ m : Fin g ⊕ Fin g → ℤ,
      ∑ j, m j • sumBasis hs hp φ j = realCoord hs hp φ fun j => (m j : ℝ) := by
    intro m
    have hm : (fun j => (m j : ℝ)) = ∑ j, (m j : ℝ) • Pi.single j (1 : ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    simp only [sumBasis, Module.Basis.map_apply, Pi.basisFun_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Int.cast_smul_eq_zsmul]
  show y ∈ Submodule.span ℤ (Set.range (perBasis hs hp φ)) ↔ _
  rw [perBasis, Module.Basis.range_reindex, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, hsum]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hsum, hm]⟩

variable (hφ : ∀ v w, Hf v w = hermForm (imInv τ) (φ v) (φ w))


include hφ in
theorem im_Hf_realCoord (p q : Fin g ⊕ Fin g → ℝ) :
    (Hf (realCoord hs hp φ p) (realCoord hs hp φ q)).im =
      ∑ i, p (.inr i) * q (.inl i) - ∑ i, p (.inl i) * q (.inr i) := by
  rw [hφ, apply_realCoord, apply_realCoord, realPt_apply, realPt_apply, im_hermForm_imInv hs hp]
  simp [dotProduct]

private theorem eq_realCoord_of_eq_int_add_tau_mulVec {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    y = realCoord hs hp φ fun j => ((Sum.elim m n j : ℤ) : ℝ) := by
  apply φ.injective
  rw [apply_realCoord, realPt_apply, h]
  simp

def torus (a b : Fin g → ℝ) : GT (Fin g) where
  b := perBasis hs hp φ
  integral x y hx hy := by
    obtain ⟨m, rfl⟩ := (mem_lat_perBasis hs hp φ x).1 hx
    obtain ⟨n, rfl⟩ := (mem_lat_perBasis hs hp φ y).1 hy
    refine ⟨∑ i, m (.inr i) * n (.inl i) - ∑ i, m (.inl i) * n (.inr i), ?_⟩
    rw [im_Hf_realCoord hs hp φ hφ]
    push_cast
    rfl
  perfect f := by
    let e : Fin g ⊕ Fin g → lat (perBasis hs hp φ) := fun j =>
      ⟨_, (mem_lat_perBasis hs hp φ _).2 ⟨Pi.single j 1, rfl⟩⟩
    refine ⟨_, (mem_lat_perBasis hs hp φ _).2
      ⟨Sum.elim (fun i => -f (e (.inr i))) fun i => f (e (.inl i)), rfl⟩, fun y => ?_⟩
    obtain ⟨n, hn⟩ := (mem_lat_perBasis hs hp φ y).1 y.2
    have hy : y = ∑ j, n j • e j := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hn, e, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower,
        ← map_zsmul, ← map_sum]
      congr 1
      funext j
      simp [Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hn, im_Hf_realCoord hs hp φ hφ, hy, map_sum]
    simp [mul_comm]
  ka y := cexp (((π * ∑ i, (realCoord hs hp φ).symm y (.inl i) * (realCoord hs hp φ).symm y (.inr i) +
    2 * π * (∑ i, a i * (realCoord hs hp φ).symm y (.inl i) -
      ∑ i, b i * (realCoord hs hp φ).symm y (.inr i)) : ℝ) : ℂ) * I)
  ka_abs _ _ := norm_exp_ofReal_mul_I _

variable (a b : Fin g → ℝ)

theorem mem_lat_torus (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (torus hs hp φ hφ a b).b ↔
      ∃ m n : Fin g → ℤ, φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) := by
  show y ∈ lat (perBasis hs hp φ) ↔ _
  rw [mem_lat_perBasis]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    rw [apply_realCoord, realPt_apply]
    simp
  · rintro ⟨m, n, h⟩
    exact ⟨Sum.elim m n, eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h⟩

theorem torus_ka {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    (torus hs hp φ hφ a b).ka y = canMult a b m n := by
  rw [eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h]
  simp only [torus, LinearEquiv.symm_apply_apply, canMult, Sum.elim_inl, Sum.elim_inr]
  congr 1
  simp only [dotProduct]
  push_cast
  ring

theorem canTh_mem_Sec : (fun v => canTh τ a b (φ v)) ∈ (torus hs hp φ hφ a b).Sec 1 := by
  show _ ∧ _
  refine ⟨(differentiable_canTh hp a b).comp
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable, ?_⟩
  intro γ hγ v
  obtain ⟨m, n, h⟩ := (mem_lat_torus hs hp φ hφ a b γ).1 hγ
  beta_reduce
  rw [map_add (f := _), h, canTh_add_period hs hp a b m n rfl, torus_ka hs hp φ hφ a b h, hφ, hφ, h]
  simp only [Nat.cast_one, one_mul]
  ring_nf

private theorem norm_sq_eq_re_Hf (w : EuclideanSpace ℂ (Fin g)) : ‖w‖ ^ 2 = (Hf w w).re := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem l2_canTh_eq_inv_sqrt_two_pow_mul_det_im : (torus hs hp φ hφ a b).l2 1 (fun v => canTh τ a b (φ v)) =
    (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  have hpt : ∀ x : Fin g ⊕ Fin g → ℝ,
      (torus hs hp φ hφ a b).ptN2 1 (fun v => canTh τ a b (φ v))
          ((sumBasis hs hp φ).equivFun.symm x) =
        ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))
            ((fun i => (x (.inl i) : ℂ)) + τ.mulVec (fun i => (x (.inr i) : ℂ)))‖ ^ 2 *
          Real.exp (-2 * Real.pi *
            ((fun i => x (.inr i)) ⬝ᵥ (τ.map Complex.im).mulVec (fun i => x (.inr i)))) := by
    intro x
    have hx : (sumBasis hs hp φ).equivFun.symm x = realCoord hs hp φ x := by
      simp [sumBasis, Module.Basis.map_equivFun]
    simp only [hx, GT.ptN2]
    rw [norm_sq_eq_re_Hf, hφ, apply_realCoord, Nat.cast_one, one_mul, norm_canTh_realPt hp,
      realPt_apply]
  have hfd : ZSpan.fundamentalDomain (torus hs hp φ hφ a b).b =
      ZSpan.fundamentalDomain (sumBasis hs hp φ) :=
    ZSpan.fundamentalDomain_reindex (b := sumBasis hs hp φ) _
  rw [GT.l2, hfd, avg_fd_cube, cubeIco_eq]
  simp_rw [hpt]
  exact GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hs hp

end

end GlobalTheory.CanTh
end

