module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
section
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

structure HermFam (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] where

  form : (K →+* ℂ) → V → V → ℂ
  add_right : ∀ σ x y z, form σ x (y + z) = form σ x y + form σ x z
  smul_right : ∀ σ (a : K) x y, form σ x (a • y) = σ a * form σ x y
  conj_symm : ∀ σ x y, starRingEnd ℂ (form σ x y) = form σ y x
  posDef : ∀ σ (n : ℕ) (v : Fin n → V), LinearIndependent K v →
    (Matrix.of fun i j => form σ (v i) (v j)).PosDef

section

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def HermFam.gram (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => h.form σ (v i) (v j)

def HermFam.nrm (h : HermFam K V) (σ : K →+* ℂ) (x : V) : ℝ :=
  Real.sqrt (h.form σ x x).re

end

section

variable (K : Type*) [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def latRank (E : Submodule (𝓞 K) V) : ℕ :=
  finrank K (Submodule.span K (E : Set V))

def IsFrame (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : Prop :=
  (∀ i, v i ∈ E) ∧ LinearIndependent K v ∧ (E : Set V) ⊆ Submodule.span K (Set.range v)

def meanLog (A : (K →+* ℂ) → ℝ) : ℝ :=
  (∑ σ : K →+* ℂ, Real.log (A σ)) / finrank ℚ K

variable {K}

def degreeOfFamily (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : ℝ :=
  (Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ)
    - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re) / finrank ℚ K


open Classical in
def deg (h : HermFam K V) (E : Submodule (𝓞 K) V) : ℝ := by
  classical
  exact if hE : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 then degreeOfFamily h E hE.choose.2 else 0

end

end ReciprocityTheory.GeometryOfNumbersTheory
end
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountZSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem finite_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hb : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  haveI : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hc : IsClosed (L : Set E) := (L.toAddSubgroup).isClosed_of_discreteTopology
  exact Metric.finite_isBounded_inter_isClosed ⟨(‹DiscreteTopology L› : DiscreteTopology L)⟩ hb hc

theorem fiber_count_le_ncard_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Set E) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (x : E) :
    ∑' g : L, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal) ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
  classical
  by_cases hx : ∃ g0 : L, x ∈ g0 +ᵥ ((2⁻¹ : ℝ) • S)
  swap
  · push_neg at hx
    simp [Set.indicator_of_notMem (hx _)]
  obtain ⟨g0, hg0⟩ := hx

  have key : ∀ g : L, x ∈ g +ᵥ ((2⁻¹ : ℝ) • S) → ((g : E) - g0) ∈ S := by
    intro g hg
    rw [Set.mem_vadd_set] at hg hg0
    obtain ⟨a, ha, hax⟩ := hg
    obtain ⟨c, hc, hcx⟩ := hg0
    rw [Set.mem_smul_set] at ha hc
    obtain ⟨s1, hs1, rfl⟩ := ha
    obtain ⟨s2, hs2, rfl⟩ := hc
    rw [Submodule.vadd_def, vadd_eq_add] at hax hcx
    have e : (g : E) - g0 = (2⁻¹ : ℝ) • s2 + (2⁻¹ : ℝ) • (-s1) := by
      rw [smul_neg, eq_sub_of_add_eq hax, eq_sub_of_add_eq hcx]; abel
    rw [e]
    exact hconv hs2 (hsymm s1 hs1) (by norm_num) (by norm_num) (by norm_num)
  have hfin : {g : L | ((g : E) - g0) ∈ S}.Finite := by
    have hinj : Function.Injective (fun g : L => (g : E) - g0) :=
      fun a b h => Subtype.ext (sub_left_injective h)
    refine ((finite_inter_lattice L S hb).preimage hinj.injOn).subset ?_
    intro g hg
    exact Set.mem_inter hg (sub_mem g.2 g0.2)
  rw [tsum_eq_sum (s := hfin.toFinset) (fun g hg => Set.indicator_of_notMem
    (fun h => hg (hfin.mem_toFinset.2 (key g h))) _)]
  calc ∑ g ∈ hfin.toFinset, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal)
      ≤ ∑ g ∈ hfin.toFinset, (1 : ENNReal) := by
        refine Finset.sum_le_sum fun g _ => ?_
        unfold Set.indicator; split_ifs <;> simp
    _ = (hfin.toFinset.card : ENNReal) := by simp
    _ ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        have hh := Set.ncard_le_ncard_of_injOn (s := {g : L | ((g : E) - g0) ∈ S})
          (t := S ∩ (L : Set E)) (fun g : L => (g : E) - g0)
          (fun g hg => Set.mem_inter hg (sub_mem g.2 g0.2))
          (fun a _ b _ h => Subtype.ext (sub_left_injective h)) (finite_inter_lattice L S hb)
        exact_mod_cast hh

theorem measure_div_le_ncard_inter_lattice (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (hm : MeasurableSet S) :
    (μ S).toReal / (2 ^ finrank ℝ E * ZLattice.covolume L μ) ≤ ((S ∩ (L : Set E)).ncard : ℝ) := by
  classical
  haveI : MeasureTheory.VAddInvariantMeasure L E μ :=
    ⟨fun g s _ => by simp only [Submodule.vadd_def, vadd_eq_add]; exact measure_preimage_add μ (g : E) s⟩
  have hF : MeasureTheory.IsAddFundamentalDomain L
      (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) μ :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ hF
  have hpos : 0 < ZLattice.covolume L μ := ZLattice.covolume_pos L μ
  have hTm : MeasurableSet ((2⁻¹ : ℝ) • S) := hm.const_smul₀ _
  have hle : μ ((2⁻¹ : ℝ) • S) ≤ ((S ∩ (L : Set E)).ncard : ENNReal)
      * μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [hF.measure_eq_tsum ((2⁻¹ : ℝ) • S)]
    calc ∑' g : L, μ ((g +ᵥ (2⁻¹ : ℝ) • S)
          ∩ ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))
        = ∑' g : L, ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ := by
          congr 1; funext g
          rw [lintegral_indicator_one (hTm.const_vadd g), Measure.restrict_apply (hTm.const_vadd g)]
      _ = ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ∑' g : L, ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ :=
          (lintegral_tsum fun g => (measurable_one.indicator (hTm.const_vadd g)).aemeasurable).symm
      _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((S ∩ (L : Set E)).ncard : ENNReal) ∂μ :=
          lintegral_mono fun y => fiber_count_le_ncard_inter_lattice L S hconv hsymm hb y
      _ = _ := setLIntegral_const _ _
  have hFfin : μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) ≠ ⊤ := by
    intro h
    rw [hcov, Measure.real, h] at hpos
    simp at hpos
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFfin) hle
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (by positivity), inv_pow, ENNReal.toReal_natCast] at hreal
  have h2 : (0 : ℝ) < 2 ^ finrank ℝ E := by positivity
  rw [inv_mul_le_iff₀ h2] at hreal
  rw [div_le_iff₀ (mul_pos h2 hpos), hcov, Measure.real]
  calc (μ S).toReal ≤ _ := hreal
    _ = _ := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
section
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

open MeasureTheory

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}

lemma norm_sq_convex_comb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have h1 : ‖a • z + b • w‖ ≤ a * ‖z‖ + b * ‖w‖ := by
    calc ‖a • z + b • w‖ ≤ ‖a • z‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖z‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖z‖ + b * ‖w‖) ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖z‖ - ‖w‖))]
  calc ‖a • z + b • w‖ ^ 2 ≤ (a * ‖z‖ + b * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma sqBall_convex (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by
  intro u hu v hv a b ha hb hab
  simp only [sqBall, Set.mem_setOf_eq] at hu hv ⊢
  calc ∑ k, ‖(a • u + b • v) k‖ ^ 2 = ∑ k, ‖a • u k + b • v k‖ ^ 2 := rfl
    _ ≤ ∑ k, (a * ‖u k‖ ^ 2 + b * ‖v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_sq_convex_comb ha hb hab _ _
    _ = a * ∑ k, ‖u k‖ ^ 2 + b * ∑ k, ‖v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R ^ 2 + b * R ^ 2 := by gcongr
    _ = R ^ 2 := by rw [← add_mul, hab, one_mul]

lemma sqBall_neg (r : ℕ) (R : ℝ) : ∀ u ∈ sqBall r E R, -u ∈ sqBall r E R := by
  intro u hu
  simpa [sqBall] using hu

lemma sqBall_subset (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by
  intro u hu
  simp only [sqBall, Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun k => ?_
  have hk : ‖u k‖ ^ 2 ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ k)).trans hu
  have := sq_le_sq.mp hk
  rwa [abs_of_nonneg (norm_nonneg _)] at this

lemma sqBall_isBounded (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := Metric.isBounded_closedBall.subset (sqBall_subset r R)

lemma sqBall_isClosed (r : ℕ) (R : ℝ) : IsClosed (sqBall r E R) := by
  unfold sqBall
  exact isClosed_le (continuous_finsetSum _ fun k _ => (continuous_apply k).norm.pow 2)
    continuous_const

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

end Generic

end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder MatrixOrder

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gramSt_det_one_add_eq {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) := by
  set U := hQ.1.eigenvectorUnitary
  have hspec := hQ.1.spectral_theorem
  have h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U
      (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues)) := by
    rw [map_add (f := _), map_one, ← hspec]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) : Matrix ι ι ℂ) =
      diagonal (fun i => ((1 + hQ.1.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, one_apply]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod]
  rw [mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul]
  try rw [Unitary.coe_star]
  rw [Unitary.mul_star_self_of_mem U.2, det_one, mul_one]

theorem gramSt_det_re_le_of_sub {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by
  set S := CFC.sqrt G with hSdef
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := by
    intro h; rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, gramSt_det_one_add_eq hQ]
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hGpos
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : (1:ℝ) ≤ ∏ i, (1 + hQ.1.eigenvalues i) := by
    calc (1:ℝ) = ∏ _i : ι, (1:ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith

end SlopeTestRemainingChoices

section Block

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem gramSt_fischer {A : Matrix m m ℂ} {B : Matrix m k ℂ} {C : Matrix k m ℂ} {D : Matrix k k ℂ}
    (h : (fromBlocks A B C D).PosDef) :
    (fromBlocks A B C D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosDef := by
    have := h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext; simp
    rwa [e] at this
  have hD : D.PosDef := by
    have := h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext; simp
    rwa [e] at this
  have hC : C = Bᴴ := by
    have := (isHermitian_fromBlocks_iff.mp h.1)
    exact this.2.1.symm
  subst hC
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    (PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  have hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0 := by
    intro h0
    have := h.det_pos
    rw [hdet, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hSd : (D - Bᴴ * A⁻¹ * B).PosDef := hS.posDef_iff_det_ne_zero.mpr hSne
  have hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
    rw [sub_sub_cancel]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hmono := gramSt_det_re_le_of_sub hSd hdiff
  obtain ⟨hAre, hAim⟩ := Complex.pos_iff.mp hA.det_pos
  rw [hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre.le

end Block

theorem gramSt_fin_blocks {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := gramSt_fischer hP
  rwa [← hE, det_submatrix_equiv_self] at this

theorem gramSt_hadamard {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := gramSt_fin_blocks (a := k) (b := 1) hD
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re := (Complex.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)

theorem posDef_det_re_pos {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    0 < G.det.re ∧ G.det.im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hG.det_pos
  exact ⟨h1, h2.symm⟩

theorem det_re_le_of_sub_posSemidef {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re :=
  gramSt_det_re_le_of_sub hG hGH

theorem det_re_le_mul_prod_diag {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by
  have h1 := gramSt_fin_blocks hM
  have h2 := gramSt_hadamard (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a))
  have h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re :=
    (Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZStA
section
namespace ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension

open Matrix

private theorem exists_linearIndependent_append_of_codim {r : ℕ} (w : Fin r → (Fin r → ℚ))
    (hw : LinearIndependent ℚ w) :
    ∀ d a (u0 : Fin a → (Fin r → ℚ)), LinearIndependent ℚ u0 → r - a = d → a ≤ r →
      ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  intro d
  induction d with
  | zero =>
    intro a u0 hu0 hd har
    refine ⟨0, Fin.elim0, by omega, ?_⟩
    rw [Fin.append_right_nil u0 _ rfl]
    exact hu0.comp _ (Fin.cast_injective _)
  | succ d ih =>
    intro a u0 hu0 hd har
    obtain ⟨j, hj⟩ : ∃ j, w j ∉ Submodule.span ℚ (Set.range u0) := by
      by_contra hcon
      push_neg at hcon
      haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      have htop : Submodule.span ℚ (Set.range w) = ⊤ :=
        hw.span_eq_top_of_card_eq_finrank (by simp)
      have hle : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range u0) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr hcon)
      rw [htop, top_le_iff] at hle
      have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range u0)) ≤ Fintype.card (Fin a) :=
        finrank_range_le_card (R := ℚ) u0
      rw [hle, finrank_top] at h1
      simp at h1
      omega
    have hu1 : LinearIndependent ℚ (Fin.snoc u0 (w j) : Fin (a + 1) → (Fin r → ℚ)) :=
      linearIndependent_finSnoc.mpr ⟨hu0, hj⟩
    obtain ⟨m, f, hm, hli⟩ := ih (a + 1) (Fin.snoc u0 (w j)) hu1 (by omega) (by omega)
    refine ⟨m + 1, Fin.cons j f, by omega, ?_⟩
    rw [Fin.comp_cons, Fin.append_right_cons]
    exact hli.comp _ (Fin.cast_injective _)

theorem exists_append_li {a r : ℕ} (u0 : Fin a → (Fin r → ℚ)) (hu0 : LinearIndependent ℚ u0)
    (w : Fin r → (Fin r → ℚ)) (hw : LinearIndependent ℚ w) :
    ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  have har : a ≤ r := by
    have h := hu0.fintype_card_le_finrank
    simpa using h
  exact exists_linearIndependent_append_of_codim w hw _ a u0 hu0 rfl har

end ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
end

