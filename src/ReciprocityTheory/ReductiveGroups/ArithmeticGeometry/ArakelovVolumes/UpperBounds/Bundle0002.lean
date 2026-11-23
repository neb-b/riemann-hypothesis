module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetMonoDetOneAdd
public import Lemmata.PosDefOfRealQuadratic.QuadFormRealSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open Matrix
open scoped ComplexOrder Matrix

variable {p q : ℕ}

theorem cross_psd (Z W : Matrix (Fin p) (Fin q) ℂ) (hW : (1 - W * Wᴴ).PosDef) :
    ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ - (1 - Z * Zᴴ)).PosSemidef := by
  set B := 1 - W * Wᴴ with hBdef
  set C := 1 - Z * Wᴴ with hCdef
  set S := B⁻¹ with hSdef
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hW.det_pos.ne'
  have hSB : S * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBS : B * S = 1 := Matrix.mul_nonsing_inv B hBu
  have hBh : Bᴴ = B := hW.1
  have hS : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_nonsing_inv, hBh]
  have h1 : (C * S - 1) * B * (C * S - 1)ᴴ = C * S * Cᴴ - C - Cᴴ + B := by
    have e : (C * S - 1) * B = C - B := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hSB, Matrix.mul_one, Matrix.one_mul]
    rw [e, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      ← Matrix.mul_assoc B S, hBS, Matrix.one_mul, Matrix.mul_assoc C S]
    abel
  have h2 : C + Cᴴ - B = (1 - Z * Zᴴ) + (W - Z) * (W - Z)ᴴ := by
    rw [hCdef, hBdef]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have e : C * S * Cᴴ - (1 - Z * Zᴴ) = (C * S - 1) * B * (C * S - 1)ᴴ + (W - Z) * (W - Z)ᴴ := by
    have hA : (1 - Z * Zᴴ) = C + Cᴴ - B - (W - Z) * (W - Z)ᴴ := by rw [h2]; abel
    rw [h1, hA]; abel
  rw [e]
  exact (hW.posSemidef.mul_mul_conjTranspose_same _).add (posSemidef_self_mul_conjTranspose _)

theorem det_re_pos_im {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    0 < A.det.re ∧ A.det.im = 0 := by
  have h := hA.det_pos
  rw [Complex.lt_def] at h
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

theorem det_eq_ofReal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(det_re_pos_im hA).2])

theorem det_mul_det_le_normSq_det (Z W : Matrix (Fin p) (Fin q) ℂ) (hZ : (1 - Z * Zᴴ).PosDef)
    (hW : (1 - W * Wᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re * (1 - W * Wᴴ).det.re ≤ Complex.normSq (1 - Z * Wᴴ).det := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ)
    (1 - Z * Zᴴ) hZ.posSemidef (cross_psd Z W hW)
  obtain ⟨hb, hbi⟩ := det_re_pos_im hW
  set b := (1 - W * Wᴴ).det.re
  have hdet : ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ).det =
      ((Complex.normSq (1 - Z * Wᴴ).det / b : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_conjTranspose,
      Ring.inverse_eq_inv', det_eq_ofReal hW, mul_right_comm, Complex.star_def, Complex.mul_conj]
    push_cast; ring
  rw [hdet, Complex.ofReal_re] at hm
  rwa [le_div_iff₀ hb] at hm

theorem det_re_le_one {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re ≤ 1 := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p 1 (1 - Z * Zᴴ) hZ.posSemidef
    (by rw [sub_sub_cancel]; exact posSemidef_self_mul_conjTranspose Z)
  simpa using hm

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

theorem quad_im {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (x : Fin m → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hA.apply i j
  rw [Complex.star_def] at h
  rw [h]; ring

theorem posDef_eventually {X : Type*} [TopologicalSpace X] {m : ℕ}
    (A : X → Matrix (Fin m) (Fin m) ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  first | exact Bl.PosDefOfRealQuadratic.goal1 .. | (apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption) | (intros; apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption)

theorem cont_coord {n : ℕ} (i : Fin n) : Continuous fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.continuous _

theorem herm_one_sub {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : (1 - Z * Zᴴ).IsHermitian :=
  isHermitian_one.sub (isHermitian_mul_conjTranspose_self Z)

theorem cont_entry {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) (k : Fin f) (a b : Fin p) :
    Continuous fun x => (1 - Zof (g x) k * (Zof (g x) k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Zof, Matrix.of_apply]
  exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
    (hg _).mul (continuous_star.comp (hg _)))

theorem isOpen_of {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) :
    IsOpen {x | ∀ k, (1 - Zof (g x) k * (Zof (g x) k)ᴴ).PosDef} := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  exact Filter.eventually_all.2 fun k => posDef_eventually _ (cont_entry g hg k)
    (fun x => herm_one_sub _) x0 (hx0 k)

theorem isOpen_Dset (f p q : ℕ) : IsOpen (Dset f p q) :=
  isOpen_of (fun v : V (nD f p q) => v) cont_coord

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace AlgT

variable (d : Data K ι Ω WT A)

end AlgT

open AlgT

def TrdegD (d : Data K ι Ω WT A) (c : ι) : Prop :=
  Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j =>
    ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) = d.D

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal

noncomputable section

variable {p q : ℕ}

theorem sumBdJf_eq_diag : Jf p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Jf, Matrix.diagonal_apply, Matrix.one_apply] <;>
    split_ifs <;> simp

private theorem Jf_mul_self_eq_one : Jf p q * Jf p q = 1 := by
  rw [sumBdJf_eq_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem inv_eq_lemma_2 {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := by
  have hg : gᴴ * Jf p q * g = Jf p q := h
  apply Matrix.inv_eq_left_inv
  calc Jf p q * gᴴ * Jf p q * g = Jf p q * (gᴴ * Jf p q * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jf_mul_self_eq_one]

theorem sumBd_inv_entry {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ =
      ‖g j i - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) j i‖ := by
  have hs : ∀ z : ℂ, ‖(starRingEnd ℂ) z - 1‖ = ‖z - 1‖ := fun z => by
    have h0 := Complex.norm_conj (z - 1)
    rwa [map_sub, map_one] at h0
  rw [inv_eq_lemma_2 h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]
  · simp
  · simp
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]

theorem sumBd_sep {f : ℕ} (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)) (hd : DiscreteTopology Γ)
    (hU : ∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ Γ, γ ≠ 1 → ∃ k i j,
      c ≤ ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
  by_contra hcon
  push_neg at hcon
  have hc' : ∀ n : ℕ, ∃ γ ∈ Γ, γ ≠ 1 ∧ ∀ k i j,
      ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hcon _ (by positivity)
  choose γ hγΓ hγ1 hγc using hc'
  have hent : ∀ k i j, Filter.Tendsto
      (fun n => ((γ n k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hγc n k i j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : ∀ k i j, Filter.Tendsto
      (fun n => (((γ n k)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Matrix.coe_units_inv, sumBd_inv_entry (hU _ (hγΓ n) k) i j]
    exact (hγc n k j i).le
  have hT : Filter.Tendsto γ Filter.atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply, Pi.one_apply, inv_one, Units.val_one]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hent k i j
    · exact (MulOpposite.continuous_op.tendsto _).comp
        (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hinv k i j)
  have hδ : Filter.Tendsto (fun n => (⟨γ n, hγΓ n⟩ : Γ)) Filter.atTop (𝓝 1) := tendsto_subtype_rng.mpr hT
  have hev : ∀ᶠ n in Filter.atTop, (⟨γ n, hγΓ n⟩ : Γ) ∈ ({1} : Set Γ) :=
    hδ ((isOpen_discrete ({1} : Set Γ)).mem_nhds rfl)
  obtain ⟨n, hn⟩ := hev.exists
  exact hγ1 n (congrArg Subtype.val hn)

theorem sumBd_inv_eq {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := inv_eq_lemma_2 h

theorem sumBd_mul_inv {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) : g * g⁻¹ = 1 := by
  have hg : gᴴ * Jf p q * g = Jf p q := h
  have hl : g⁻¹ * g = 1 := by
    rw [sumBd_inv_eq h]
    calc Jf p q * gᴴ * Jf p q * g = Jf p q * (gᴴ * Jf p q * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jf_mul_self_eq_one]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)

theorem sumBd_inv_entry' {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j‖ = ‖g j i‖ := by
  rw [sumBd_inv_eq h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem sumBd_sep_diff {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsUpq g) {R c : ℝ}
    (hR : 0 < R) (hc0 : 0 < c) (hgR : ∀ i j, ‖g i j‖ ≤ R) {i j : Fin p ⊕ Fin q}
    (hc : c ≤ ‖(h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) :
    ∃ l, c / (((p + q : ℕ) : ℝ) + 1) / R ≤ ‖h i l - g i l‖ := by
  by_contra hcon
  push_neg at hcon
  have hN : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hgi : ∀ l, ‖g⁻¹ l j‖ ≤ R := fun l => by rw [sumBd_inv_entry' hg]; exact hgR j l
  have e : (h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j = ((h - g) * g⁻¹) i j := by
    rw [Matrix.sub_mul, sumBd_mul_inv hg, Matrix.sub_apply]
  rw [e, Matrix.mul_apply] at hc
  have hle : ‖∑ l, (h - g) i l * g⁻¹ l j‖ ≤ ∑ _l : Fin p ⊕ Fin q, c / (((p + q : ℕ) : ℝ) + 1) / R * R := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, Matrix.sub_apply]
    exact mul_le_mul (hcon l).le (hgi l) (norm_nonneg _) (by positivity)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    div_mul_cancel₀ _ hR.ne'] at hle
  have h3 : ((p + q : ℕ) : ℝ) * (c / (((p + q : ℕ) : ℝ) + 1)) < c := by
    rw [mul_div_assoc', div_lt_iff₀ hN]
    nlinarith
  push_cast at hle h3
  linarith

theorem sumBd_count {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    {R η : ℝ} (hη : 0 < η)
    (hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖) :
    ({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard ≤
      ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
        Finset.Icc (-⌈R / η⌉) ⌈R / η⌉).card : ℕ∞) := by
  classical
  let S : Set ι := {a | ∀ k i j, ‖x a k i j‖ ≤ R}
  let val : ι → Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℝ := fun a t =>
    if t.2.2.2 then (x a t.1 t.2.1 t.2.2.1).re else (x a t.1 t.2.1 t.2.2.1).im
  let φ : ι → (Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℤ) := fun a t => ⌊val a t / η⌋
  have hmaps : ∀ a ∈ S, φ a ∈ Fintype.piFinset (fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
      Finset.Icc (-⌈R / η⌉) ⌈R / η⌉) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro t
    rw [Finset.mem_Icc]
    have hb := ha t.1 t.2.1 t.2.2.1
    have hv : |val a t| ≤ R := by
      simp only [val]
      split_ifs
      · exact (Complex.abs_re_le_norm _).trans hb
      · exact (Complex.abs_im_le_norm _).trans hb
    rw [abs_le] at hv
    have h1 : -(R / η) ≤ val a t / η := by rw [← neg_div]; exact div_le_div_of_nonneg_right hv.1 hη.le
    have h2 : val a t / η ≤ R / η := div_le_div_of_nonneg_right hv.2 hη.le
    constructor
    · apply Int.le_floor.2
      push_cast
      linarith [Int.le_ceil (R / η)]
    · exact Int.cast_le.1 ((Int.floor_le _).trans (h2.trans (Int.le_ceil _)))
  have hinj : Set.InjOn φ S := by
    intro a ha b hb hab
    by_contra hne
    obtain ⟨k, i, j, hsep⟩ := hsep2 a ha b hb hne
    have hre := congrFun hab (k, i, j, true)
    have him := congrFun hab (k, i, j, false)
    simp only [φ, val, if_true, Bool.false_eq_true, if_false] at hre him
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hre
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor him
    rw [← sub_div, abs_div, abs_of_pos hη, div_lt_one hη] at h1 h2
    have h3 := Complex.norm_le_abs_re_add_abs_im (x b k i j - x a k i j)
    simp only [Complex.sub_re, Complex.sub_im] at h3
    rw [abs_sub_comm] at h1 h2
    linarith
  calc S.encard = (φ '' S).encard := hinj.encard_image.symm
    _ ≤ ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
          Finset.Icc (-⌈R / η⌉) ⌈R / η⌉ : Finset _) : Set _).encard :=
        Set.encard_le_encard (by rintro _ ⟨a, ha, rfl⟩; exact hmaps a ha)
    _ = _ := Set.encard_coe_eq_coe_finsetCard _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

