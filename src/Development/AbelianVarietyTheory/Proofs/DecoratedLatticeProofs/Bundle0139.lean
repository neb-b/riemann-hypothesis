module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfPsiE
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstVec

theorem first_col {K : Type} [CommRing K] {σ : ℕ} (T S : Matrix (Fin (σ + 1)) (Fin (σ + 1)) K) (h : S * T = 1)
    (hl : T (Fin.last σ) (Fin.last σ) = 1) (hu : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → ∀ a b, b ≤ a → T a j * S j' b = 0)
    (hs : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∑ a : Fin (σ + 1), ∑ b : Fin (σ + 1),
      if b.1 = a.1 + 1 then T a j * S j' b else 0) = 1) : ∀ a, T a 0 = if a = 0 then 1 else 0 := by
  have key : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∀ b, j' < b → T b j' = 0) → ∀ a, j ≤ a →
      T a j = if a = j then T j j * S j' j' * T j' j' else 0 := fun j j' e H a ha => by
    have e1 : T a j = ∑ b, T a j * S j' b * T b j' := by
      have := congrFun (congrFun h j') j'
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_one]
    rw [e1, Finset.sum_eq_single j']
    · split_ifs with h1
      · rw [h1]
      · rw [hu j j' e a j' (by rw [Fin.le_def] at *; have := mt Fin.ext h1; omega), zero_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h1 | h1
      · rw [hu j j' e a b (by rw [Fin.le_def, Fin.lt_def] at *; omega), zero_mul]
      · rw [H b h1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  have tri : ∀ j : Fin (σ + 1), ∀ b, j < b → T b j = 0 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact fun b hb => absurd (Fin.le_last b) (not_le.2 hb)
    | cast j ih => exact fun b hb => by rw [key j.castSucc j.succ rfl ih b hb.le, if_neg hb.ne']
  have triS : S.BlockTriangular id := by
    letI := invertibleOfLeftInverse T S h
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.blockTriangular_inv_of_blockTriangular fun a b hab => tri b a hab
  have diag : ∀ j : Fin (σ + 1), T j j = 1 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact hl
    | cast j ih =>
      have h1 := hs j.castSucc j.succ rfl
      rw [Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ, if_pos (show j.succ.1 = j.castSucc.1 + 1 from rfl)] at h1
      · rw [key j.castSucc j.succ rfl (tri _) _ le_rfl, if_pos rfl, h1, ih, one_mul]
      · exact fun b _ hb => if_neg fun e => hb (Fin.ext e)
      · exact fun h => absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with e
        · rcases lt_or_gt_of_ne ha with h2 | h2
          · rw [show S j.succ b = 0 from triS (show b < j.succ by
              rw [Fin.lt_def] at h2 ⊢; simp only [Fin.val_castSucc, Fin.val_succ] at h2 e ⊢; omega), mul_zero]
          · rw [tri _ a h2, zero_mul]
        · rfl
      · exact fun h => absurd (Finset.mem_univ _) h
  intro a
  split_ifs with e
  · rw [e, diag]
  · exact tri 0 a (Fin.pos_iff_ne_zero.2 e)

variable {D : D7} {S S₀ S₀' : HSp D}

theorem eq_of_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∃ s : AE D, psiE ψ s ≠ 1) {s s' : D.host.E}
    (h : ∀ t : AE D, psiE ψ (t * incA D s) = psiE ψ (t * incA D s')) : s = s' := by
  by_contra hne
  obtain ⟨y, hy⟩ := hψ
  have h0 : s - s' ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (y * incA D (s - s')⁻¹)
  have e : y * incA D (s - s')⁻¹ * incA D s = y + y * incA D (s - s')⁻¹ * incA D s' := by
    have : incA D (s - s')⁻¹ * (incA D s - incA D s') = 1 := by rw [← map_sub, ← map_mul, inv_mul_cancel₀ h0, map_one]
    linear_combination y * this
  rw [e, psiE_add] at h1
  have h2 : psiE ψ (y * incA D (s - s')⁻¹ * incA D s') * psiE ψ (-(y * incA D (s - s')⁻¹ * incA D s')) = 1 := by
    rw [← psiE_add, add_neg_cancel, psiE_zero]
  exact hy (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans (one_mul _).symm))

section

variable {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ) {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E}

theorem exists_b (hz' : z' ≠ 0) (i : Fin ρ) (t : AE D) : ∃ b : Mx D ρ S₀'.rank, b *ᵥ ratV z' = Pi.single i t := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hz'
  refine ⟨Matrix.single i k (t * incA D (z' k)⁻¹), ?_⟩
  rw [Matrix.single_mulVec]
  change Function.update (0 : Fin ρ → AE D) i (t * incA D (z' k)⁻¹ * incA D (z' k)) = _
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one]
  rfl

theorem coefX_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (n : GA D S) :
    coefX d z n = d.pX *ᵥ (mt S n *ᵥ (d'.j0 *ᵥ ratV z')) := by
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  rw [coefX, ← mulVec_mulVec, ← mulVec_mulVec, e]

theorem coefX_nB' (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (b : Mx D ρ S₀'.rank) :
    coefX d z (d'.nB b) = (d.pX * d'.jX) *ᵥ (b *ᵥ ratV z') := by
  have e0 : d.pX *ᵥ (d'.j0 *ᵥ ratV z') = 0 := by
    have := coefX_eq d d' hz 1
    rw [GlobalTheory.MixModel.mt_one, one_mulVec, coefX, GlobalTheory.MixModel.mt_one, Matrix.one_mul, d.pX_j0, zero_mulVec] at this
    exact this.symm
  rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.nB_j0, add_mulVec, mulVec_add, e0, zero_add]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem e_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz' : z' ≠ 0) (hN : ∀ n ∈ flagN d', n ∈ flagN d) : d'.e = d.e * (d.qX * d'.e) := by
  apply rat_injective
  rw [rat_mul, rat_mul]
  change d'.jX = d.jX * (d.pX * d'.jX)
  ext k i : 2
  obtain ⟨b, hb⟩ := exists_b hz' i 1
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  obtain ⟨u, -, b₁, c, hn⟩ := Decomp.flag_decomp d (hN _ (d'.nB_mem_NFlag b))
  have h1 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ ((u.1 * b₁) *ᵥ ratV z) := by
    rw [hn, mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, add_mulVec, mulVec_mulVec]
  have h2 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d'.jX *ᵥ Pi.single i 1 := by
    rw [e, mulVec_mulVec, d'.nB_j0, add_mulVec, ← mulVec_mulVec, hb]
  have h3 := add_left_cancel (h2.symm.trans h1)
  have h4 : (d.jX * (d.pX * d'.jX)) *ᵥ Pi.single i 1 = d'.jX *ᵥ Pi.single i 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h3, mulVec_mulVec _ d.pX, d.pX_jX, one_mulVec]
  have := congrFun h4 k
  simp only [mulVec_single_one] at this
  exact this.symm

end

theorem first_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ)
    {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E} (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz0 : z ≠ 0) (hz' : z' ≠ 0)
    (hN : ∀ n, n ∈ flagN d ↔ n ∈ flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n)
    (r : Fin ρ) (hr : r.1 = 0) (k : Fin S.rank) : d'.e k r = d.e k r := by
  obtain _ | σ := ρ
  · exact r.elim0
  obtain rfl : r = 0 := Fin.ext hr
  have hne := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
  have e1 := e_eq d d' hz hz' fun n => (hN n).2
  have e2 := e_eq d' d hz.symm hz0 fun n => (hN n).1
  have q1 : d'.qX * d'.e = 1 := d'.e'e
  have hT : (rat (d.qX * d'.e) : Mx D _ _) = d.pX * d'.jX := rat_mul _ _
  generalize d.qX * d'.e = T at e1 hT
  generalize hS : d'.qX * d.e = S' at e2
  have hST : S' * T = 1 := by rw [← hS, Matrix.mul_assoc, ← e1, q1]
  have hX : d.jX = d'.jX * rat S' := (congrArg rat e2).trans (rat_mul _ _)
  have hTS : (rat T : Mx D _ _) * rat S' = 1 := by rw [← rat_mul, mul_eq_one_comm.1 hST, rat_one]
  have hell : ∀ y : Fin (σ + 1) → AE D, ell D (σ + 1) ⬝ᵥ y = y (Fin.last σ) := fun y => by
    rw [dotProduct, Finset.sum_eq_single (Fin.last σ)]
    · simp [ell]
    · intro b _ hb
      rw [ell, if_neg fun e => hb (Fin.ext (by simpa using e)), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hA : ∀ (j j' : Fin (σ + 1)) (t : AE D), j'.1 = j.1 + 1 → ∃ u ∈ UX D (σ + 1), u.1 = 1 + Matrix.single j j' t ∧
      blockX d (d'.levi u) = 1 + Matrix.of fun a b => t * incA D (T a j * S' j' b) := fun j j' t e => by
    obtain ⟨u, hu, hu1⟩ := Decomp.exists_unit (D := D) (T := Matrix.single j j' t) fun a b hab =>
      Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; rw [Fin.le_def] at hab; omega)
    refine ⟨u, hu, hu1, ?_⟩
    rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.levi_jX, hu1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hT,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS]
    congr 1
    ext a b : 2
    rw [Matrix.mul_apply, Finset.sum_eq_single j', Matrix.mul_single_apply_same, Matrix.of_apply, map_mul]
    · change incA D (T a j) * t * incA D (S' j' b) = _
      ring
    · intro c _ hc
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have H := first_col T S' hST ?_ ?_ ?_
  · rw [e1, Matrix.mul_apply]
    simp only [H, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine eq_of_psiE hne fun t => ?_
    obtain ⟨b, hb⟩ := exists_b hz' (Fin.last σ) t
    have h1 := hc _ ((hN _).2 (d'.nB_mem_NFlag b))
    have h2 : blockX d (d'.nB b) = 1 := by
      rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.nB_jX, ← hX, d.pX_jX]
    rw [psiBes_nB, psiBes, simpleSum, h2, upSum_one, zero_add, coefX_nB' d d' hz, hb, hell, hell, ← hT, mulVec_single] at h1
    simp only [map_one, one_mul, Pi.single_eq_same, mul_one] at h1 ⊢
    rw [mul_comm t]
    exact h1
  · intro j j' e a b hab
    obtain ⟨u, hu, -, h2⟩ := hA j j' 1 e
    obtain ⟨u₁, hu₁, b₁, c, hn⟩ := Decomp.flag_decomp d ((hN _).2 (d'.levi_mem_NFlag hu))
    rw [blockX, hn, Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h2
    have h3 := congrFun (congrFun h2 a) b
    rw [Matrix.add_apply, Matrix.of_apply, one_mul] at h3
    have h4 : u₁.1 a b = (1 : Mx D (σ + 1) (σ + 1)) a b := by
      rcases eq_or_lt_of_le hab with rfl | h
      · rw [(hu₁ b b).2, Matrix.one_apply_eq]
      · rw [(hu₁ a b).1 h, Matrix.one_apply_ne h.ne']
    rw [h4, left_eq_add] at h3
    exact incA_injective (h3.trans (map_zero _).symm)
  · intro j j' e
    refine eq_of_psiE hne fun t => ?_
    obtain ⟨u, hu, h1, h2⟩ := hA j j' t e
    have h3 := hc _ ((hN _).2 (d'.levi_mem_NFlag hu))
    have h4 : coefX d z (d'.levi u) = 0 := by
      have := coefX_nB' d d' hz 0
      rw [zero_mulVec, mulVec_zero, coefX_eq d d' hz, d'.nB_zero, GlobalTheory.MixModel.mt_one, one_mulVec] at this
      rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.wittDecomp_levi_inclAnisotropic, this]
    have hadd : ∀ M : Mx D (σ + 1) (σ + 1), upSum (1 + M) = upSum M := fun M =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        split_ifs with h
        · rw [Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega), zero_add]
        · rfl
    have h5 : upSum (Matrix.single j j' t : Mx D (σ + 1) (σ + 1)) = t := by
      rw [upSum, Finset.sum_eq_single j, Finset.sum_eq_single j', if_pos e, Matrix.single_apply_same]
      · exact fun b _ hb => if_neg fun e' => hb (Fin.ext (e'.trans e.symm))
      · exact fun h => absurd (Finset.mem_univ _) h
      · exact fun a _ ha => Finset.sum_eq_zero fun b _ => by
          rw [Matrix.single_apply_of_row_ne ha.symm, ite_self]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [psiBes_levi, psiUni, h1, hadd, h5, psiBes, simpleSum, h2, h4, hadd, dotProduct_zero, add_zero, map_one, one_mul] at h3
    rw [map_one, mul_one, ← h3]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [upSum, map_sum, Finset.mul_sum, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

end GlobalTheory.FirstVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridgeInhab

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_eq_one_of_sub_one {x : k} (hx : valuation k (x - 1) < 1) : valuation k x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (valuation k) (x := x - 1) (y := 1) (by simpa using hx)
  simpa using h

def delta (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) : kˣ →* ℂˣ := μ₁ * GlobalTheory.SmGL.unrChar k (μ₁ ϖ)⁻¹

theorem delta_unit (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) {x : kˣ} (hx : valuation k (x : k) = 1) : delta μ₁ ϖ x = μ₁ x := by
  simp [delta, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]

theorem delta_tame {μ₁ : kˣ →* ℂˣ} (h : IsTame μ₁) (ϖ : kˣ) : IsTame (delta μ₁ ϖ) := by
  intro x hx
  rw [delta_unit μ₁ ϖ (val_eq_one_of_sub_one hx)]
  exact h x hx

def eta (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) (j : ℕ) : kˣ →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ m then μ j * δ⁻¹ else 1

theorem eta_mul (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) {i : ℕ} (hi : i < m) :
    eta μ m δ (i + 1) * δ = μ (i + 1) := by
  rw [eta, if_pos ⟨by omega, by omega⟩, inv_mul_cancel_right]

theorem eta_unram (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ)
    (h : ∀ i, i < m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x) (j : ℕ) : IsUnram (eta μ m δ j) := by
  intro x hx
  unfold eta
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h i (by omega) x hx, mul_inv_cancel]
  · rfl

theorem exists_near {E : Type} [Field E] {ι : E →+* k} (hd : DenseRange ι) (x : k) :
    ∃ a : E, valuation k (ι a - x) < 1 := by
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hU
  exact ⟨a, hy⟩

theorem tame_near {μ : kˣ →* ℂˣ} (h : IsTame μ) {x u : kˣ} (hx : valuation k (x : k) = 1)
    (hu : valuation k ((u : k) - x) < 1) : μ u = μ x := by
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hy : valuation k (((x⁻¹ * u : kˣ) : k) - 1) < 1 := by
    have e : ((x⁻¹ * u : kˣ) : k) - 1 = (x : k)⁻¹ * ((u : k) - x) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hu
  have := h _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

end Loc

section Arith
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem unitV_inv {P : HeightOneSpectrum (𝓞 E)} (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    LocE.unitV χ⁻¹ a = (LocE.unitV χ a)⁻¹ := by
  unfold LocE.unitV
  split_ifs <;> simp

theorem valuation_self (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) :
    LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

theorem locChar_q {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) (cq : K)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (q : E) = cq := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : redP P (1 : E) = 1 := by
    have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
    rw [h3, reduction_coe, map_one]
  have hu : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.locChar
  rw [valuation_self P q hq h0, zpow_one, zpow_one, div_self hqE]
  unfold LocE.unitV
  rw [dite_eq_left hu]
  have h2 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1]; rfl)
  rw [h2, map_one, Units.val_one, mul_one]

end Arith

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem muAt_unit (hP : P.1 ∉ Pr.vGs) (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
    muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
  unfold muAt
  rw [if_neg hP]
  exact GlobalTheory.LastSteps.locChar_unit _ _ ha

theorem muAt_q (hP : P.1 ∉ Pr.vGs) (i : ℕ) (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal) (h0 : 0 < qOf P.1) :
    muAt Ch sel mu cst i P ((qOf P.1 : ℕ) : X.E) = cst.muq (i + 1) P := by
  unfold muAt
  rw [if_neg hP]
  exact locChar_q _ hq h0 _ _

end Chain

theorem exists_twData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2

  have hunit : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = μ 1 x := by
    intro i hi x hx
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, muAt_unit Ch sel mu cst P hP i hred, muAt_unit Ch sel mu cst P hP 0 hred]
  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = delta (μ 1) ϖ x := by
    intro i hi x hx
    rw [delta_unit _ _ hx]; exact hunit i hi x hx

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, delta (μ 1) ϖ, delta_tame ht1 ϖ, eta μ R.m (delta (μ 1) ϖ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  ·
    intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  ·
    intro a u ha hr hu
    show ((delta (μ 1) ϖ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [delta_unit _ _ hva, hμ1 a u hu, muAt_unit Ch sel mu cst P hP 0 hr, unitV_inv, map_inv₀]
  ·
    intro i hi
    show ((eta μ R.m (delta (μ 1) ϖ) (i + 1) * delta (μ 1) ϖ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, muAt_q Ch sel mu cst P hP i hqmem hqpos]

end GlobalTheory.TwBridgeInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistIndexRepresentativeOfBounds
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.MRepsPick

theorem exists_rep_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ j c h γ hγ hal hne
  classical
  obtain ⟨b₀⟩ := hne
  have hj : j < s := by omega
  let hh : rowSG Pr sel mu → AutY X R (j + 1) := fun P' => if P' = P then γ else L.h (j + 1) b₀ P'
  obtain ⟨b, hb⟩ := hL.surj j hj hh
    (by
      intro P' hP'
      have hne : P' ≠ P := by
        rintro rfl
        exact hA.nmem hP'
      simp only [hh, ite_eq_right hne]
      exact hL.stabG (j + 1) b₀ P' hP')
    (by
      intro P' hP'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, ite_eq_left rfl]
        exact hγ
      · simp only [hh, ite_eq_right hPP]
        exact hL.boundQ (j + 1) b₀ P' hP')
    (by
      intro P'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, ite_eq_left rfl]
        exact hal
      · simp only [hh, ite_eq_right hPP]
        exact hL.nonvan j hj b₀ P')
  refine ⟨b, ?_⟩
  have := hb P
  simpa [hh] using this

end GlobalTheory.MRepsPick
end

