module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cdo_matrix {ι κ : Type} [Fintype ι] [Fintype κ] {s : Set E} {M : E → Matrix ι κ ℂ} :
    ContDiffOn ℂ ∞ M s ↔ ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s := by
  constructor
  · intro h i j
    have h1 : ContDiffOn ℂ ∞ (fun x => M x i) s := (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).1 h i
    exact (contDiffOn_pi (Φ := fun x => M x i)).1 h1 j
  · intro h
    exact (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).2 fun i =>
      (contDiffOn_pi (Φ := fun x => M x i)).2 fun j => h i j

theorem cdo_det {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (h : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem cdo_zpow {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (k : ℤ) :
    ContDiffOn ℂ ∞ (fun x => f x ^ k) s := by
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast] using hf.pow j
  · refine ((hf.pow j).inv fun x hx => pow_ne_zero j (h0 x hx)).congr fun x _ => ?_
    simp [_root_.zpow_neg]

theorem cd_entry {ι κ : Type} [Fintype ι] [Fintype κ] (i : ι) (j : κ) :
    ContDiff ℂ ∞ (fun x : Matrix ι κ ℂ => x i j) :=
  contDiff_apply_apply (𝕜 := ℂ) (E := ℂ) i j

theorem contDiff_first_cayley_block : ContDiff ℂ ∞ (u1 (n := n)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  refine (cdo_matrix (s := Set.univ)).2 (fun i j => ?_) |>.contDiffAt Filter.univ_mem
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((contDiff_const.mul (cd_entry _ _)).add (cd_entry _ _)).contDiffOn

theorem contDiff_second_cayley_block : ContDiff ℂ ∞ (u2 (n := n)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  refine (cdo_matrix (s := Set.univ)).2 (fun i j => ?_) |>.contDiffAt Filter.univ_mem
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact ((contDiff_const.mul (cd_entry _ _)).neg.add (cd_entry _ _)).contDiffOn

theorem cdo_mul {ι κ μ' : Type} [Fintype ι] [Fintype κ] [Fintype μ'] {s : Set E} {M : E → Matrix ι κ ℂ}
    {N : E → Matrix κ μ' ℂ} (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s)
    (hN : ∀ i j, ContDiffOn ℂ ∞ (fun x => N x i j) s) : ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x * N x) i j) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hM i k).mul (hN k j)

theorem cdo_inv {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) (h0 : ∀ x ∈ s, (M x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x)⁻¹ i j) s := by
  intro i j
  have e : ∀ x, (M x)⁻¹ i j = ((M x).det)⁻¹ * ((M x).updateRow j (Pi.single i 1)).det := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ((cdo_det hM).inv h0).mul (cdo_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM a b

theorem contDiffOn_first_cayley_block_entries (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x => u1 x i j) s := fun i j =>
  ((cdo_matrix (M := u1 (n := n)) (s := s)).1 contDiff_first_cayley_block.contDiffOn) i j

theorem contDiffOn_second_cayley_block_entries (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x => u2 x i j) s := fun i j =>
  ((cdo_matrix (M := u2 (n := n)) (s := s)).1 contDiff_second_cayley_block.contDiffOn) i j

theorem cdo_id (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => x i j) s := fun i j =>
  (cd_entry i j).contDiffOn

theorem cdo_wM (s : Set (M2 n)) (hs : ∀ x ∈ s, (u2 x).det ≠ 0) : ∀ i j, ContDiffOn ℂ ∞ (fun x => wM x i j) s :=
  cdo_mul (cdo_inv (contDiffOn_second_cayley_block_entries s) hs) (contDiffOn_first_cayley_block_entries s)

theorem det_wM (x : M2 n) (h2 : (u2 x).det ≠ 0) : (wM x).det = ((u2 x).det)⁻¹ * (u1 x).det := by
  rw [wM, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem cdo_wM_inv (s : Set (M2 n)) (hs : ∀ x ∈ s, (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (wM x)⁻¹ i j) s :=
  cdo_inv (cdo_wM s fun x hx => (hs x hx).2) fun x hx => by
    rw [det_wM x (hs x hx).2]; exact mul_ne_zero (inv_ne_zero (hs x hx).2) (hs x hx).1

theorem cdo_minorOn {s : Set E} (t : Finset (Fin n)) {M : E → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => minorOn t (M x)) s :=
  cdo_det fun i j => hM _ _

theorem contDiffOn_inverse_first_block (s : Set (M2 n)) (hs : ∀ x ∈ s, IsUnit x.det) : ∀ i j, ContDiffOn ℂ ∞ (fun x => ub1 x i j) s := by
  intro i j
  have hinv := cdo_inv (cdo_id s) fun x hx => (hs x hx).ne_zero
  simp only [ub1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (hinv _ _).add (contDiffOn_const.mul (hinv _ _))

theorem contDiffOn_scalar_section_of_units (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := by
  unfold f0
  exact (cdo_zpow (cdo_det (contDiffOn_first_cayley_block_entries _)) (by exact fun x hx => hx.1) _).mul (cdo_zpow (cdo_det (contDiffOn_second_cayley_block_entries _)) (by exact fun x hx => hx.2) _)

theorem dom_sub (x : M2 n) (hx : x ∈ Dom n) : (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 := ⟨hx.2.1, hx.2.2.1⟩

theorem contDiffOn_hF' (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := by
  unfold hF
  refine (((contDiffOn_scalar_section_of_units p q).mono fun x hx => dom_sub x hx).mul
    (cdo_minorOn _ (cdo_wM _ fun x hx => hx.2.2.1))).mul (cdo_minorOn _ (cdo_wM_inv _ dom_sub))

theorem contDiffOn_fV' (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := by
  unfold fV
  exact ((cdo_zpow (cdo_det (contDiffOn_first_cayley_block_entries _)) (by exact fun x hx => hx.2.1) _).mul
    (cdo_zpow (cdo_det (contDiffOn_second_cayley_block_entries _)) (by exact fun x hx => hx.2.2.1) _)).mul
    (cdo_zpow (cdo_det (contDiffOn_inverse_first_block _ (by exact fun x hx => hx.1))) (by exact fun x hx => hx.2.2.2) _)

def Cinv (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)

theorem Cm_mul_Cinv : Cm n * Cinv n = 1 := by
  have hI : (2 * Complex.I) ≠ 0 := by simp
  rw [Cm, Cinv, Matrix.mul_smul, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
      smul_eq_mul, Matrix.smul_apply] <;>
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, one_mul, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    split_ifs <;> (try simp_all) <;> (try split_ifs) <;> (try simp_all) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)

theorem Cm_inv : (Cm n)⁻¹ = Cinv n := Matrix.inv_eq_right_inv Cm_mul_Cinv

theorem Cinv_mul_Cm : (Cm n)⁻¹ * Cm n = 1 := by
  rw [Matrix.nonsing_inv_mul]
  exact (Matrix.isUnit_det_of_right_inverse Cm_mul_Cinv)

theorem Cm_mul_inv : Cm n * (Cm n)⁻¹ = 1 := by rw [Cm_inv]; exact Cm_mul_Cinv

theorem fromBlocks_one_eq (Q R : Matrix (Fin n) (Fin n) ℂ) :
    (fromBlocks 1 Q R 1 : M2 n) = 1 + fromBlocks 0 Q R 0 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp

theorem mX_eq' (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹ := by
  rw [mX, fromBlocks_one_eq, Matrix.mul_add, Matrix.add_mul, mul_one, Cm_mul_inv]

theorem embOn_mul_embOn_disj {s t : Finset (Fin n)} (hst : ∀ c, c ∈ s → c ∉ t) (T : Matrix s s ℂ) (S : Matrix t t ℂ) :
    embOn s T * embOn t S = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply, embOn]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : a ∈ s ∧ c ∈ s
  · by_cases h2 : c ∈ t ∧ b ∈ t
    · exact absurd h2.1 (hst c h1.2)
    · rw [dite_eq_right h2, mul_zero]
  · rw [dite_eq_right h1, zero_mul]

theorem WD_prod (Q R Q' R' : Matrix (Fin n) (Fin n) ℂ) :
    (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * fromBlocks (Q * R') 0 0 (R * Q') * (Cm n)⁻¹ := by
  have e : (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * (fromBlocks 0 Q R 0 * ((Cm n)⁻¹ * Cm n) * fromBlocks 0 Q' R' 0) * (Cm n)⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, Cinv_mul_Cm, mul_one, Matrix.fromBlocks_multiply]
  simp

def mulLc (M : M2 n) : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ M)

theorem mulLc_apply (M v : M2 n) : mulLc M v = M * v := rfl

def mulLcL : M2 n →ₗ[ℂ] (M2 n →L[ℂ] M2 n) where
  toFun := mulLc
  map_add' a b := by ext1 v; simp [mulLc_apply, Matrix.add_mul]
  map_smul' c a := by ext1 v; simp [mulLc_apply, Matrix.smul_mul]

theorem continuous_mulLc : Continuous (fun M : M2 n => mulLc M) :=
  (mulLcL (n := n)).continuous_of_finiteDimensional

theorem left_mul' (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (M x : M2 n)
    (hx : M * x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F (M * y)) x v = iteratedFDeriv ℂ N F (M * x) (fun i => M * v i) := by
  have hV' : IsOpen (mulLc M ⁻¹' U) := hU.preimage (mulLc M).continuous
  have key := (mulLc M).iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hV'.uniqueDiffOn
    (show mulLc M x ∈ U from hx) (i := N) (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ N (F ∘ mulLc M) (mulLc M ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ mulLc M) x :=
    iteratedFDerivWithin_of_isOpen N hV' (show x ∈ mulLc M ⁻¹' U from hx)
  have e2 : iteratedFDerivWithin ℂ N F U (mulLc M x) = iteratedFDeriv ℂ N F (mulLc M x) :=
    iteratedFDerivWithin_of_isOpen N hU (show mulLc M x ∈ U from hx)
  have key' : iteratedFDeriv ℂ N (F ∘ mulLc M) x =
      (iteratedFDeriv ℂ N F (mulLc M x)).compContinuousLinearMap (fun _ => mulLc M) :=
    e1.symm.trans (key.trans (congrArg (fun A => ContinuousMultilinearMap.compContinuousLinearMap A
      (fun _ : Fin N => mulLc M)) e2))
  exact congrArg (fun A => A v) key'

theorem cont_translate' (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by
  set Φ := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ (fun _ : Fin N => M2 n)
    (fun _ : Fin N => M2 n) ℂ with hΦ
  have h1 : ContinuousOn (iteratedFDeriv ℂ N F) U :=
    (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)
  have hA : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2))
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) :=
    h1.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)
  have hL : Continuous (fun y : Kg × M2 n => Φ (fun _ => mulLc (ι y.1))) :=
    Φ.cont.comp (continuous_pi fun _ => continuous_mulLc.comp (hι.comp continuous_fst))
  refine (((hc.comp continuous_fst).continuousOn).smul (hL.continuousOn.clm_apply hA)).congr ?_
  intro y hy
  have hyU : ι y.1 * y.2 ∈ U := hy.2 y.1
  have hcd : ContDiffAt ℂ N (fun x => F (ι y.1 * x)) y.2 :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).comp y.2 (mulLc (ι y.1)).contDiff.contDiffAt).of_le
      (by exact_mod_cast le_top)
  have e : (fun x => F (ι y.1 * x) * c y.1) = c y.1 • (fun x => F (ι y.1 * x)) := by
    funext x; simp [smul_eq_mul, mul_comm]
  ext v
  simp only [Function.comp_apply]
  rw [e, iteratedFDeriv_const_smul_apply hcd, _root_.smul_apply, smul_eq_mul,
    left_mul' F U hU hF (ι y.1) y.2 hyU N v]
  rfl

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isymm (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n G x (u ∘ π) = iteratedFDeriv ℂ n G x u :=
  hG.contDiffAt.iteratedFDeriv_comp_perm u π

theorem ipeel0 (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u 0)) x (fun k => u k.succ) := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ G) x := (hG.contDiffAt (n := ω)).fderiv_right le_top
  have happ := (ContinuousLinearMap.apply ℂ ℂ (u 0)).iteratedFDeriv_comp_left hfd (i := n) le_rfl
  have hfun : (fun y => fderiv ℂ G y (u 0)) = (ContinuousLinearMap.apply ℂ ℂ (u 0)) ∘ fderiv ℂ G := rfl
  rw [← isymm G x hG (n + 1) u (finRotate (n + 1)), iteratedFDeriv_succ_apply_right, hfun, happ]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, finRotate_last]
  congr 2
  funext k
  simp [Fin.init, finRotate_apply, Fin.coeSucc_eq_succ]

theorem ipeel (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by
  rw [← isymm G x hG (n + 1) u i0.cycleRange.symm, ipeel0 G x hG n]
  simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]

theorem detD_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
  have hgen : ∀ (m : ℕ) (h : m = N) (e : Fin m ≃ Fin N) (σ : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ m G 0 (fun i => Matrix.single (e i) (σ (e i)) (1 : ℂ)) =
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
    intro m h e σ
    subst h
    exact isymm G 0 hG m (fun k => Matrix.single k (σ k) 1) e
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hgen _ (Fintype.card_fin N) _ σ]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivEqZeroOfVanish
section
noncomputable section

open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC

variable {n : ℕ}

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem det_ne_zero_of_inG {y : M2 n} (hy : InG y) : y.det ≠ 0 := by
  intro h
  have hJ : (JJ n).det ≠ 0 := by
    intro hJ
    have := congrArg Matrix.det (JJ_sq (n := n))
    rw [det_mul, hJ, mul_zero, det_neg, det_one] at this
    simp at this
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, h, mul_zero] at this
  exact hJ this.symm

theorem fderiv_eq_zero_of_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) {H : M2 n → V} (hH : ContDiffOn ℂ ∞ H Ω)
    (h0 : ∀ g, InG g → H g = 0) {y : M2 n} (hy : InG y) : fderiv ℂ H y = 0 := by
  have hdiff : ∀ g, InG g → DifferentiableAt ℂ H g := fun g hg =>
    (hH.contDiffAt (hΩ.mem_nhds (hG hg))).differentiableAt (by simp)
  have hlow : ∀ g, InG g → ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c →
      fderiv ℂ H g (g * fromBlocks 0 0 c 0) = 0 := by
    intro g hg c hc
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [lower_line, h0 _ (inG_mul hg (inG_lower (herm_real_smul hc t))), h0 g hg]
  have hup : ∀ g, InG g → ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      fderiv ℂ H g (g * fromBlocks 0 b 0 0) = 0 := by
    intro g hg b hb
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [upper_line, h0 _ (inG_mul hg (inG_upper (herm_real_smul hb t))), h0 g hg]
  have hone : fderiv ℂ H y (y * 1) = 0 := by
    rw [mul_one]
    refine HolD.scalar_dir (hdiff y hy) (fun t => h0 _ ?_)
    have e : Complex.exp (↑t * Complex.I) • y = y * (Complex.exp (↑t * Complex.I) • (1 : M2 n)) := by
      rw [mul_smul_comm, mul_one]
    rw [e]
    refine inG_mul hy (inG_scalar ?_)
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
    simp
  have hCy : ContDiffAt ℂ ∞ H y := hH.contDiffAt (hΩ.mem_nhds (hG hy))
  have hsymm : IsSymmSndFDerivAt ℂ H y :=
    hCy.isSymmSndFDerivAt (by simpa [minSmoothness_of_isRCLikeNormedField] using two_le_infty)
  have hD : DifferentiableAt ℂ (fderiv ℂ H) y :=
    (hCy.fderiv_right (m := 1) (by simpa [one_add_one_eq_two] using two_le_infty)).differentiableAt one_ne_zero
  have hcomm : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c →
      fderiv ℂ H y (y * fromBlocks (-(b * c)) 0 0 (c * b)) = 0 := by
    intro b c hb hc
    set U : M2 n := fromBlocks 0 b 0 0 with hU
    set L : M2 n := fromBlocks 0 0 c 0 with hL
    let mL : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ L)
    let mU : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ U)
    have e1 := HolD.line2 (H := H) (y := y) (w := y * U) (m := mL) hD (fun t => by
      have hg := inG_mul hy (inG_upper (herm_real_smul hb t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * U)) * L) = 0
      rw [upper_line]
      exact hlow _ hg c hc)
    have e2 := HolD.line2 (H := H) (y := y) (w := y * L) (m := mU) hD (fun t => by
      have hg := inG_mul hy (inG_lower (herm_real_smul hc t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * L)) * U) = 0
      rw [lower_line]
      exact hup _ hg b hb)
    change fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) + fderiv ℂ H y (y * U * L) = 0 at e1
    change fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) + fderiv ℂ H y (y * L * U) = 0 at e2
    have key : fromBlocks (-(b * c)) 0 0 (c * b) = L * U - U * L := by
      simp only [hU, hL, Matrix.fromBlocks_multiply]
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp
    rw [key, mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
    have a1 := eq_neg_of_add_eq_zero_right e1
    have a2 := eq_neg_of_add_eq_zero_right e2
    have hs : fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) = fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) :=
      hsymm _ _
    rw [sub_eq_zero]
    exact a2.trans ((congrArg Neg.neg hs).trans a1.symm)
  let W : Submodule ℂ (M2 n) :=
    LinearMap.ker ((fderiv ℂ H y : M2 n →ₗ[ℂ] V) ∘ₗ LinearMap.mulLeft ℂ y)
  have hW : W = ⊤ :=
    span_top W (fun b hb => LinearMap.mem_ker.mpr (hup y hy b hb))
      (fun c hc => LinearMap.mem_ker.mpr (hlow y hy c hc))
      (fun b c hb hc => LinearMap.mem_ker.mpr (hcomm b c hb hc))
      (LinearMap.mem_ker.mpr hone)
  have hdet : IsUnit y.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_inG hy)
  ext u
  have hu : y⁻¹ * u ∈ W := hW ▸ Submodule.mem_top
  have e := LinearMap.mem_ker.mp hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    ContinuousLinearMap.coe_coe, Matrix.mul_nonsing_inv_cancel_left _ _ hdet] at e
  simpa using e

theorem nat_lt_infty (N : ℕ) : ((N : ℕ) : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top N)

private theorem iteratedFDeriv_eq_zero_of_eq_zero_on_inG {n : ℕ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) (N : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (H : M2 n → V),
      ContDiffOn ℂ ∞ H Ω → (∀ g, InG g → H g = 0) → ∀ g, InG g → iteratedFDeriv ℂ N H g = 0 := by
  induction N with
  | zero =>
    intro V _ _ _ H _ h0 g hg
    ext v
    simp [h0 g hg]
  | succ N ih =>
    intro V _ _ _ H hH h0 g hg
    have hH' := (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hH
    letI : NormedAddCommGroup (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℂ (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
    haveI : SequentialSpace (M2 n) :=
      inferInstanceAs (SequentialSpace ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
    haveI : @CompleteSpace (M2 n →L[ℂ] V) PseudoMetricSpace.toUniformSpace :=
      ContinuousLinearMap.instCompleteSpace
    have e : iteratedFDeriv ℂ N (fun y => fderiv ℂ H y) g = 0 :=
      ih (fun y => fderiv ℂ H y) hH'.2 (fun g' hg' => fderiv_eq_zero_of_vanish hΩ hG hH h0 hg') g hg
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
    have e' := congrArg (continuousMultilinearCurryRightEquiv' ℂ N (M2 n) V).symm e
    exact e'.trans (map_zero _)

theorem holZero : HolZero := by
  intro n Ω F hΩ hG hF h0 N g hg
  exact iteratedFDeriv_eq_zero_of_eq_zero_on_inG hΩ hG N F hF (fun g hg => h0 g hg) g hg

private theorem contDiffOn_integral_and_iteratedFDeriv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] {Ω : Set E} (F : Kg → E → ℂ) (hΩ : IsOpen Ω)
    (hcont : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (F y.1) y.2) (univ ×ˢ Ω))
    (hF : ∀ k, ContDiffOn ℂ ∞ (F k) Ω) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : E) (v : Fin N → E), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ := by
  have hFd : ∀ k, ∀ x ∈ Ω, ContDiffAt ℂ ∞ (F k) x := fun k x hx =>
    (hF k).contDiffAt (hΩ.mem_nhds hx)
  have hA : ∀ N : ℕ, ∀ x ∈ Ω, HasFDerivAt (fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (F k)) x ∂μ) x := by
    intro N x hx
    refine HolA.hasFDerivAt_int hΩ (hcont N) ?_ ?_ hx
    · have e : (fun y : Kg × E => fderiv ℂ (iteratedFDeriv ℂ N (F y.1)) y.2) =
          fun y => continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ
            (iteratedFDeriv ℂ (N + 1) (F y.1) y.2) := by
        funext y
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).continuous.comp_continuousOn
        (hcont (N + 1))
    · intro k x hx
      exact ((hFd k x hx).differentiableAt_iteratedFDeriv (by simpa using nat_lt_infty N)).hasFDerivAt
  have hB : ∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x =
      ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x _
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) =ᶠ[𝓝 x]
          fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hA N x hx).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℂ (iteratedFDeriv ℂ N (F k)) x)).symm
  have hD : ∀ m : ℕ, DifferentiableOn ℂ (fun x => iteratedFDerivWithin ℂ m (fun x => ∫ k, F k x ∂μ) Ω x) Ω :=
    fun m x hx => ((hA m x hx).differentiableAt.differentiableWithinAt).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen m hΩ hy).trans (hB m y hy))
      ((iteratedFDerivWithin_of_isOpen m hΩ hx).trans (hB m x hx))
  refine ⟨contDiffOn_of_continuousOn_differentiableOn (n := ⊤) (fun m _ => (hD m).continuousOn)
    (fun m _ => hD m), ?_⟩
  intro N x v hx
  rw [hB N x hx]
  have hint : Integrable (fun k => iteratedFDeriv ℂ N (F k) x) μ :=
    HolA.integrable_of_cont ((hcont N).comp_continuous (continuous_id.prodMk continuous_const)
      (fun k => ⟨mem_univ _, hx⟩))
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => E) ℂ v).integral_comp_comm hint).symm

theorem holInt : HolInt := by
  intro n Kg _ _ _ _ μ _ Ω F hΩ hcont hF
  exact contDiffOn_integral_and_iteratedFDeriv_integral μ F hΩ hcont hF

end PositivityTheory.Rg.Sw.LVs
end
end

