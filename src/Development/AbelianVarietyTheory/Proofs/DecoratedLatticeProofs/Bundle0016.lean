module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.SortedCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permUnitO {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) 𝒪[k] where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

def permUnit {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) (permUnitO σ)

theorem permUnit_mem_KO {N : ℕ} (σ : Equiv.Perm (Fin N)) : (permUnit σ : GL (Fin N) k) ∈ KO k (Fin N) :=
  ⟨permUnitO σ, rfl⟩

theorem permUnit_val {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((permUnit σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = σ.toPEquiv.toMatrix := by
  ext i j
  simp only [permUnit, permUnitO, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem conj_torusElt {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    permUnit σ * torusElt k (Fin N) ϖ m * (permUnit σ)⁻¹ = torusElt k (Fin N) ϖ (m ∘ σ) := by
  apply Units.ext
  have hinv : (((permUnit σ : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      σ.symm.toPEquiv.toMatrix := by
    show (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) = _
    exact PEquiv.map_toMatrix _ _
  rw [Units.val_mul, Units.val_mul, hinv, permUnit_val, torusElt, torusElt, val_diagT, val_diagT,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix]
  exact Matrix.submatrix_diagonal_equiv _ σ

theorem torusElt_conj {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    torusElt k (Fin N) ϖ m = (permUnit σ)⁻¹ * torusElt k (Fin N) ϖ (m ∘ σ) * permUnit σ := by
  rw [← conj_torusElt ϖ m σ]
  group

theorem cartan_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ' := by
  intro k _ _ _ _ N ϖ hϖ g
  obtain ⟨x, hx, y, hy, m, rfl⟩ := GlobalTheory.LocalCartan.cartan_decomposition k (Fin N) ϖ g hϖ
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin N), Monotone ((fun i => -m i) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  refine ⟨m ∘ σ, fun a b hab => ?_, x * (permUnit σ)⁻¹, mul_mem hx (inv_mem (permUnit_mem_KO σ)),
    permUnit σ * y, mul_mem (permUnit_mem_KO σ) hy, ?_⟩
  · have := hmono hab
    simp only [Function.comp_apply] at this ⊢
    omega
  · have h := torusElt_conj ϖ m σ
    rw [torusElt] at h
    rw [h]
    group

end GlobalTheory.SortedCartan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalField
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.CartanDom

theorem det_mul_eq_sum_fun {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

theorem prod_zpow_eq {G : Type*} [CommGroupWithZero G] {ι : Type*} (s : Finset ι) {x : G} (hx : x ≠ 0)
    (e : ι → ℤ) : ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hx, ih]

theorem sum_le_sum_of_threshold {α : Type*} [DecidableEq α] (e : α → ℤ) (U T : Finset α) (hc : T.card = U.card)
    (c : ℤ) (hU : ∀ i ∈ U, e i ≤ c) (hU' : ∀ i ∈ T, i ∉ U → c ≤ e i) : ∑ i ∈ U, e i ≤ ∑ i ∈ T, e i := by
  have h1 : ∑ i ∈ U ∩ T, (c - e i) ≤ ∑ i ∈ U, (c - e i) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun i hi _ => by linarith [hU i hi])
  have h2 : ∑ i ∈ U ∩ T, (e i - c) ≤ ∑ i ∈ T, (e i - c) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i hi hni => by
      have : i ∉ U := fun h => hni (Finset.mem_inter.2 ⟨h, hi⟩)
      linarith [hU' i hi this])
  simp only [Finset.sum_sub_distrib, Finset.sum_const, smul_eq_mul] at h1 h2
  rw [hc] at h2
  linarith

theorem sum_tail_le {N : ℕ} (e : Fin N → ℤ) (he : Antitone e) (j : ℕ) (hj : j < N)
    (f : {i : Fin N // ¬ (i : ℕ) < j} → Fin N) (hf : Function.Injective f) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), e i ≤ ∑ x, e (f x) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (fun a _ b _ h => hf h)]
  refine sum_le_sum_of_threshold e _ _ ?_ (e ⟨j, hj⟩) ?_ ?_
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_subtype]
  · intro i hi
    exact he (Fin.le_iff_val_le_val.2 (by simp at hi; simpa using hi))
  · intro i _ hi
    exact he (Fin.le_iff_val_le_val.2 (by simp at hi; simp; omega))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (hM : ∀ i j, valuation k (M i j) ≤ 1) : valuation k M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul, map_prod]; exact Finset.prod_le_one' fun i _ => hM _ _
  · rw [Units.neg_smul, one_smul, Valuation.map_neg, map_prod]; exact Finset.prod_le_one' fun i _ => hM _ _

theorem minor_mul_int {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (X A : Matrix m m k)
    (γ : ValueGroupWithZero k) (hA : ∀ i j, valuation k (A i j) ≤ 1)
    (hX : ∀ f h : ι → m, valuation k (X.submatrix f h).det ≤ γ) (f h : ι → m) :
    valuation k ((X * A).submatrix f h).det ≤ γ := by
  have e : (X * A).submatrix f h = X.submatrix f id * A.submatrix id h := by
    ext a b; simp [Matrix.mul_apply]
  rw [e, det_mul_eq_sum_fun]
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  calc _ ≤ 1 * γ := mul_le_mul' (Finset.prod_le_one' fun i _ => hA _ _)
          (by simpa [Matrix.submatrix_submatrix] using hX f σ)
    _ = γ := one_mul γ

theorem minor_int_mul {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (A X : Matrix m m k)
    (γ : ValueGroupWithZero k) (hA : ∀ i j, valuation k (A i j) ≤ 1)
    (hX : ∀ f h : ι → m, valuation k (X.submatrix f h).det ≤ γ) (f h : ι → m) :
    valuation k ((A * X).submatrix f h).det ≤ γ := by
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_mul]
  exact minor_mul_int Xᵀ Aᵀ γ (fun i j => hA j i)
    (fun f h => by rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact hX h f) h f

theorem det_diag_mul_submatrix {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]
    (d : m → k) (M : Matrix m m k) (f h : ι → m) :
    ((diagonal d * M).submatrix f h).det = (∏ x, d (f x)) * (M.submatrix f h).det := by
  have e : (diagonal d * M).submatrix f h = diagonal (fun x => d (f x)) * M.submatrix f h := by
    ext a b; simp [diagonal_mul]
  rw [e, det_mul, det_diagonal]

theorem det_submatrix_eq_zero {m ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix m m k) (f h : ι → m)
    (hf : ¬ Function.Injective f) : (M.submatrix f h).det = 0 := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, h1, h2⟩ := hf
    exact ⟨a, b, h1, h2⟩
  exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hab])

theorem KO_int {m : Type} [Fintype m] [DecidableEq m] {κ : GL m k} (hκ : κ ∈ KO k m) (i j : m) :
    valuation k (κ.1 i j) ≤ 1 := by
  obtain ⟨κ₀, rfl⟩ := hκ
  exact (κ₀.1 i j).2

theorem KO_det {m : Type} [Fintype m] [DecidableEq m] {κ : GL m k} (hκ : κ ∈ KO k m) :
    valuation k κ.1.det = 1 := by
  have h1 := val_det_le_one _ (KO_int hκ)
  have h2 := val_det_le_one _ (KO_int (inv_mem hκ))
  have h3 : valuation k κ.1.det * valuation k (κ⁻¹).1.det = 1 := by
    rw [← map_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, map_one]
  by_contra hne
  have hlt : valuation k κ.1.det < 1 := lt_of_le_of_ne h1 hne
  have : valuation k κ.1.det * valuation k (κ⁻¹).1.det < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  rw [h3] at this
  exact lt_irrefl _ this

theorem card_filter_lt (N n : ℕ) (hn : n ≤ N) : (Finset.univ.filter fun i : Fin N => (i : ℕ) < n).card = n := by
  first
  | exact @_root_.GlobalTheory.CardValuationLt.card_val_lt
  | exact _root_.GlobalTheory.CardValuationLt.card_val_lt
  | (apply _root_.GlobalTheory.CardValuationLt.card_val_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.CardValuationLt.card_val_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CardValuationLt.card_val_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CardValuationLt.card_val_lt ..)

theorem indic_antitone (N n : ℕ) : Antitone (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) := by
  intro a b hab
  simp only [indic, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (a : ℕ) ≤ b := hab
  split_ifs <;> omega

theorem sum_indic (N n : ℕ) (hn : n ≤ N) :
    ∑ i : Fin N, indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i = n := by
  simp only [indic, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast card_filter_lt N n hn

theorem val_torus_prod (ϖ : kˣ) {ι : Type*} [Fintype ι] (e : ι → ℤ) :
    valuation k (∏ x, (ϖ : k) ^ e x) = valuation k (ϖ : k) ^ ∑ x, e x := by
  rw [map_prod]
  simp_rw [map_zpow₀]
  exact prod_zpow_eq _ ((Valuation.ne_zero_iff _).2 ϖ.ne_zero) e

theorem tail_diag {N : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (j : ℕ) (hj : j < N) (M : Matrix (Fin N) (Fin N) k) (γ : ValueGroupWithZero k)
    (hM : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N, valuation k (M.submatrix f h).det ≤ γ)
    (f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N) :
    valuation k (((diagonal fun i => (ϖ : k) ^ e i) * M).submatrix f h).det ≤
      valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), e i) * γ := by
  rw [det_diag_mul_submatrix]
  by_cases hf : Function.Injective f
  · rw [map_mul, val_torus_prod]
    have hw1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
    have hw0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
    exact mul_le_mul' ((zpow_le_zpow_iff_right_of_lt_one₀ hw0 hw1).2 (sum_tail_le e he j hj f hf)) (hM f h)
  · rw [det_submatrix_eq_zero _ _ _ hf, mul_zero, map_zero]
    exact zero_le'

theorem tail_bound {N : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (μ ν ε : Fin N → ℤ)
    (hμ : Antitone μ) (hε : Antitone ε) (g : GL (Fin N) k)
    (hg : ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ ε * κ')
    (hmain : ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
      torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') (j : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), μ i +
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ε i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ν i := by
  by_cases hj : j < N
  swap
  · have : Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j) = ∅ := by
      ext i; simp; omega
    rw [this]
    simp
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', h1⟩ := hmain
  have hw1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hw0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  have hA : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N,
      valuation k (((torusElt k (Fin N) ϖ ε).1 * κ'.1).submatrix f h).det ≤
        valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ε i) * 1 := by
    intro f h
    rw [val_torusElt]
    exact tail_diag ϖ hϖ ε hε j hj κ'.1 1 (fun f h => val_det_le_one _ (fun a b => KO_int hκ' _ _)) f h
  have hB : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N,
      valuation k ((κ * torusElt k (Fin N) ϖ ε * κ').1.submatrix f h).det ≤
        valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ε i) * 1 := by
    intro f h
    rw [Units.val_mul, Units.val_mul, mul_assoc]
    exact minor_int_mul _ _ _ (KO_int hκ) hA f h
  have hC : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N,
      valuation k ((torusElt k (Fin N) ϖ μ * (κ * torusElt k (Fin N) ϖ ε * κ')).1.submatrix f h).det ≤
        valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), μ i) *
          (valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ε i) * 1) := by
    intro f h
    rw [Units.val_mul (torusElt k (Fin N) ϖ μ), val_torusElt]
    exact tail_diag ϖ hϖ μ hμ j hj _ _ hB f h
  have e : torusElt k (Fin N) ϖ ν =
      κ₁⁻¹ * (torusElt k (Fin N) ϖ μ * (κ * torusElt k (Fin N) ϖ ε * κ')) * κ₁'⁻¹ := by
    rw [h1]; group
  have hD : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N,
      valuation k ((torusElt k (Fin N) ϖ ν).1.submatrix f h).det ≤
        valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), μ i) *
          (valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), ε i) * 1) := by
    intro f h
    rw [e, Units.val_mul, Units.val_mul]
    exact minor_mul_int _ _ _ (KO_int (inv_mem hκ₁')) (minor_int_mul _ _ _ (KO_int (inv_mem hκ₁)) hC) f h
  have hE := hD Subtype.val Subtype.val
  rw [val_torusElt, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal] at hE
  simp only [Function.comp_apply] at hE
  rw [val_torus_prod, mul_one, ← zpow_add₀ hw0.ne'] at hE
  have hle := (zpow_le_zpow_iff_right_of_lt_one₀ hw0 hw1).1 hE
  rwa [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j)) (fun i => by simp) ν] at hle

theorem total_eq {N : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (μ ν ε : Fin N → ℤ) (g : GL (Fin N) k)
    (hg : ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ ε * κ')
    (hmain : ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
      torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') :
    ∑ i, ν i = ∑ i, μ i + ∑ i, ε i := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', h1⟩ := hmain
  have hw1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hw0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  have hd : ∀ e : Fin N → ℤ, valuation k (torusElt k (Fin N) ϖ e).1.det = valuation k (ϖ : k) ^ ∑ i, e i := by
    intro e; rw [val_torusElt, det_diagonal, val_torus_prod]
  have h2 := congrArg (fun x : GL (Fin N) k => valuation k x.1.det) h1
  simp only [Units.val_mul, det_mul, map_mul] at h2
  rw [hd, hd, hd, KO_det hκ, KO_det hκ', KO_det hκ₁, KO_det hκ₁'] at h2
  simp only [mul_one, one_mul] at h2
  rw [← zpow_add₀ hw0.ne'] at h2
  have a := (zpow_le_zpow_iff_right_of_lt_one₀ hw0 hw1).1 h2.le
  have b := (zpow_le_zpow_iff_right_of_lt_one₀ hw0 hw1).1 h2.ge
  omega

theorem cartan_dominance : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k, (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') → (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') → ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i) := by
  intro k _ _ _ _ N ϖ hϖ μ ν hμ hν n hn g hg hmain
  have htot := total_eq ϖ hϖ μ ν _ g hg hmain
  rw [sum_indic N n hn] at htot
  refine ⟨htot, fun j => ?_⟩
  have ht := tail_bound ϖ hϖ μ ν _ hμ (indic_antitone N n) g hg hmain j
  have s1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ν
  have s2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) μ
  have s3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)
    (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n))
  have s4 := sum_indic N n hn
  rw [Finset.sum_add_distrib]
  linarith

end GlobalTheory.CartanDom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongruenceUnipotentMatrixReduction
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.TopCongr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_invariant {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by
  by_cases hx : IntM x
  · have e : g * x = x + (g - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, hp x _ hx (hg.mul_intM hx)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (u.val * x) = 0 := by_contra fun h => hx (by
      have := (mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)
      rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)
    rw [h1, h2]

theorem hat_eq_zero [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem phiTop_eq (z : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) (XIx (Fin κ) t (s + 1) ⊕ Fin 0) k) :
    (S.T t).PhiTop z = (S.P.iter t S.μ S.tame (s + 1)).Phi t (S.μ (s + 1 + 1))
      (z.submatrix (ixSucc _ t (s + 1)) (stdOrd (Fin κ) t (s + 1) 0 rfl)) := by
  have e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (s + 1) 0 rfl)).bas = 1 := by
    change embA _ _ = 1
    rw [Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]
  change S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _
  unfold LatFrame.coords TypeDatum.iterPhi
  rw [e]
  simp [LatFrame.refl, typeFrame]

theorem symmetricChain_psi_base_eq_one_of_maximalIdeal {d : XIx (Fin κ) t (s + 1) → k} (hd : ∀ i, valuation k (d i) < 1) :
    S.ψ (-1 * (d ⬝ᵥ S.y0 t)) = 1 := by
  refine (S.cond 1).2 (by simp) _ ?_
  have h := (S.unif _).1 (hd (Sum.inl (Sum.inr 0)))
  have h0 : (0 : ValueGroupWithZero k) < valuation k (S.ϖ : k) := by
    rw [zero_lt_iff]; simp
  simp only [SymData.y0, dotProduct_single, neg_mul, one_mul, Valuation.map_neg, map_mul, map_one,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ h0).2 h

theorem xiTop_mul_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (g : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) k), (∀ r c, valuation k ((g - 1) r c) < 1) → ∀ x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k, (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (g * x) = (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ g hg x
  refine mul_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

end GlobalTheory.TopCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReindexIff
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}




end Local

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}

end Iter

end GlobalTheory.SymCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalOne

theorem zonalInt_one_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] :
    μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  intro hK γ ψ hψ
  have h1 : ψ 1 = 1 := by
    rw [hψ.2 1 (one_mem _) (fun _ => 1) (fun i => by simp)]
    simp [ord]
  have hκ : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := by
    intro κ hκ
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun GlobalTheory.SplitFlip.isOpen_KO.measurableSet hκ]
  simp [Measure.real, hK]

end GlobalTheory.ZonalOne
end

