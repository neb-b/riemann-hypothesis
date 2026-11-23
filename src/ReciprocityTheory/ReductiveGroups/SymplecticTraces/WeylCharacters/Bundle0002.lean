module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0004
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitA
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def sp_sub (ε : Fin n → Bool) (c : Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ :=
  M.submatrix (blk ε c) (blk ε c)

theorem sp_blk_inj (ε : Fin n → Bool) (c : Bool) : Function.Injective (blk ε c) := by
  intro a b h
  exact ((univ.filter fun i : Fin n => ε i = c).orderEmbOfFin rfl).injective h

theorem sp_blk_surj (ε : Fin n → Bool) (a : Fin n) : ∃ r, blk ε (ε a) r = a := by
  have ha : a ∈ ((univ.filter fun i : Fin n => ε i = ε a : Finset (Fin n)) : Set (Fin n)) := by
    simp
  rw [← Finset.range_orderEmbOfFin (univ.filter fun i : Fin n => ε i = ε a) rfl] at ha
  obtain ⟨r, hr⟩ := ha
  exact ⟨r, hr⟩

private theorem eps_blk (ε : Fin n → Bool) (c : Bool) (r : Fin (cnt ε c)) : ε (blk ε c r) = c := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = c) rfl r
  exact (Finset.mem_filter.mp h).2

private theorem apply_eq_zero_of_commute_Jm_of_eps_ne {ε : Fin n → Bool} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (a b : Fin n) (h : ε a ≠ ε b) : M a b = 0 := by
  have e := congrFun (congrFun hM a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have key : M a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
    rw [mul_sub, e]; ring
  have hne : ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) ≠ 0 := by
    revert h
    cases ha : ε a <;> cases hb : ε b <;> norm_num
  exact (mul_eq_zero.mp key).resolve_right hne

private theorem image_blk_univ_eq_filter_eps (ε : Fin n → Bool) (c : Bool) :
    (univ.image (blk ε c)) = univ.filter fun i : Fin n => ε i = c := by
  ext b
  constructor
  · intro hb
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eps_blk ε c t⟩
  · intro hb
    have hb' : ε b = c := (Finset.mem_filter.mp hb).2
    subst hb'
    obtain ⟨t, ht⟩ := sp_blk_surj ε b
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩

private theorem sp_sub_mul_of_eq_zero_off_eps_blocks {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ a b, ε a ≠ ε b → M a b = 0) (N : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (M * N) = sp_sub ε c M * sp_sub ε c N := by
  ext r s
  simp only [sp_sub, Matrix.submatrix_apply, Matrix.mul_apply]
  have hs := Finset.sum_image (s := (univ : Finset (Fin (cnt ε c)))) (g := blk ε c)
    (f := fun b => M (blk ε c r) b * N b (blk ε c s)) (fun x _ y _ h => sp_blk_inj ε c h)
  rw [image_blk_univ_eq_filter_eps] at hs
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  have hb' : ε b ≠ c := fun e => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩)
  rw [hM _ _ (by rw [eps_blk ε c r]; exact fun e => hb' e.symm), zero_mul]

theorem sp_sub_mul {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (N : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (M * N) = sp_sub ε c M * sp_sub ε c N := by
  exact sp_sub_mul_of_eq_zero_off_eps_blocks c (fun a b h => apply_eq_zero_of_commute_Jm_of_eps_ne hM a b h) N

theorem sp_sub_one (ε : Fin n → Bool) (c : Bool) : sp_sub ε c 1 = 1 := by
  unfold sp_sub
  exact Matrix.submatrix_one _ (sp_blk_inj ε c)

theorem sp_sub_diag (ε : Fin n → Bool) (c : Bool) (t : Fin n → ℂ) :
    sp_sub ε c (diagonal t) = diagonal (t ∘ blk ε c) := by
  unfold sp_sub
  exact Matrix.submatrix_diagonal _ _ (sp_blk_inj ε c)

theorem sp_sub_smul (ε : Fin n → Bool) (c : Bool) (x : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (x • M) = x • sp_sub ε c M := by
  ext i j
  simp [sp_sub]

theorem sp_sub_pow {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (k : ℕ) : sp_sub ε c (M ^ k) = sp_sub ε c M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, sp_sub_one]
  | succ k ih => rw [pow_succ', pow_succ', sp_sub_mul c hM, ih]

theorem sp_Jm_true (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  simp [Jm]

theorem sp_sub_Kset {ε : Fin n → Bool} (c : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    sp_sub ε c g ∈ Kset (fun _ : Fin (cnt ε c) => true) := by
  simp only [Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  have hzs : ∀ a b, ε a ≠ ε b → (star g) a b = 0 := by
    intro a b h
    rw [Matrix.star_apply, apply_eq_zero_of_commute_Jm_of_eps_ne hc b a (Ne.symm h), star_zero]
  refine ⟨?_, by rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hst : star (sp_sub ε c g) = sp_sub ε c (star g) := by
    ext i j
    simp [sp_sub, Matrix.star_apply]
  rw [hst, ← sp_sub_mul_of_eq_zero_off_eps_blocks c hzs, Matrix.mem_unitaryGroup_iff'.mp hu, sp_sub_one]

theorem sp_sub_exp {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) :
    sp_sub ε c (NormedSpace.exp M) = NormedSpace.exp (sp_sub ε c M) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M
  have hs' := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (sp_sub ε c M)
  have hmap : HasSum (fun k => sp_sub ε c (((k.factorial : ℂ)⁻¹) • M ^ k))
      (sp_sub ε c (NormedSpace.exp M)) := by
    refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => ?_
    exact Pi.hasSum.mp (Pi.hasSum.mp hs (blk ε c i)) (blk ε c j)
  simp only [sp_sub_smul, sp_sub_pow c hM] at hmap
  exact hmap.unique hs'

def sp_proj (ε : Fin n → Bool) (c : Bool) : KG ε →* KG (fun _ : Fin (cnt ε c) => true) where
  toFun k := torepK _ (sp_sub_Kset c k.2)
  map_one' := onep_KG_ext (by rw [toMK_torepK]; exact sp_sub_one ε c)
  map_mul' k k' := onep_KG_ext (by
    rw [toMK_torepK]
    exact sp_sub_mul c k.2.2 _)

theorem sp_toMK_proj (ε : Fin n → Bool) (c : Bool) (k : KG ε) :
    toMK (sp_proj ε c k) = sp_sub ε c (toMK k) := by
  exact toMK_torepK _ _

theorem sp_proj_cont (ε : Fin n → Bool) (c : Bool) : Continuous (sp_proj ε c) := by
  have hA : Continuous fun k : KG ε =>
      sp_sub ε c (((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
  show Continuous fun k : KG ε => torepK _ (sp_sub_Kset c k.2)
  unfold torepK
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  rw [Units.continuous_iff]
  exact ⟨hA, hA.matrix_conjTranspose⟩

theorem sp_sub_inK {ε : Fin n → Bool} (c : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    inK (fun _ : Fin (cnt ε c) => true) (sp_sub ε c X) := by
  unfold inK at hX ⊢
  obtain ⟨hG, hc⟩ := hX
  refine ⟨?_, by rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]⟩
  unfold inG at hG ⊢
  rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]
  ext i j
  have e := congrFun (congrFun hG (blk ε c i)) (blk ε c j)
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, eps_blk] at e
  simp only [sp_sub, Matrix.add_apply, Matrix.zero_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
  have hd : (if c = true then (1 : ℂ) else -1) ≠ 0 := by cases c <;> norm_num
  have e2 : (if c = true then (1 : ℂ) else -1) *
      (star (X (blk ε c j) (blk ε c i)) + X (blk ε c i) (blk ε c j)) = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp e2).resolve_left hd

theorem sp_proj_curve {ε : Fin n → Bool} (c : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    {γ : ℝ → KG ε} (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    toMK (sp_proj ε c (γ t)) = NormedSpace.exp ((t : ℂ) • sp_sub ε c X) := by
  rw [sp_toMK_proj, hγ, sp_sub_exp c (by rw [Matrix.smul_mul, hX.2, Matrix.mul_smul]),
    sp_sub_smul]

theorem sp_sub_single_same (ε : Fin n → Bool) (c : Bool) (r s : Fin (cnt ε c)) (x : ℂ) :
    sp_sub ε c (single (blk ε c r) (blk ε c s) x) = single r s x := by
  ext i j
  simp [sp_sub, Matrix.single_apply, (sp_blk_inj ε c).eq_iff]

theorem sp_sub_single_other (ε : Fin n → Bool) {c c' : Bool} (h : c ≠ c') (r s : Fin (cnt ε c)) (x : ℂ) :
    sp_sub ε c' (single (blk ε c r) (blk ε c s) x) = 0 := by
  ext i j
  have hne : blk ε c r ≠ blk ε c' i := fun e => h (by rw [← eps_blk ε c r, e, eps_blk ε c' i])
  simp [sp_sub, Matrix.single_apply, hne]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.UCharOf
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem uChar_of (hS : SqCharStatement) : UCharStatement := by
  intro N Λ _ T k t hk
  obtain ⟨σ, hσk, hU, hK⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.exists_rep T
  obtain ⟨lam, hlam, e, he⟩ :=
    ReciprocityTheory.ChartRestriction.DS.HW.model_equiv N (fun a => (Λ a : ℝ)) T.V σ ⊤ hU hK
  have hw : lam.w = Λ := by
    funext a
    exact_mod_cast (hlam a).symm
  let g : GL (Fin N) ℂ := ReciprocityTheory.ChartRestriction.DS.HW.torepUnit _ k.2
  have hg : (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t := hk
  obtain ⟨f, hf, htr⟩ := hS N lam g t hg
  let e' : T.V ≃ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam := Submodule.topEquiv.symm.trans e
  have hconj : f = e'.conj ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have hz := he g k.2 (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at hz
    rw [hf y, ← hz, ← hσk k]
    rfl
  have hk' : kChar T k = LinearMap.trace ℂ _ f := by
    rw [hconj, LinearMap.trace_conj']
    rfl
  rw [hk', htr, hw]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

