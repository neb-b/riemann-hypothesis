module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ}

def ldTop (j : Fin s) : {a : Fin s // (a : ℕ) < j + 1} := ⟨j, Nat.lt_succ_self _⟩

@[simp] theorem ldTop_val (j : Fin s) : (ldTop j).1 = j := rfl

theorem eq_ldTop_iff {j : Fin s} (a : {a : Fin s // (a : ℕ) < j + 1}) : a = ldTop j ↔ a.1 = j :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

theorem sum_eq_sum_lt_of_zero (m : ℕ) (f : Fin s → ℂ) (hf : ∀ l : Fin s, ¬ (l : ℕ) < m → f l = 0) :
    ∑ l, f l = ∑ b : {a : Fin s // (a : ℕ) < m}, f b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < m) f]
  have : ∑ b : {a : Fin s // ¬ (a : ℕ) < m}, f b = 0 := Finset.sum_eq_zero (fun b _ => hf b b.2)
  rw [this, add_zero]

theorem prod_lt_eq (m : ℕ) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < m}, f a = ∏ a : Fin s, if (a : ℕ) < m then f a else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) f).symm

theorem prod_lt_succ (j : Fin s) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < j + 1}, f a = (∏ a : {a : Fin s // (a : ℕ) < j}, f a) * f j := by
  have hj : f j = ∏ a : Fin s, if a = j then f a else 1 := by simp
  rw [prod_lt_eq, prod_lt_eq, hj, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h1 : (a : ℕ) < j
  · have h2 : a ≠ j := fun h => by subst h; omega
    simp [h1, h2, show (a : ℕ) < j + 1 by omega]
  · by_cases h3 : a = j
    · subst h3; simp
    · have : ¬ (a : ℕ) < j + 1 := fun h => h3 (Fin.ext (by omega))
      simp [h1, h3, this]

theorem submatrix_mul_conjTranspose_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ρ : κ → Fin s) (m : ℕ) :
    (M * gᴴ).submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) =
      M.submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) *
        gᴴ.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [Matrix.conjTranspose_apply, hg c.1 l (by have := c.2; rw [Fin.lt_iff_val_lt_val]; omega), star_zero, mul_zero]

theorem submatrix_mul_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ν : κ → Fin s) (m : ℕ) :
    (g * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν =
      g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [hg a.1 l (by have := a.2; rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem det_submatrix_lt (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val).det =
      ∏ a : {a : Fin s // (a : ℕ) < m}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · rfl
  · intro a b h
    exact hg a.1 b.1 h

theorem leadMinor_conj_lower (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    leadMinor (g * G * gᴴ) m =
      (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) * leadMinor G m * star (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) := by
  unfold leadMinor
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, submatrix_mul_lt g G hg]
  erw [Matrix.det_mul]
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, det_submatrix_lt g hg]

theorem det_updateRow_finset_sum {ι κ : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (r : ι)
    (t : Finset κ) (c : κ → ℂ) (v : κ → ι → ℂ) :
    (A.updateRow r (∑ l ∈ t, c l • v l)).det = ∑ l ∈ t, c l * (A.updateRow r (v l)).det := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r (fun c => by simp)
  · intro a t ha ih
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih, Finset.sum_insert ha]

theorem submatrix_ld_eq_updateRow (X : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    X.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val =
      (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j)
        (fun c : {a : Fin s // (a : ℕ) < j + 1} => X i c) := by
  ext a c
  rw [Matrix.updateRow_apply]
  by_cases h : a.1 = j
  · simp [h, (eq_ldTop_iff a).2 h]
  · have : a ≠ ldTop j := fun e => h ((eq_ldTop_iff a).1 e)
    simp [h, this]

theorem updateRow_mul_lower (g X : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s)
    (v : {a : Fin s // (a : ℕ) < j + 1} → ℂ) :
    ((g * X).submatrix Subtype.val Subtype.val).updateRow (ldTop j) v =
      (g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1) *
        (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j) v := by
  ext a c
  by_cases h : a = ldTop j
  · subst h
    simp [Matrix.mul_apply, Pi.single_apply]
  · have ha : (a.1 : ℕ) < j := by
      have := a.2
      have : (a.1 : ℕ) ≠ j := fun e => h ((eq_ldTop_iff a).2 (Fin.ext e))
      omega
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_eq_sum_lt_of_zero ((j : ℕ) + 1) _ fun l hl => by
      rw [hg a.1 l (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.updateRow_apply]
    by_cases hb : b = ldTop j
    · subst hb
      rw [ldTop_val, hg a.1 j (by rw [Fin.lt_iff_val_lt_val]; exact ha)]
      simp
    · simp [hb]

theorem det_frameRow (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s) :
    ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j + 1} → Fin s) Subtype.val).updateRow
      (ldTop j) (Pi.single (ldTop j) 1)).det =
      ∏ a : {a : Fin s // (a : ℕ) < j}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · have e : ∀ a : {a : Fin s // (a : ℕ) < j + 1},
        ((g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1)) a a =
          (fun b : Fin s => if b = j then 1 else g b b) a := by
      intro a
      by_cases h : a = ldTop j
      · subst h; simp
      · have : a.1 ≠ j := fun e => h ((eq_ldTop_iff a).2 e)
        simp [Matrix.updateRow_ne h, this]
    rw [Fintype.prod_congr _ _ e, prod_lt_succ j (fun b : Fin s => if b = j then 1 else g b b)]
    simp only [if_true, mul_one]
    refine Fintype.prod_congr (fun a : {a : Fin s // (a : ℕ) < j} => if (a : Fin s) = j then (1 : ℂ) else g a a)
      (fun a => g a a) fun a => ?_
    have : a.1 ≠ j := fun e => by have := a.2; rw [e] at this; omega
    simp [this]
  · intro a b hab
    have hab' : (a.1 : ℕ) < b.1 := hab
    by_cases h : a = ldTop j
    · subst h
      have := b.2
      simp at hab'
      omega
    · rw [Matrix.updateRow_ne h, Matrix.submatrix_apply]
      exact hg a.1 b.1 (Fin.lt_iff_val_lt_val.mpr hab')

end GlobalTheory.ChernCalc

namespace GlobalTheory.ChernCalc

theorem ldNum_conj_lower {s : ℕ} (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (i j : Fin s) :
    ((g * G * gᴴ).submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det =
      (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) *
        (∑ l, g i l * (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then l else a.1)
          Subtype.val).det) * star (∏ a : {a : Fin s // (a : ℕ) < j + 1}, g a a) := by
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    det_submatrix_lt g hg, submatrix_ld_eq_updateRow, updateRow_mul_lower g G hg]
  erw [Matrix.det_mul]
  rw [det_frameRow g hg]
  have hrow : (fun c : {a : Fin s // (a : ℕ) < j + 1} => (g * G) i c) =
      ∑ l, g i l • (fun c : {a : Fin s // (a : ℕ) < j + 1} => G l c) := by
    funext c; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow, det_updateRow_finset_sum]
  simp only [submatrix_ld_eq_updateRow]

theorem ldPart_conj_lower : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) →
    IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧
      ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  intro s G g hG hg hdet
  have hgd : g.det = ∏ a, g a a := Matrix.det_of_lowerTriangular g (fun a b h => hg a b h)
  have hdiag : ∀ a, g a a ≠ 0 := by
    intro a
    have h := hdet.ne_zero
    rw [hgd] at h
    exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ _)
  have hP : ∀ m : ℕ, (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) ≠ 0 :=
    fun m => Finset.prod_ne_zero_iff.mpr fun a _ => hdiag a
  have hlm : ∀ m : ℕ, leadMinor G m ≠ 0 := fun m => by
    unfold leadMinor
    exact ((hG.submatrix Subtype.val_injective).det_pos).ne'
  have hsq : ∀ z w : ℂ, (z * w * star z).re = ‖z‖ ^ 2 * w.re := by
    intro z w
    rw [mul_comm z w, mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.re_mul_ofReal]
    ring
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    simp only [ldPart, Matrix.of_apply]
    rw [ldNum_conj_lower g G hg, leadMinor_conj_lower g G hg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.mul_apply, prod_lt_succ j (fun b => g b b)]
    simp only [Matrix.of_apply, ← mul_div_assoc, Pi.star_apply]
    rw [← Finset.sum_div, star_mul]
    have h1 := hP (j : ℕ)
    have h2 := hlm (j : ℕ)
    have h3 : star (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) ≠ 0 := star_ne_zero.mpr h1
    field_simp
  · unfold grD
    rw [leadMinor_conj_lower g G hg, leadMinor_conj_lower g G hg, hsq, hsq, prod_lt_succ i (fun b => g b b),
      norm_mul, mul_pow]
    have hn : ‖∏ a : {a : Fin s // (a : ℕ) < i}, g a a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hP _))
    rw [mul_assoc, mul_div_mul_left _ _ hn, mul_div_assoc]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjection
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GrpDescent

section Pt
variable {S X : Scheme.{0}} (G' : Over S) (f : X ⟶ S)

def ptOf {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) : T ⟶ (Over.pullback f).obj G' :=
  Over.homMk (pullback.lift a T.hom ha) (pullback.lift_snd _ _ _)

theorem ptOf_fst {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f a ha).left ≫ pullback.fst G'.hom f = a := pullback.lift_fst _ _ _

theorem ptOf_mul [GrpObj G'] {T : Over X} (w : T.left ⟶ (G' ⊗ G').left) (hw : w ≫ (G' ⊗ G').hom = T.hom ≫ f)
    (h₁ : (w ≫ (fst G' G').left) ≫ G'.hom = T.hom ≫ f) (h₂ : (w ≫ (snd G' G').left) ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f _ h₁ * ptOf G' f _ h₂).left ≫ pullback.fst G'.hom f = w ≫ μ[G'].left := by
  let U : Over.mk (T.hom ≫ f) ⟶ G' ⊗ G' := Over.homMk w hw
  have e := (isGrpPullback_pullback G' f).2 T (ptOf G' f _ h₁) (ptOf G' f _ h₂) (U ≫ fst G' G') (U ≫ snd G' G')
    (ptOf_fst G' f _ h₁).symm (ptOf_fst G' f _ h₂).symm
  rw [← e, ← MonObj.comp_mul, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rfl

end Pt

theorem mul_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  intro R _ _ _ _ S π hprop hsurj hint G' _ G β hsm hβ φ hφ hdat
  haveI := hsm
  haveI : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have hflat : Flat (G ⊗ G).hom := inferInstance
  let Z' : Over (Sp R) := Over.mk ((G' ⊗ G').hom ≫ π)
  let u : Z' ⟶ G := Over.homMk ((fst G' G').left ≫ β) (by
    show ((fst G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let v : Z' ⟶ G := Over.homMk ((snd G' G').left ≫ β) (by
    show ((snd G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let p : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift u v).left
  have hp1 : p ≫ (fst G G).left = (fst G' G').left ≫ β := by
    show (lift u v ≫ fst G G).left = _
    rw [lift_fst]; rfl
  have hp2 : p ≫ (snd G G).left = (snd G' G').left ≫ β := by
    show (lift u v ≫ snd G G).left = _
    rw [lift_snd]; rfl
  have hA : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have htop : IsPullback p (snd G' G').left (snd G G).left β := by
    refine IsPullback.of_right (h₁₂ := (fst G G).left) (h₂₂ := G.hom) ?_ hp2 hB
    rw [hp1, hβ.w]
    exact hA.paste_horiz hβ
  have hpb : IsPullback p (G' ⊗ G').hom (G ⊗ G).hom π := by
    have h := htop.paste_vert hβ
    rwa [Over.w (snd G' G'), Over.w (snd G G)] at h

  have hepi : ∀ {W : Scheme.{0}} (a b : (G ⊗ G).left ⟶ W), p ≫ a = p ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.MorDescent.descend R S _ _ W π _ p _ hprop hsurj hint hflat hpb (p ≫ a)
      (by rw [← Category.assoc, pullback.condition, Category.assoc])
    exact (hc a rfl).trans (hc b hab.symm).symm

  have heq : pullback.fst p p ≫ μ[G'].left ≫ β = pullback.snd p p ≫ μ[G'].left ≫ β := by
    set f₁ := pullback.fst p p
    set f₂ := pullback.snd p p
    have hf : f₁ ≫ p = f₂ ≫ p := pullback.condition
    have hs : (f₁ ≫ (G' ⊗ G').hom) ≫ π = (f₂ ≫ (G' ⊗ G').hom) ≫ π := by
      rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, hf, Category.assoc]
    let σ := pullback.lift _ _ hs
    let T₀ : Over (pullback π π) := Over.mk σ
    have hw₁ : f₁ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.fst π π := (pullback.lift_fst _ _ hs).symm
    have hw₂ : f₂ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.snd π π := (pullback.lift_snd _ _ hs).symm

    have htr : ∀ (a₁ a₂ : T₀.left ⟶ G'.left) (h₁ : a₁ ≫ G'.hom = T₀.hom ≫ pullback.fst π π)
        (h₂ : a₂ ≫ G'.hom = T₀.hom ≫ pullback.snd π π), a₁ ≫ β = a₂ ≫ β →
        ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom = ptOf G' (pullback.snd π π) a₂ h₂ := by
      intro a₁ a₂ h₁ h₂ hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply hβ.hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, ← hdat, ← Category.assoc, ptOf_fst, ptOf_fst, hb]
        · rw [Category.assoc, pullback.condition, ptOf_fst, h₂, ← Category.assoc]
          exact congrArg (· ≫ pullback.snd π π) (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom))
      · exact (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom)).trans (Over.w (ptOf G' (pullback.snd π π) a₂ h₂)).symm
    have hb₁ : (f₁ ≫ (fst G' G').left) ≫ β = (f₂ ≫ (fst G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp1, ← Category.assoc, hf, Category.assoc]
    have hb₂ : (f₁ ≫ (snd G' G').left) ≫ β = (f₂ ≫ (snd G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp2, ← Category.assoc, hf, Category.assoc]
    have k₁ : (f₁ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have k₂ : (f₁ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have l₁ : (f₂ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have l₂ : (f₂ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have e₁ := ptOf_mul G' (pullback.fst π π) (T := T₀) f₁ hw₁ k₁ k₂
    have e₂ := ptOf_mul G' (pullback.snd π π) (T := T₀) f₂ hw₂ l₁ l₂
    have hAB : (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ * ptOf G' (pullback.fst π π) (T := T₀) _ k₂) ≫ φ.hom =
        ptOf G' (pullback.snd π π) (T := T₀) _ l₁ * ptOf G' (pullback.snd π π) (T := T₀) _ l₂ := by
      refine ((IsMonHom.monoidHom φ.hom T₀).map_mul _ _).trans ?_
      show (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ ≫ φ.hom) * (ptOf G' (pullback.fst π π) (T := T₀) _ k₂ ≫ φ.hom) = _
      rw [htr _ _ k₁ l₁ hb₁, htr _ _ k₂ l₂ hb₂]
    rw [← Category.assoc f₁, ← e₁, ← Category.assoc f₂, ← e₂, ← hAB, Over.comp_left]
    simp only [Category.assoc]
    rw [hdat]
  obtain ⟨h₀, hh₀, -⟩ := _root_.GlobalTheory.MorDescent.descend R S _ _ _ π _ p _ hprop hsurj hint hflat hpb (μ[G'].left ≫ β) heq
  have hover : h₀ ≫ G.hom = (G ⊗ G).hom := by
    apply hepi
    rw [← Category.assoc, hh₀, Category.assoc, hβ.w, ← Category.assoc, Over.w μ[G'], hpb.w]
  refine ⟨Over.homMk h₀ hover, fun T x y x₀ y₀ hx hy => ?_⟩
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ p := by
    apply hB.hom_ext
    · rw [Category.assoc, hp1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, hx]
    · rw [Category.assoc, hp2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hy]
  rw [Over.comp_left, hl]
  change ((lift x y).left ≫ p) ≫ h₀ = _
  rw [Category.assoc, hh₀, Hom.mul_def, Over.comp_left, Category.assoc]

end GlobalTheory.GrpDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)}


variable (I) in
def hRed (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left :=
  pullback.lift (thick R I e ≫ h.left) (𝟙 _) (by
    rw [Category.assoc, Over.w h, Category.id_comp]
    exact Category.comp_id _)

theorem hRed_fst (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left :=
  pullback.lift_fst _ _ _

variable {D : DegData R I} {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

def TRel (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)))
    (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1))) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (R ⧸ I ^ (e + 1))) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (JG : (Z ⟶ G.left) → U.LG.L.ι), Good D.toPre.P.L z J → Good U.LG.L z JG →
    val t (r ≫ thick R I e) z J *
        wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) *
        val f (r ≫ thick R I e) z JG =
      val (L := D.toPre.P.L) D.toPre.rig (r ≫ thick R I e) z J

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTQuotRigid

theorem objMap_comp_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem eq_one_of_fixes_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
      (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
      IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  intro p _ D R _ b N h M hN hNp hM X s s₁ u lev hlev ρ hρ k _ _ y a hya
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨-, -, m, hm⟩ := hρ a
  obtain ⟨o, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N X (Sp k) s y u
  obtain ⟨c, hc⟩ := objMap_comp_φ n m
  have key : ∀ (f : Sp k ⟶ X), f = y → ∀ mm : ObjMap o u f, mm.φ = n.φ := by
    intro f hf mm
    subst hf
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ mm n
  have hφ : n.φ ≫ m.φ = n.φ := by rw [← hc]; exact key _ hya c

  have hx : ∀ x, y ≫ (sympTwist a lev x).left = y ≫ (lev x).left := by
    intro x
    have ht : (y ≫ (sympTwist a lev x).left) ≫ u.A.hom = 𝟙 (Sp k) ≫ y := by
      rw [Category.assoc, Over.w]
      rfl
    have hσ := n.cart.1.lift_fst (y ≫ (sympTwist a lev x).left) (𝟙 _) ht
    have e1 : (y ≫ (sympTwist a lev x).left) ≫ m.φ = y ≫ (lev x).left := by
      rw [Category.assoc, hm x, ← Category.assoc, hya]
    rw [← e1, ← hσ, Category.assoc, hφ]

  let β : cycAway M →+* k := (Spec.preimage (y ≫ s₁)).hom
  have hβ : y ≫ s₁ = spMap β := by
    change y ≫ s₁ = Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ s₁)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hpow : β (zetaAway M) ^ M = 1 := by rw [← map_pow, zetaAway_pow_self hM.ne', map_one]
  let z : kˣ := Units.ofPowEqOne _ M hpow hM.ne'
  have hcl := (hlev.2.2 k y β z hβ rfl).1
  have hunit : ∀ x, (toUnit (Over.mk y) ≫ lev x).left = y ≫ (lev x).left := by
    intro x
    rw [Over.comp_left]
    congr 1
  have hfix : ∀ x, (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x) =
      reduceMod M x := by
    intro x
    set c := liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))
    have hsame : toUnit (Over.mk y) ≫ lev c = toUnit (Over.mk y) ≫ lev x := by
      ext1
      rw [hunit, hunit]
      exact hx x
    have hsplit : lev c = lev (c - x) * lev x := by rw [← hlev.1, sub_add_cancel]
    have h1 : toUnit (Over.mk y) ≫ lev (c - x) = 1 := by
      rw [hsplit, comp_mul] at hsame
      exact mul_eq_right.1 hsame
    obtain ⟨d, hd⟩ := (hcl (c - x)).1 h1
    have hr : reduceMod M c = reduceMod M x := by
      have : c = x + M • d := by rw [← hd]; abel
      rw [this]
      funext i
      simp [reduceMod]
    exact (reduceMod_liftMod _).symm.trans hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := hfix (liftMod v)
  rw [reduceMod_liftMod] at this
  exact this

end GlobalTheory.HTQuotRigid
end
end

