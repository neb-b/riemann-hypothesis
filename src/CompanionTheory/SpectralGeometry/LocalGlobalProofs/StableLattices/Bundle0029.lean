module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeEmb

variable {n m : ℕ}

def er (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) : BranchingSupport.Sub n m :=
  ⟨I.1.erase (I.1.orderEmbOfFin I.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), I.2]; rfl⟩

theorem er_emb (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ⇑((er I j).1.orderEmbOfFin (er I j).2) = fun a => I.1.orderEmbOfFin I.2 (j.succAbove a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    show _ ∈ I.1.erase _
    rw [Finset.mem_erase]
    exact ⟨fun h => Fin.succAbove_ne j a ((I.1.orderEmbOfFin I.2).injective h), Finset.orderEmbOfFin_mem _ _ _⟩
  · exact (I.1.orderEmbOfFin I.2).strictMono.comp (Fin.strictMono_succAbove j)

theorem exists_emb (I : BranchingSupport.Sub n (m + 1)) {t : Fin n} (ht : t ∈ I.1) : ∃ j, I.1.orderEmbOfFin I.2 j = t := by
  have h : t ∈ Set.range (I.1.orderEmbOfFin I.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact ht
  exact h

theorem er_card (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j).card = j := by
  have key : ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j) =
      (Finset.Iio j).map (I.1.orderEmbOfFin I.2).toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ha, hlt⟩
      have ha' : a ∈ I.1 := Finset.mem_of_mem_erase ha
      obtain ⟨i, rfl⟩ := exists_emb I ha'
      exact ⟨i, (I.1.orderEmbOfFin I.2).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hlt := (I.1.orderEmbOfFin I.2).lt_iff_lt.mpr hi
      exact ⟨Finset.mem_erase.mpr ⟨hlt.ne, Finset.orderEmbOfFin_mem _ _ _⟩, hlt⟩
  rw [key, Finset.card_map, Fin.card_Iio]

theorem jW_er (I I' : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    jW n m (er I j, I.1.orderEmbOfFin I.2 j) I' = if I' = I then (-1) ^ (j : ℕ) else 0 := by
  have h1 : I.1.orderEmbOfFin I.2 j ∉ (er I j).1 := by simp [er]
  have h2 : insert (I.1.orderEmbOfFin I.2 j) (er I j).1 = I.1 :=
    Finset.insert_erase (Finset.orderEmbOfFin_mem _ _ _)
  simp only [jW, h1, not_false_eq_true, true_and, h2, er_card]
  by_cases hI : I' = I
  · subst hI
    simp
  · rw [if_neg (fun h => hI (Subtype.ext h)), if_neg hI]

theorem jW_ne (p : BranchingSupport.Sub n m × Fin n) (I : BranchingSupport.Sub n (m + 1)) (h : jW n m p I ≠ 0) :
    ∃ j, (er I j, I.1.orderEmbOfFin I.2 j) = p := by
  obtain ⟨J, t⟩ := p
  simp only [jW] at h
  by_cases hc : t ∉ J.1 ∧ I.1 = insert t J.1
  · have htI : t ∈ I.1 := by
      rw [hc.2]
      exact Finset.mem_insert_self t J.1
    obtain ⟨j, hj⟩ := exists_emb I htI
    refine ⟨j, ?_⟩
    rw [hj]
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    show I.1.erase (I.1.orderEmbOfFin I.2 j) = J.1
    rw [hj, hc.2, Finset.erase_insert hc.1]
  · exact (h (if_neg hc)).elim

theorem sum_jW (F : BranchingSupport.Sub n m × Fin n → ℂ) (I : BranchingSupport.Sub n (m + 1)) :
    ∑ p, F p * jW n m p I = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * F (er I j, I.1.orderEmbOfFin I.2 j) := by
  have hq : Function.Injective (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)) :=
    fun a b hab => (I.1.orderEmbOfFin I.2).injective (congrArg Prod.snd hab)
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)))) ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => hq hab)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [jW_er, if_pos rfl, mul_comm]
  · intro p _ hp
    by_contra hne
    obtain ⟨j, hj⟩ := jW_ne p I (right_ne_zero_of_mul hne)
    exact hp (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem laplace (g : Matrix (Fin n) (Fin n) ℂ) (r : Fin (m + 1) → Fin n) (i : Fin (m + 1))
    (J : BranchingSupport.Sub n m) (hJ : ⇑(J.1.orderEmbOfFin J.2) = fun a => r (i.succAbove a)) (I : BranchingSupport.Sub n (m + 1)) :
    ((cmp m g ⊗ₖ g) * jW n m) (J, r i) I =
      (-1) ^ (i : ℕ) * (g.submatrix r (I.1.orderEmbOfFin I.2)).det := by
  rw [Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply]
  have hs := sum_jW (fun p => cmp m g J p.1 * g (r i) p.2) I
  simp only at hs
  rw [hs, Matrix.det_succ_row _ i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd : cmp m g J (er I j) =
      ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det := by
    unfold BranchingSupport.cmp
    rw [hJ, er_emb]
    rfl
  have h2 : ((-1 : ℂ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hd, Matrix.submatrix_apply, pow_add]
  generalize ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det = d
  generalize g (r i) (I.1.orderEmbOfFin I.2 j) = x
  linear_combination (-(-1 : ℂ) ^ (j : ℕ) * d * x) * h2

theorem first (g : Matrix (Fin n) (Fin n) ℂ) : jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m := by
  ext ⟨J, t⟩ I
  by_cases ht : t ∈ J.1
  · have hL : (jW n m * cmp (m + 1) g) (J, t) I = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro I'' _
      simp only [jW, ht, not_true_eq_false, false_and, if_false, zero_mul]
    have hl := laplace g (Fin.cons t ⇑(J.1.orderEmbOfFin J.2)) 0 J (by
      funext a
      simp only [Fin.succAbove_zero, Fin.cons_succ]) I
    rw [Fin.cons_zero] at hl
    rw [hL, hl]
    have hr : t ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact ht
    obtain ⟨a, ha⟩ := hr
    rw [Matrix.det_zero_of_row_eq (i := (0 : Fin (m + 1))) (j := a.succ) (Fin.succ_ne_zero a).symm ?_, mul_zero]
    funext c
    simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ, ha]
  · let K : BranchingSupport.Sub n (m + 1) := ⟨insert t J.1, by simp [ht, J.2]⟩
    obtain ⟨i, hi⟩ := exists_emb K (Finset.mem_insert_self t J.1)
    have hJK : er K i = J := by
      apply Subtype.ext
      show K.1.erase (K.1.orderEmbOfFin K.2 i) = J.1
      rw [hi]
      exact Finset.erase_insert ht
    have hl := laplace g ⇑(K.1.orderEmbOfFin K.2) i J (by rw [← hJK]; exact er_emb K i) I
    rw [hi] at hl
    rw [hl, Matrix.mul_apply, Finset.sum_eq_single K]
    · have hp : ((J, t) : BranchingSupport.Sub n m × Fin n) = (er K i, K.1.orderEmbOfFin K.2 i) := by
        rw [hJK, hi]
      rw [hp, jW_er, if_pos rfl]
      rfl
    · intro I'' _ hne
      simp only [jW]
      rw [if_neg (fun h => hne (Subtype.ext h.2)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ K) h

theorem cmp_tr (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : BranchingSupport.cmp l gᵀ = (BranchingSupport.cmp l g)ᵀ := by
  ext I J
  simp only [BranchingSupport.cmp, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]

theorem third : (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (BranchingSupport.Sub n (m + 1)) (BranchingSupport.Sub n (m + 1)) ℂ) := by
  have h1 : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  ext I I'
  rw [Matrix.mul_apply]
  show ∑ p, jW n m p I * jW n m p I' = _
  have hs := sum_jW (fun p => jW n m p I') I
  rw [Finset.sum_congr rfl (fun p _ => mul_comm (jW n m p I) (jW n m p I')), hs]
  simp only [jW_er]
  by_cases h : I' = I
  · subst h
    have hc : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (if I' = I' then (-1) ^ (j : ℕ) else 0) = 1 :=
      fun j => by rw [if_pos rfl, h1]
    rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero, Matrix.smul_apply,
      Matrix.one_apply_ne (Ne.symm h), smul_zero]

theorem wedgeInt : WedgeInt := by
  intro n m
  refine ⟨fun g => ⟨first g, ?_⟩, third⟩
  have h := congrArg Matrix.transpose (first (n := n) (m := m) gᵀ)
  simp only [Matrix.transpose_mul, cmp_tr, Matrix.transpose_transpose,
    Matrix.kroneckerMap_transpose] at h
  exact h.symm

end GlobalTheory.CompanionTheory.WedgeEmb
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckHomCat

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm

variable {k r : ℕ}

theorem sn_nonneg (X : Obj k r) (W : List (Mx k r)) (x : M X) : 0 ≤ sn X W x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sn_add_le (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (x y : M X) :
    sn X W (x + y) ≤ sn X W x + sn X W y := by
  unfold sn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [dsigW_eq', Pi.add_apply, Submodule.coe_add]
  rw [dsW_add X.2.repOn (x c).2 (y c).2 (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_add_le _ _

theorem sn_smul (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (a : ℂ) (x : M X) :
    sn X W (a • x) = ‖a‖ * sn X W x := by
  unfold sn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [dsigW_eq', Pi.smul_apply, Submodule.coe_smul]
  rw [dsW_smul X.2.repOn (x c).2 a (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_smul _ _

theorem sum_nonneg' (X : Obj k r) (Ws : List (List (Mx k r))) (x : M X) :
    0 ≤ (Ws.map fun W' => sn X W' x).sum :=
  List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
    exact sn_nonneg X W x

def Dom (X : Obj k r) (φ : M X → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W' ∈ Ws, LieWd k r W') ∧
    ∀ x, φ x ≤ C * (Ws.map fun W' => sn X W' x).sum

theorem Dom.mono {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X ψ) (hle : ∀ x, φ x ≤ ψ x) : Dom X φ := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  exact ⟨C, Ws, hW, fun x => (hle x).trans (hb x)⟩

theorem Dom.zero (X : Obj k r) : Dom X fun _ => 0 :=
  ⟨0, [], by simp, fun _ => by simp⟩

theorem Dom.add {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X φ) (h' : Dom X ψ) :
    Dom X fun x => φ x + ψ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hm => (List.mem_append.1 hm).elim (hW W) (hW' W), fun x => ?_⟩
  rw [List.map_append, List.sum_append]
  have h1 := sum_nonneg' X Ws x
  have h2 := sum_nonneg' X Ws' x
  have h3 := hb x
  have h4 := hb' x
  have h5 := mul_le_mul_of_nonneg_right (le_abs_self C) h1
  have h6 := mul_le_mul_of_nonneg_right (le_abs_self C') h2
  have h7 := mul_nonneg (abs_nonneg C) h2
  have h8 := mul_nonneg (abs_nonneg C') h1
  nlinarith

theorem Dom.mul {X : Obj k r} {φ : M X → ℝ} (h : Dom X φ) {a : ℝ} (ha : 0 ≤ a) :
    Dom X fun x => a * φ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨a * C, Ws, hW, fun x => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) ha

theorem Dom.listSum {X : Obj k r} {ι : Type} (φ : ι → M X → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, Dom X (φ i)) → Dom X fun x => (l.map fun i => φ i x).sum
  | [], _ => by simpa using Dom.zero X
  | i :: l, h => by
    simpa using (h i List.mem_cons_self).add
      (Dom.listSum φ l fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem homCat : HomCat := by
  intro k r
  refine ⟨fun X Y => ⟨fun W hW => ?_, fun g _ => ?_⟩, fun X Y f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩,
    fun X Y c f hf => ⟨fun W hW => ?_, fun g hg => ?_⟩, fun X => ⟨fun W hW => ?_, fun g _ => ?_⟩,
    fun X Y Z f f' hf hf' => ⟨fun W hW => ?_, fun g hg => ?_⟩⟩
  · refine (Dom.zero X).mono fun x => ?_
    have := sn_smul Y hW 0 0
    rw [zero_smul, norm_zero, zero_mul] at this
    exact this.le
  · rw [LinearMap.zero_comp, LinearMap.comp_zero]
  · exact (Dom.add (hf.cont W hW) (hf'.cont W hW)).mono fun x => sn_add_le Y hW _ _
  · rw [LinearMap.add_comp, LinearMap.comp_add, hf.equiv g hg, hf'.equiv g hg]
  · exact (Dom.mul (hf.cont W hW) (norm_nonneg c)).mono fun x => (sn_smul Y hW _ _).le
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf.equiv g hg]
  · exact ⟨1, [W], by simpa using hW, fun x => by simp⟩
  · rw [LinearMap.id_comp, LinearMap.comp_id]
  · obtain ⟨C, Ws, hWs, hb⟩ := hf'.cont W hW
    refine ((Dom.listSum (X := X) (fun W' x => sn Y W' (f x)) Ws
      fun W' h' => hf.cont W' (hWs W' h')).mul (abs_nonneg C)).mono fun x => ?_
    exact (hb (f x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sum_nonneg' Y Ws _))
  · rw [LinearMap.comp_assoc, hf.equiv g hg, ← LinearMap.comp_assoc, hf'.equiv g hg, LinearMap.comp_assoc]

end GlobalTheory.CompanionTheory.ZuckHomCat

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
section
noncomputable section

namespace GlobalTheory.CompanionTheory.BmuIwa

open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

theorem adapted_dec_one {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem conj_mem {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hAH : Aᴴ = A)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A)ᴴ * A * (A * gᴴ * A) = A := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
  calc A * (g * A) * A * (A * gᴴ * A) = A * (g * (A * A) * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hA, Matrix.mul_one, CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hg, hA, Matrix.one_mul]

theorem conj_mul {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by
  calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hA]

theorem adapted_dec_left {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by
  have hA := h.mul_self
  have hAH := h.herm
  obtain ⟨k, B, hk, hkA, hBA, hg, hB⟩ := adapted_dec_one h _ (conj_mem hA hAH hx)
  set A := dp p 0 c
  have hBl := conj_mul hA hBA
  have hk' : k * kᴴ = 1 := mul_eq_one_comm.1 hk
  refine ⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA
  · let _ : Invertible B := invertibleOfLeftInverse B _ hBl
    rw [← inv_eq_left_inv hBl]
    exact blockTriangular_inv_of_blockTriangular hB
  · rw [conjTranspose_conjTranspose]; exact hk'
  · have h1 : k * B * x = 1 := by rw [← hg]; exact conj_mul hA hx
    calc x = (A * Bᴴ * A * B) * x := by rw [hBl, Matrix.one_mul]
      _ = A * Bᴴ * A * ((kᴴ * k) * B * x) := by rw [hk, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = A * Bᴴ * A * kᴴ * (k * B * x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

def pq (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := if outer k r i then i.rev else i

def bq (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ := if outer k r i then 2 * (i.val : ℤ) - (2 * r + k) else 0

theorem pq_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (pq k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]; omega
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem bq_eq (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    bq k r i = if i.val ≤ r ∨ r + k ≤ i.val then 2 * (i.val : ℤ) - (2 * r + k) else 0 := by
  unfold bq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem adapted_pq (k r : ℕ) : Adapted (pq k r) (bq k r) (fun _ => 1) := by
  constructor
  · intro i
    apply Fin.ext
    have := i.2
    rw [pq_val, pq_val]
    split_ifs <;> omega
  · intro i j hij
    have h : i.val ≤ j.val := hij
    rw [bq_eq, bq_eq]
    split_ifs <;> omega
  · intro i
    have := i.2
    rw [bq_eq, bq_eq, pq_val]
    split_ifs <;> omega
  · intro i hi
    apply Fin.ext
    have := i.2
    rw [bq_eq] at hi
    rw [pq_val]
    split_ifs at hi ⊢ <;> omega
  · intro i j hi hij
    apply Fin.ext
    rw [bq_eq] at hi
    rw [bq_eq, bq_eq] at hij
    split_ifs at hi hij <;> omega
  · intro i
    simp
  · intro i
    simp
  · intros
    rfl
  · intros
    rfl

theorem Hq_eq_dp (k r : ℕ) : Hq k r = dp (pq k r) 0 (fun _ => 1) := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Hq, dp, Matrix.of_apply, Pi.zero_apply, ite_self, zero_add, Fin.ext_iff, pq_val]
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
    exact if_congr (by omega) rfl rfl
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]
    exact if_congr eq_comm rfl rfl

theorem iwaQ : IwaQ := by
  intro k r _ x hx
  have hx' : xᴴ * Hq k r * x = Hq k r := hx
  rw [Hq_eq_dp] at hx'
  obtain ⟨s, κ, hs, hκ, h1, h2, h3⟩ := adapted_dec_left (adapted_pq k r) x hx'
  rw [← Hq_eq_dp] at hs hκ
  exact ⟨s, hs, κ, hκ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.BmuIwa
end
end

