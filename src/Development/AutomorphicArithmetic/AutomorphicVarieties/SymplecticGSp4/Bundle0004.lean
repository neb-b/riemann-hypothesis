module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdLocal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open Polynomial

variable {B : Type} [CommRing B]

private theorem aeval_conj (u : (M4 B)ˣ) (X : M4 B) (p : B[X]) :
    aeval ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) p = (u : M4 B) * aeval X p * (u⁻¹ : (M4 B)ˣ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc]

private theorem prj_conj (c : Fin 4 → B) (u : (M4 B)ˣ) (X : M4 B) (i : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * prj c X i * (u⁻¹ : (M4 B)ˣ) :=
  aeval_conj u X _

private theorem eig_left (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)) * prj c X i = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem eig_right (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    prj c X i * (X - c i • (1 : M4 B)) = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem aeval_sub (X : M4 B) (a : B) (p : B[X]) :
    ∃ Y : M4 B, aeval X p - p.eval a • (1 : M4 B) = Y * (X - a • (1 : M4 B)) := by
  obtain ⟨s, hs⟩ : Polynomial.X - C a ∣ p - C (p.eval a) := X_sub_C_dvd_sub_C_eval
  refine ⟨aeval X s, ?_⟩
  have h := congrArg (aeval X) hs
  rw [mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one] at h
  exact h

private theorem prj_sub (c : Fin 4 → B) (X : M4 B) (i j : Fin 4) :
    ∃ Y : M4 B, prj c X i - (∏ a ∈ Finset.univ.erase i, (c j - c a)) • (1 : M4 B) = Y * (X - c j • (1 : M4 B)) := by
  obtain ⟨Y, hY⟩ := aeval_sub X (c j) (∏ a ∈ Finset.univ.erase i, (Polynomial.X - C (c a)))
  refine ⟨Y, ?_⟩
  rw [← hY, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rfl

private theorem prj_mul (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i j : Fin 4) :
    prj c X i * prj c X j = (∏ a ∈ Finset.univ.erase i, (c j - c a)) • prj c X j := by
  obtain ⟨Y, hY⟩ := prj_sub c X i j
  have h1 := congrArg (· * prj c X j) hY
  simp only [mul_assoc, eig_left c X h j, mul_zero, sub_mul, smul_mul_assoc, one_mul] at h1
  exact sub_eq_zero.mp h1

private theorem unit_d (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (i : Fin 4) :
    IsUnit (∏ a ∈ Finset.univ.erase i, (c i - c a)) :=
  IsUnit.prod_iff.mpr fun a ha => hc i a (Finset.ne_of_mem_erase ha).symm

private theorem zero_d (c : Fin 4 → B) {i j : Fin 4} (hij : j ≠ i) :
    (∏ a ∈ Finset.univ.erase i, (c j - c a)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self _)

private theorem det_eig (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)).det = 0 := by
  have h1 := Matrix.eval_charpoly X (c i)
  rw [h, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h1
  have h2 : X - c i • (1 : M4 B) = -(Matrix.scalar (Fin 4) (c i) - X) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h2, Matrix.det_neg, ← h1, mul_zero]

private theorem exists_unit [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) : ∃ ab : Fin 4 × Fin 4, IsUnit (prj c X i ab.1 ab.2) := by
  by_contra hn
  push Not at hn
  obtain ⟨Y, hY⟩ := prj_sub c X i i
  have h1 := congrArg Matrix.det hY
  rw [Matrix.det_mul, det_eig c X h i, mul_zero] at h1
  have h2 := congrArg (residue B) h1
  set d := ∏ a ∈ Finset.univ.erase i, (c i - c a) with hd
  have h3 : (residue B).mapMatrix (prj c X i - d • (1 : M4 B)) = Matrix.diagonal fun _ => -residue B d := by
    ext a b
    have h0 : residue B (prj c X i a b) = 0 := (residue_eq_zero_iff _).mpr (hn (a, b))
    by_cases hab : a = b
    · subst hab; simp [h0]
    · simp [h0, hab]
  rw [RingHom.map_det, h3, Matrix.det_diagonal, map_zero, Finset.prod_eq_zero_iff] at h2
  obtain ⟨_, -, h4⟩ := h2
  exact ((unit_d c hc i).map (residue B)).ne_zero (neg_eq_zero.mp h4)

private theorem diagonalize [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) :
    ∃ u : (M4 B)ˣ, (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c := by
  choose ab hab using exists_unit c hc X h
  let P : M4 B := Matrix.of fun x j => prj c X j x (ab j).2
  let Q : M4 B := Matrix.of fun i x => prj c X i (ab i).1 x
  have hQP : Q * P = Matrix.diagonal fun i => (∏ a ∈ Finset.univ.erase i, (c i - c a)) * prj c X i (ab i).1 (ab i).2 := by
    ext i j
    have h1 : (Q * P) i j = (prj c X i * prj c X j) (ab i).1 (ab j).2 := rfl
    rw [h1, prj_mul c X h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [zero_d c (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]; simp
  have hdet : IsUnit (Q * P).det := by
    rw [hQP, Matrix.det_diagonal]
    exact IsUnit.prod_iff.mpr fun a _ => (unit_d c hc a).mul (hab a)
  rw [Matrix.det_mul] at hdet
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_of_mul_isUnit_right hdet)
  have hXP : X * P = P * Matrix.diagonal c := by
    ext x j
    have h1 : (X * P) x j = (X * prj c X j) x (ab j).2 := rfl
    have h2 := eig_left c X h j
    rw [sub_mul, sub_eq_zero, smul_mul_assoc, one_mul] at h2
    rw [h1, h2, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    rfl
  refine ⟨v⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hv, hXP, ← hv, Units.inv_mul_cancel_left]

private theorem prj_diag (c : Fin 4 → B) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun x => ∏ a ∈ Finset.univ.erase i, (c x - c a) := by
  have h1 : Matrix.diagonal c = Matrix.diagonalAlgHom B c := rfl
  unfold prj
  rw [h1, aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext x
  rw [map_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp

private theorem sandwich (c : Fin 4 → B) (u : (M4 B)ˣ) (X Y : M4 B) (i j : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) j * ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) *
      prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * (prj c X j * Y * prj c X i) * (u⁻¹ : (M4 B)ˣ) := by
  rw [prj_conj, prj_conj]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

private theorem entry_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (u : (M4 B)ˣ) (X Y : M4 B)
    (hu : (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c) (i j : Fin 4) (h : prj c X j * Y * prj c X i = 0) :
    ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) j i = 0 := by
  have h1 := sandwich c u X Y i j
  rw [h, mul_zero, zero_mul, hu, prj_diag, prj_diag] at h1
  have h2 := congrFun (congrFun h1 j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply, (unit_d c hc i).mul_left_eq_zero,
    (unit_d c hc j).mul_right_eq_zero] at h2
  exact h2

private theorem row_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : T * P = 0) (i : Fin 4)
    (hu : ∀ a, i < a → IsUnit (T a a)) (b a : Fin 4) : i < a → P a b = 0 := by
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_right_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [hT a x h, zero_mul]
      · rw [ih x h (ha.trans h), mul_zero]
    · simp

private theorem col_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : P * T = 0) (i : Fin 4)
    (hu : ∀ a, a < i → IsUnit (T a a)) (b a : Fin 4) : a < i → P b a = 0 := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP b) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_left_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [ih x h (h.trans ha), zero_mul]
      · rw [hT x a h, mul_zero]
    · simp

private theorem charpoly_tri (c : Fin 4 → B) (T : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) :
    T.charpoly = ∏ j, (Polynomial.X - C (c j)) := by
  rw [Matrix.charpoly_of_upperTriangular T (fun i j h => hT i j h)]
  simp only [hd]

private theorem tri_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (T R : M4 B)
    (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) (hR : ∀ i j, j < i → R i j = 0) (i j : Fin 4) (hij : i ≤ j)
    (h0 : R j i = 0) : prj c T j * R * prj c T i = 0 := by
  have hch := charpoly_tri c T hT hd
  have hT' : ∀ k i j, j < i → (T - c k • (1 : M4 B)) i j = 0 := fun k i j h => by
    simp [hT i j h, Matrix.one_apply_ne h.ne']
  have hu : ∀ k a, a ≠ k → IsUnit ((T - c k • (1 : M4 B)) a a) := fun k a h => by
    simpa [hd] using hc a k h
  have hrow := row_zero _ _ (hT' i) (eig_left c T hch i) i fun a h => hu i a h.ne'
  have hcol := col_zero _ _ (hT' j) (eig_right c T hch j) j fun a h => hu j a h.ne
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases lt_or_ge i y with hy | hy
  · rw [hrow b y hy, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro x _
    rcases lt_or_ge x j with hx | hx
    · rw [hcol a x hx, zero_mul]
    · rcases lt_or_ge y x with hxy | hxy
      · rw [hR x y hxy, mul_zero]
      · have e1 : x = j := le_antisymm (hxy.trans (hy.trans hij)) hx
        have e2 : y = i := le_antisymm hy (hij.trans (hx.trans hxy))
        rw [e1, e2, h0, mul_zero]

private theorem conj_sub (u : (M4 B)ˣ) (Y : M4 B) (a : B) :
    (u : M4 B) * (Y - a • (1 : M4 B)) * (u⁻¹ : (M4 B)ˣ) = (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) - a • (1 : M4 B) := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

private theorem conj_zero (u : (M4 B)ˣ) (Y : M4 B) (h : (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) = 0) : Y = 0 := by
  rwa [Units.mul_left_eq_zero, Units.mul_right_eq_zero] at h

end UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal in
theorem UpperTheory.V.GradeZeroInterpolatingElement.ordLocal :
    ∀ {H : Type} [Group H] (I : Subgroup H) (B : Type) [CommRing B] [IsLocalRing B] (ps : Fin 4 → H → B) (s₀ : H) (r : H →* M4 B), s₀ ∈ I → (∀ i j, i ≠ j → IsUnit (ps i s₀ - ps j s₀)) → (Ord I ps s₀ r ↔ ∃ u : (M4 B)ˣ, (∀ g i j, j < i → ((u : M4 B) * r g * (u⁻¹ : (M4 B)ˣ)) i j = 0) ∧ ∀ s ∈ I, ∀ i, ((u : M4 B) * r s * (u⁻¹ : (M4 B)ˣ)) i i = ps i s) := by
  intro H _ I B _ _ ps s₀ r hs₀ hc
  constructor
  · intro h
    obtain ⟨u, hu⟩ := diagonalize (fun a => ps a s₀) hc (r s₀) h.charpoly
    refine ⟨u, fun g i j hij => entry_zero _ hc u _ _ hu j i (h.stable g j i hij), fun s hs i => ?_⟩
    have h1 := entry_zero _ hc u _ _ hu i i (h.inert s hs i)
    rw [conj_sub, Matrix.sub_apply, sub_eq_zero] at h1
    simpa using h1
  · rintro ⟨u, h1, h2⟩
    refine ⟨?_, fun g i j hij => ?_, fun s hs i => ?_⟩
    · have h3 := charpoly_tri (fun a => ps a s₀) _ (h1 s₀) (h2 s₀ hs₀)
      rw [← h3, Matrix.coe_units_inv]
      exact (Matrix.charpoly_units_conj u (r s₀)).symm
    · apply conj_zero u
      rw [← sandwich]
      exact tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (h1 g) i j hij.le (h1 g j i hij)
    · apply conj_zero u
      rw [← sandwich, conj_sub]
      refine tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (fun a b hab => ?_) i i le_rfl ?_
      · rw [Matrix.sub_apply, h1 s a b hab]
        simp [Matrix.one_apply_ne hab.ne']
      · rw [Matrix.sub_apply, h2 s hs i]
        simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem wt_add' (i k j : Fin 4) : wt i j = wt i k + wt k j := by
  simp only [wt, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

private theorem wt_self' (i : Fin 4) : wt i i = 0 := by
  simp [wt]

variable {R : Type} [CommRing R]

private theorem wv_add' (t : Rˣ × Rˣ) (a b : ℤ × ℤ) : wv t (a + b) = wv t a * wv t b := by
  simp only [wv, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [mul_mul_mul_comm]

private theorem wv_zero' (t : Rˣ × Rˣ) : wv t 0 = 1 := by simp [wv]

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn]

private theorem adj_smul' (a : R) (X : M4 R) : adj (a • X) = a • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_smul_comm]

private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply]

private theorem tconj_apply' (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) : tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem tconj_unit' (t : Rˣ × Rˣ) : ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ) := by
  let d : Fin 4 → Rˣ := fun i => wv t (lamW i, muW i)
  have key : ∀ i j, wv t (wt i j) = d i * (d j)⁻¹ := by
    intro i j
    rw [eq_mul_inv_iff_mul_eq, ← wv_add']
    congr 1
    simp [wt]
  let u : (M4 R)ˣ := ⟨Matrix.diagonal fun i => (d i : R), Matrix.diagonal fun i => ((d i)⁻¹ : Rˣ),
    by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one], by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]⟩
  refine ⟨u, fun X => ?_⟩
  ext i j
  simp only [u, Units.inv_mk, tconj_apply', key, Units.val_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.grp :
    ∀ (R : Type) [CommRing R], (∀ X Y : M4 R, adj (X * Y) = adj Y * adj X) ∧ (∀ X : M4 R, adj (adj X) = X) ∧ (∀ X Y : M4 R, adj (X + Y) = adj X + adj Y) ∧ (∀ (a : R) (X : M4 R), adj (a • X) = a • adj X) ∧ adj (1 : M4 R) = 1 ∧ (∀ (R' : Type) [CommRing R'] (f : R →+* R') (X : M4 R), adj (X.map f) = (adj X).map f) ∧ (∀ (ν : R) (g g' : M4 R), IsGSp ν g → g * g' = 1 → adj g = ν • g') ∧ (∀ (ν ν' : R) (g g' : M4 R), IsGSp ν g → IsGSp ν' g' → IsGSp (ν * ν') (g * g')) ∧ (∀ (t : Rˣ × Rˣ) (X Y : M4 R), tconj t (X * Y) = tconj t X * tconj t Y) ∧ (∀ t : Rˣ × Rˣ, tconj t (1 : M4 R) = 1) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), adj (tconj t X) = tconj t (adj X)) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), (tconj t X).trace = X.trace) ∧ (∀ t : Rˣ × Rˣ, ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ)) := by
  intro R _
  refine ⟨adj_mul', adj_adj', ?_, adj_smul', adj_one', ?_, ?_, ?_, ?_, ?_, ?_, ?_, tconj_unit'⟩
  · intro X Y
    ext i j
    simp [adj_apply]
  · intro R' _ f X
    ext i j
    simp [adj_apply, Matrix.map_apply]
  · intro ν g g' hg h
    have hg' : adj g * g = ν • 1 := hg
    calc adj g = adj g * (g * g') := by rw [h, mul_one]
      _ = adj g * g * g' := (mul_assoc _ _ _).symm
      _ = ν • g' := by rw [hg', smul_mul_assoc, one_mul]
  · intro ν ν' g g' hg hg'
    have h1 : adj g * g = ν • 1 := hg
    have h2 : adj g' * g' = ν' • 1 := hg'
    show adj (g * g') * (g * g') = (ν * ν') • 1
    rw [adj_mul', mul_assoc, ← mul_assoc (adj g), h1, smul_mul_assoc, one_mul, mul_smul_comm, h2,
      smul_smul]
  · intro t X Y
    ext i j
    simp only [tconj_apply', Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wt_add' i k j, wv_add', Units.val_mul]
    ring
  · intro t
    ext i j
    rw [tconj_apply', Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [wt_self', wv_zero']
    · simp
  · intro t X
    ext i j
    simp only [adj_apply, tconj_apply']
    rw [wt_rev, mul_smul_comm]
  · intro t X
    simp [Matrix.trace, tconj_apply', wt_self', wv_zero']
end

