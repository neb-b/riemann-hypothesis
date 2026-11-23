module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianDiagonalisation
section
open Matrix in
private def Dz {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι E) : Prop :=
  ∃ g : Matrix ι ι E, g.det ≠ 0 ∧ ∃ D : ι → E, Matrix.conjTranspose g * T * g = Matrix.diagonal D

open Matrix in
private theorem Dz.of_submatrix {E ι κ : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {T : Matrix κ κ E}
    (h : Dz (T.submatrix e e)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨g.submatrix e.symm e.symm, ?_, D ∘ e.symm, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hg
  · have h1 : (g.submatrix e.symm e.symm)ᴴ * T * g.submatrix e.symm e.symm
        = (gᴴ * T.submatrix e e * g).submatrix e.symm e.symm := by
      rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _]
      simp [conjTranspose_submatrix]
    rw [h1, hD]
    ext a b
    simp [diagonal_apply]

open Matrix in
private theorem Dz.of_congr {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι E} (hP : P.det ≠ 0) (h : Dz (Pᴴ * T * P)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨P * g, ?_, D, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hP hg
  · rw [← hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]

open Matrix in
private theorem Dz.sum {E A B : Type} [Field E] [StarRing E] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (hA : ∀ X : Matrix A A E, X.IsHermitian → Dz X)
    (hB : ∀ X : Matrix B B E, X.IsHermitian → Dz X)
    (T : Matrix (A ⊕ B) (A ⊕ B) E) (hT : T.IsHermitian) (hdet : T.toBlocks₁₁.det ≠ 0) :
    Dz T := by
  obtain ⟨X, Y, Z, W, rfl⟩ : ∃ X Y Z W, T = fromBlocks X Y Z W :=
    ⟨_, _, _, _, (fromBlocks_toBlocks T).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hdet
  obtain ⟨h1, h2, h3, h4⟩ := (isHermitian_fromBlocks_iff).1 hT
  have hu : IsUnit X.det := isUnit_iff_ne_zero.2 hdet
  have hXX : X * X⁻¹ = 1 := mul_nonsing_inv X hu
  have hXi : X⁻¹ᴴ = X⁻¹ := by rw [conjTranspose_nonsing_inv, h1.eq]
  have hZ : Yᴴ = Z := h2
  subst hZ
  set U : Matrix (A ⊕ B) (A ⊕ B) E := fromBlocks 1 (-(X⁻¹ * Y)) 0 1 with hU
  have hUdet : U.det ≠ 0 := by
    rw [hU, det_fromBlocks_zero₂₁]; simp
  set S : Matrix B B E := W - Yᴴ * X⁻¹ * Y with hS
  have hSH : S.IsHermitian := by
    rw [IsHermitian, hS, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hXi, h4.eq, Matrix.mul_assoc]
  have key : Uᴴ * fromBlocks X Y Yᴴ W * U = fromBlocks X 0 0 S := by
    rw [hU, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hXi,
      h1.eq]
    have hXX' : X⁻¹ * X = 1 := nonsing_inv_mul X hu
    congr 1
    · simp
    · have hY : X * (X⁻¹ * Y) = Y := by rw [← Matrix.mul_assoc, hXX, Matrix.one_mul]
      simp [hY]
    · simp [Matrix.mul_assoc, hXX']
    · simp [Matrix.mul_assoc, hXX, hXX', hS, Matrix.add_mul, Matrix.mul_add]
      abel
  refine Dz.of_congr hUdet ?_
  rw [key]
  obtain ⟨gA, hgA, DA, hDA⟩ := hA X h1
  obtain ⟨gB, hgB, DB, hDB⟩ := hB S hSH
  refine ⟨fromBlocks gA (0 : Matrix A B E) (0 : Matrix B A E) gB, ?_, Sum.elim DA DB, ?_⟩
  · rw [det_fromBlocks_zero₂₁]; exact mul_ne_zero hgA hgB
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal]
    simp [hDA, hDB]

open Matrix in
private theorem Dz.pivot {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X)
    (T : Matrix ι ι E) (hT : T.IsHermitian) (i : ι) (hi : T i i ≠ 0) : Dz T := by
  let e : {a // a = i} ⊕ {a // ¬ a = i} ≃ ι := Equiv.sumCompl _
  refine Dz.of_submatrix e ?_
  refine Dz.sum ?_ (ih _ ?_) _ (hT.submatrix e) ?_
  · intro X _
    refine ⟨1, by simp, fun a => X a a, ?_⟩
    ext a b
    have : a = b := Subsingleton.elim _ _
    subst this
    simp
  · exact Fintype.card_subtype_lt (x := i) (by simp)
  · have : Unique {a // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [det_unique]
    have hdef : (((default : {a // a = i})) : ι) = i := (default : {a // a = i}).2
    simpa [e, toBlocks₁₁, hdef] using hi

open Matrix in
private theorem Dz.all {E : Type} [Field E] [StarRing E] [CharZero E] :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ T : Matrix ι ι E, T.IsHermitian → Dz T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ _ hcard T hT
  have ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X :=
    fun κ _ _ h X hX => IH _ (hcard ▸ h) κ rfl X hX
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact Dz.pivot ih T hT i hi
  push_neg at hd
  by_cases h0 : T = 0
  · subst h0
    exact ⟨1, by simp, 0, by ext i j; simp [Matrix.diagonal]⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by ext a b; simpa using hc a b)
  have hne : j ≠ i := by
    rintro rfl
    exact hij (hd _)
  set c := (T i j)⁻¹ with hc
  set P : Matrix ι ι E := 1 + single j i c with hP
  have hPdet : P.det ≠ 0 := by
    have : P = transvection j i c := rfl
    rw [this, det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  have hji : T j i = star (T i j) := (hT.apply j i).symm
  have hval : (Pᴴ * T * P) i i = 2 := by
    have hPH : Pᴴ = 1 + single i j (star c) := by
      rw [hP, conjTranspose_add, conjTranspose_one, conjTranspose_single]
    rw [hPH, hP]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.mul_assoc, single_mul_apply_same, mul_single_apply_same]
    have h1 : T i j * c = 1 := mul_inv_cancel₀ hij
    have h2 : star c * T j i = 1 := by
      rw [hji, ← star_mul', mul_comm, h1, star_one]
    rw [h1, h2, hd i, hd j]
    norm_num
  refine Dz.of_congr hPdet (Dz.pivot ?_ _ ?_ i ?_)
  · exact ih
  · exact isHermitian_conjTranspose_mul_mul P hT
  · rw [hval]; exact two_ne_zero

theorem UpperTheory.hermitian_diagonalisation :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ i j, σ (T j i) = T i j) → T.det ≠ 0 → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), Matrix.transpose ((g : Matrix (Fin n) (Fin n) E).map σ) * T * (g : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => algebraMap F E (D i : F) := by
  intro F E _ _ _ _ σ hσ hfix n T hT hdet
  letI : StarRing E :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by
        show σ (a * b) = σ b * σ a
        rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hstar : ∀ x : E, star x = σ x := fun _ => rfl
  have hH : T.IsHermitian := by
    ext i j
    exact hT i j
  obtain ⟨g, hg, D, hD⟩ := Dz.all n (Fin n) (by simp) T hH
  have hct : Matrix.transpose (g.map σ) = Matrix.conjTranspose g := rfl
  have hDH : (Matrix.diagonal D).IsHermitian := by
    rw [← hD]
    have := Matrix.isHermitian_conjTranspose_mul_mul g hH
    exact this
  have hfixD : ∀ i, σ (D i) = D i := by
    intro i
    have := hDH.apply i i
    simpa [hstar] using this
  have hdD : ∀ i, D i ≠ 0 := by
    intro i h0
    have h1 : (Matrix.diagonal D).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [← hD, Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (Matrix.conjTranspose g).det ≠ 0 := by
      rw [Matrix.det_conjTranspose]
      intro h3
      exact hg (by simpa using h3)
    exact mul_ne_zero (mul_ne_zero h2 hdet) hg h1
  choose d hd using fun i => hfix (D i) (hfixD i)
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    apply hdD i
    rw [← hd, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg, fun i => Units.mk0 (d i) (hd0 i), ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = g := rfl
  rw [hcoe, hct, hD]
  congr 1
  ext i
  simp [hd]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianPositiveSymplectic
section
private theorem exists_ker {n g : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (U : Submodule ℂ (Fin g → ℂ)) (hU : ∀ y, f y ∈ U)
    (hI : ∀ y, f y = 0 → f (Complex.I • y) = 0) :
    ∃ K : Submodule ℂ (Fin n → ℂ), (∀ y, y ∈ K ↔ f y = 0) ∧
      n ≤ Module.finrank ℂ K + Module.finrank ℂ U := by
  let K : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {y | f y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun z y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have hz : z • y = z.re • y + z.im • (Complex.I • y) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im z]
          ring
        rw [hz, map_add (f := _), map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }
  refine ⟨K, fun y => Iff.rfl, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.ker f = K.restrictScalars ℝ := by
    ext y
    rfl
  have h3 : LinearMap.range f ≤ U.restrictScalars ℝ := by
    rintro _ ⟨y, rfl⟩
    exact hU y
  have h4 := Submodule.finrank_mono h3
  have h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U :=
    finrank_real_of_complex U
  have h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K :=
    finrank_real_of_complex K
  have h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex]; simp
  rw [h2, h6, h7] at h1
  omega

theorem UpperTheory.hermitian_positive_symplectic :
    ∀ {g j j' : ℕ} (p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ)
        (S : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : ℝ) (U U' : Submodule ℂ (Fin g → ℂ)),
        (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (dotProduct z (H.mulVec (star z))).re) →
        IsUnit S.det → 0 < c →
        (∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
          2 * (Complex.I * (c : ℂ) * dotProduct (star y') (S.mulVec y)).re) →
        Module.finrank ℂ U = j' → Module.finrank ℂ U' = j →
        (∀ y, p y - Complex.I • p (Complex.I • y) ∈ U) →
        (∀ y, p y + Complex.I • p (Complex.I • y) ∈ U') →
        ∃ K K' : Submodule ℂ (Fin (j + j') → ℂ),
          j ≤ Module.finrank ℂ K ∧ j' ≤ Module.finrank ℂ K' ∧
          (∀ y ∈ K, p y - Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K', p y + Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) ∧
          (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) ∧
          ∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0 := by
  intro g j j' p H S c U U' hH hS hc hp hU hU' hA hB
  let Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun y => Complex.I • p (Complex.I • y)
      map_add' := fun a b => by rw [smul_add, map_add (f := _), smul_add]
      map_smul' := fun r a => by
        rw [smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]; rfl }
  have hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v := by
    intro m v
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = -(Complex.I • p y) := by
    intro y hy
    rw [sub_eq_zero.mp hy, hII, neg_neg]
  have eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = Complex.I • p y := by
    intro y hy
    rw [eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]
  obtain ⟨K, hK, dK⟩ := exists_ker (p - Q) U hA (by
    intro y hy
    change p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eA y hy, smul_neg, sub_self])
  obtain ⟨K', hK', dK'⟩ := exists_ker (p + Q) U' hB (by
    intro y hy
    change p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eB y hy, smul_neg, add_neg_cancel])
  have hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
      -(2 * c * (dotProduct (star y') (S.mulVec y)).im) := by
    intro y y'
    rw [hp]
    simp
    ring
  have hinj : ∀ y, y ≠ 0 → p y ≠ 0 := by
    intro y hy h0
    apply hy
    have hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0 := by
      intro y'
      have h := hp' y y'
      rw [h0, zero_dotProduct, Complex.zero_im] at h
      have : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have hSy : S.mulVec y = 0 := by
      ext i
      have h1 := hz (Pi.single i 1)
      have h2 := hz (Pi.single i Complex.I)
      simp [← Pi.single_star] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy
  refine ⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy,
    ?_, ?_, ?_⟩
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eA y ((hK y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))
    linarith
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eB y ((hK' y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (not_lt.mp hn)
    linarith
  · intro y hy y' hy'
    have e1 := eA y ((hK y).mp hy)
    have e2 := eB y' ((hK' y').mp hy')
    have h1 := hp' y y'
    have h2 := hp' (Complex.I • y) y'
    have h3 := hp' y (Complex.I • y')
    have h4 := hp' (Complex.I • y) (Complex.I • y')
    rw [e1] at h2 h4
    rw [e2] at h3 h4
    simp [Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4
    have r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0 := by linarith
    have r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
    exact Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne')
      ((mul_eq_zero.mp r2).resolve_left hc.ne')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HilbertNinety
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HoExistsPrime
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj17.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

theorem UpperTheory.Reformulated.B.Qj17.ho_exists_prime :
    ∀ (v : UpperTheory.Reformulated.B.Qj17.Pl) (n : ℕ),
      n ≠ (0 : ℕ) →
        (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
          ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomOr
section
namespace UpperTheory.Reformulated.B.Qk44

theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) :
    (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_cases hg : ∀ s ∈ I, f s = g s
  · exact Or.inl hg
  · right
    obtain ⟨a, ha⟩ := not_forall.mp hg
    obtain ⟨haI, hne⟩ := Classical.not_imp.mp ha
    have hah : f a = h a := (H a haI).resolve_left hne
    intro b hbI
    rcases H b hbI with hb | hb
    · rcases H (a * b) (I.mul_mem haI hbI) with hab | hab
      · rw [map_mul, map_mul, hb] at hab
        exact absurd (mul_right_cancel hab) hne
      · rw [map_mul, map_mul, hah] at hab
        exact mul_left_cancel hab
    · exact hb

end UpperTheory.Reformulated.B.Qk44
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisMore
section
theorem UpperTheory.Reformulated.B.DYka1.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j : Fin n => ‖x a j‖ ^ (2 : ℕ))
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b : Fin m => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun b _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
        gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS
end

