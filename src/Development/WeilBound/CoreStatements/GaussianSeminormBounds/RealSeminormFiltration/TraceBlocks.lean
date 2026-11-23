module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0010
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieH

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex

namespace PositivityTheory.RL.Up

section Mat

variable {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_conj' (C : Matrix β ι ℂ) (C' : Matrix ι β ℂ) (h1 : C * C' = 1) (h2 : C' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * C') = C * NormedSpace.exp Y * C' := by
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℝ _
  let φ : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * C'
      map_one' := by rw [Matrix.mul_one, h1]
      map_mul' := fun X X' => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C', h2, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun X X' => by rw [Matrix.mul_add, Matrix.add_mul] }
  exact (NormedSpace.map_exp φ ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) Y).symm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_blocks (Z Z' : Matrix β β ℂ) :
    NormedSpace.exp (Matrix.fromBlocks Z 0 0 Z') = Matrix.fromBlocks (NormedSpace.exp Z) 0 0 (NormedSpace.exp Z') := by
  have : CompleteSpace (Matrix β β ℂ) := FiniteDimensional.complete ℝ _
  have : @CompleteSpace (Matrix β β ℂ × Matrix β β ℂ) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete ℝ _
  let φ : Matrix β β ℂ × Matrix β β ℂ →+* Matrix (β ⊕ β) (β ⊕ β) ℂ :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply]
      map_zero' := Matrix.fromBlocks_zero
      map_add' := fun X X' => by simp [Matrix.fromBlocks_add] }
  have := NormedSpace.map_exp φ (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd) (Z, Z')
  refine this.symm.trans ?_
  show Matrix.fromBlocks _ 0 0 _ = _
  rw [Prod.fst_exp, Prod.snd_exp]
  rfl

theorem trace_blocks (Z Z' : Matrix β β ℂ) : (Matrix.fromBlocks Z 0 0 Z').trace = Z.trace + Z'.trace := by
  simp [Matrix.trace]

theorem iff_K {b : ℂ} {M : Matrix β β ℂ} (hu : IsUnit ((b • M).map star).det) (g : Matrix β β ℂ) :
    gᴴ * (b • M).map star * g = (b • M).map star ↔ gᵀ * M * g.map star = M := by
  rcases isEmpty_or_nonempty β with h | h
  · exact iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hb : b ≠ 0 := fun e => by
    rw [e, zero_smul, Matrix.map_zero _ (star_zero _), Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have e : gᴴ * (b • M).map star * g = (b • (gᵀ * M * g.map star)).map star := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, map_star_mul, map_star_mul]
    congr 1
    ext i j
    simp
  rw [e, (Matrix.map_injective star_injective).eq_iff, (smul_right_injective _ hb).eq_iff]

theorem frame_K {R S : ℕ} {H : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (h : IsFrame H C) :
    (H.map star)ᴴ = H.map star ∧ IsUnit (H.map star).det := by
  obtain ⟨C', h1, h2⟩ := frame_inv h
  have e : H.map star = C'ᴴ * Jm R S * C' := by
    rw [← Jm_map_star, ← h.1, map_star_mul, map_star_mul, show Cᵀ.map star = Cᴴ from rfl,
      show (C.map star).map star = C by ext; simp]
    calc _ = (C * C')ᴴ * H.map star * (C * C') := by rw [h1]; simp
      _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  refine ⟨by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.mul_assoc],
    Matrix.isUnit_det_of_left_inverse (B := C * Jm R S * Cᴴ) ?_⟩
  calc _ = C * (Jm R S * (C' * C)ᴴ * Jm R S) * C' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.conjTranspose_one, Matrix.mul_one, Jm_mul_self, Matrix.mul_one, h1]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
  {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
  {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
  {C : InfinitePlace F → Matrix β (Ix R S) ℂ}

theorem sB_frame (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {u u' : Matrix α β (AE F E)}
    {c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ} (hc : ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ)
    (hc' : ∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) :
    sB σ JA JB u u' = ∑ w, 2 * (∑ l, Fock.tw1 (c w) l * star (Fock.tw1 (c' w) l)).im := by
  rw [sB, symp, Fock.trace_trace h τ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 := Fock.herm_frame (MA := JA.map (piInf (τ w))) (MB := JB.map (piInf (τ w))) hfr.1 (hfr.2.1 w) (hfr.2.2 w)
    (c w) (c' w)
  simp only [← hc, ← hc', Matrix.map_apply] at e2
  rw [← e2, hTens, neg_one_mul, map_neg, neg_re]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, piInf_cA h]
  ring

theorem fock_data (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ}
    (hΦ : IsFockMap ψ τ d A C Φ) {D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)}
    (hD : ∀ u, At (evI F) u → ∀ f, SD (fun t => d.rho ψ (realAd F t • u)) f (D u f))
    {γ : Multiplicative ℝ →* UG (cA σ) JB} {Y : InfinitePlace F → Mat R S} (hY : IsGen τ C γ Y) :
    ∃ Z : InfinitePlace F → Matrix β β ℂ, (∀ w, (Z w).trace = (Y w).trace) ∧
      (∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = NormedSpace.exp (t • Z w)) ∧
      (∀ (t : ℝ) w, piInf (τ w) ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).det = cexp (t * (Y w).trace)) ∧
      (∀ w, (Y w).trace.re = 0) ∧
      ∃ u v : InfinitePlace F × (Ln P Q R S × Bool) → Matrix α β (AE F E), (∀ j, At (evI F) (u j)) ∧ (∀ j, At (evI F) (v j)) ∧
        (∀ x, At (evI F) x → ∀ w, x.map (piInf (τ w)) * (Z w)ᵀ = ∑ j, sB σ JA JB (v j) x • (u j).map (piInf (τ w))) ∧
        ∀ T, (8 * π * I : ℂ)⁻¹ • ∑ j, (D (u j) (D (v j) (Φ T)) + D (v j) (D (u j) (Φ T))) =
          Φ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  choose C' h1 h2 using fun w => frame_inv (hfr.2.2 w)
  choose A' a1 a2 using fun w => frame_inv (hfr.2.1 w)
  have hg : ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      C w * NormedSpace.exp (t • Y w) * C' w := fun t w => by rw [← hY, Matrix.mul_assoc, h1, Matrix.mul_one]; rfl
  have hu : ∀ w, Y w ∈ upq R S := fun w => lie_of_exp _ _ fun t => (frame_iff_smul (hfr.2.2 w) (hY t w)).1 (by
    have := congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2
    simp only [map_form h] at this
    exact this)
  obtain ⟨L, -, hL, hL'⟩ := exists_lf h τ α β
  let U : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ → Matrix α β (AE F E) := fun w c =>
    L fun w' => A w' * (Pi.single w c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ
  have hU : ∀ w c T, D (U w c) (Φ T) = Φ (atL w (heisOp c) T) := fun w c T => by
    rw [(actsLaws F κ _ _ (Φ _)).2.2.2.2 _ (hD _ (hL _) (Φ T)) (hΦ.2 _ (hL _) _ (hL' _) T)]
    congr 2
    rw [sumPl, Finset.sum_eq_single w (fun w' _ hw => by simp [atL_eq, hw, heisOp]) (by simp), atL_eq, Pi.single_eq_same]
  refine ⟨fun w => C w * Y w * C' w, fun w => by rw [Matrix.trace_mul_cycle, h2, Matrix.one_mul], fun t w => ?_,
    fun t w => ?_, fun w => ?_, fun j => U j.1 (cu (Y j.1) j.2), fun j => U j.1 (cv j.2), fun j => hL _, fun j => hL _,
    fun x hx w => ?_, fun T => ?_⟩
  · rw [hg, ← exp_conj' _ _ (h1 w) (h2 w), Matrix.mul_smul, Matrix.smul_mul]
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hg, Matrix.det_conj_of_mul_eq_one (h1 w) (h2 w),
      GlobalTheory.DetSqrtCover.det_exp, Matrix.trace_smul, real_smul]
  · rw [Matrix.trace, re_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrArg Complex.re (upq_entry (hu w) i i)
    rw [eps_sq] at this
    simp at this
    simp
    linarith
  · let c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ := fun w => A' w * x.map (piInf (τ w)) * (C' w)ᵀ
    have hc : ∀ w, x.map (piInf (τ w)) = A w * c w * (C w)ᵀ := fun w => by
      simp only [c, ← Matrix.mul_assoc, a1, Matrix.one_mul]
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.mul_one]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w (fun w' _ hw => by simp [U, hL', hw.symm]) (by simp)]
    have e : ∀ j, sB σ JA JB (U w (cv j)) x = 2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im := fun j => by
      rw [sB_frame h hfr (hL' _) hc, Finset.sum_eq_single w (fun w' _ hw => by simp [hw, Fock.tw1]) (by simp),
        Pi.single_eq_same]
    simp only [e, U, hL', Pi.single_eq_same]
    rw [Finset.sum_congr rfl fun j _ => (by rw [Matrix.mul_smul, Matrix.smul_mul] :
      (2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • (A w * cu (Y w) j * (C w)ᵀ) =
        A w * ((2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • cu (Y w) j) * (C w)ᵀ),
      ← Matrix.sum_mul, ← Matrix.mul_sum, ← expand, hc]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C w)ᵀ, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.one_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [hU, ← map_add (f := _), ← map_sum, ← map_smul]
    congr 1
    rw [Fintype.sum_prod_type, sumPl, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [atL_eq, ← fock_eq (hu w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, map_add (f := _), atL_mul, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply]

theorem sumPl_add (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (L : InfinitePlace F → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (s : InfinitePlace F → ℂ) (T : Tens F P Q R S) :
    Φ (sumPl (fun w => L w + s w • 1) T) = Φ (sumPl L T) + (∑ w, s w) • Φ T := by
  simp only [sumPl, atL_eq, map_add (f := _), map_smul, atL_one, Finset.sum_add_distrib, ← Finset.sum_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]

theorem exists_dbl {γ γ' : Multiplicative ℝ →* UG (cA σ) JB} (h : γ ∈ RLines (σ := σ) JB) (h' : γ' ∈ RLines (σ := σ) JB) :
    ∃ δ ∈ RLines (σ := σ) (dbl JB), ∀ t, ((δ t).1 : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
      Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) := by
  let φ : Matrix β β (AE F E) × Matrix β β (AE F E) →* Matrix (β ⊕ β) (β ⊕ β) (AE F E) :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply] }
  let δ0 : Multiplicative ℝ →* GL (β ⊕ β) (AE F E) := (Units.map φ).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp
    (((UG (cA σ) JB).subtype.comp γ).prod ((UG (cA σ) JB).subtype.comp γ')))
  have c1 : Continuous fun t => (γ t).1 := continuous_subtype_val.comp h.1
  have c2 : Continuous fun t => (γ' t).1 := continuous_subtype_val.comp h'.1
  have hc : Continuous δ0 := Units.continuous_iff.2
    ⟨(Units.continuous_val.comp c1).matrix_fromBlocks continuous_const continuous_const (Units.continuous_val.comp c2),
     (Units.continuous_coe_inv.comp c1).matrix_fromBlocks continuous_const continuous_const
      (Units.continuous_coe_inv.comp c2)⟩
  refine ⟨δ0.codRestrict _ fun t => ?_, ⟨hc.subtype_mk _, fun t u hu => ?_⟩, fun t => rfl⟩
  · have e1 : ((γ t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ t).2
    have e2 : ((γ' t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ' t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ' t).2
    show (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)))ᵀ * dbl JB *
      (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E))).map (cA σ) = dbl JB
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  · show u • (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) - 1) = 0
    have e1 := h.2 t u hu
    have e2 := h'.2 t u hu
    rw [smul_sub, sub_eq_zero] at e1 e2 ⊢
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul]
    exact congrArg₂ (fun a b => Matrix.fromBlocks a (u • 0) (u • 0) b) e1 e2

theorem at_det {g : Matrix β β (AE F E)} (hg : At (evI F) (g - 1)) : At (evI F) (g.det - 1) := fun u hu => by
  let J : Ideal (AE F E) := LinearMap.ker (LinearMap.mul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) u))
  have hJ : ∀ x, x ∈ J ↔ u • x = 0 := fun x => by rw [Algebra.smul_def]; rfl
  rw [← hJ, ← Ideal.Quotient.eq, RingHom.map_det, map_one, ← Matrix.det_one (n := β),
    ← map_one (Ideal.Quotient.mk J).mapMatrix]
  congr 1
  ext i j
  exact Ideal.Quotient.eq.2 ((hJ _).2 (congrFun (congrFun (hg u hu) i) j))

theorem norm_eq_one (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z : AE F E} (hz : At (evI F) (z - 1))
    (h1 : ∀ w, ‖piInf (τ w) z‖ = 1) : Algebra.norm (AF F) z = 1 := by
  obtain ⟨x, hx⟩ := exists_moved h
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact ρ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hy : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ, neg_sub]
  have hy0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  obtain ⟨B, b0, b1⟩ := exists_basis h (β := x - σ x) (by
    rw [hy]
    exact fun e => hy0 (by linear_combination (-1 / 2 : E) * e))
  have hq : IsQuad (cA σ) ((1 : AF F) ⊗ₜ[F] (x - σ x)) :=
    ⟨(IsUnit.mk0 _ hy0).map (Algebra.TensorProduct.includeRight (R := F) (A := AF F)),
      by rw [← TensorProduct.tmul_neg, ← hy]; rfl,
      Algebra.TensorProduct.basis (AF F) B, by rw [Algebra.TensorProduct.basis_apply, b0]; rfl,
      by rw [Algebra.TensorProduct.basis_apply, b1]⟩
  refine hq.algebraMap_injective ?_
  rw [hq.algebraMap_norm, map_one, ← sub_eq_zero]
  refine eq_zero_of_piInf h τ _ (fun u hu => ?_) fun w => ?_
  · have e : z * cA σ z - 1 = (z - 1) * cA σ z + cA σ (z - 1) := by rw [map_sub, map_one]; ring
    rw [e, smul_add, ← smul_mul_assoc, ← map_smul, hz u hu, zero_mul, map_zero, add_zero]
  · rw [map_sub, map_mul, piInf_cA h, map_one, star_def, mul_conj, normSq_eq_norm_sq, h1]
    simp

theorem sB_anti (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB u v = -sB σ JA JB v u := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply, ← map_neg, ← map_neg, ← map_neg, ← map_neg, neg_neg,
    neg_sub]

theorem sB_neg (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB (-u) v = -sB σ JA JB u v := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [map_neg, Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg, map_sub]
  ring

theorem sB_zero (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (v : Matrix α β (AE F E)) :
    sB σ JA JB 0 v = 0 := by
  have := sB_neg d 0 v
  rw [neg_zero] at this
  linarith

variable {dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)}

theorem sB_dbl (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) (u u' v v' : Matrix α β (AE F E)) :
    sB σ JA (dbl JB) (Matrix.fromCols u u') (Matrix.fromCols v v') = sB σ JA JB u v - sB σ JA JB u' v' := by
  rw [sB, sB, sB, dd.form, d.form, d.form, hdd, hdd, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim,
    ← Fock.evIh_apply, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [dotProduct_neg, map_sub, map_add (f := _), map_neg]
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem at_cols {u u' : Matrix α β (AE F E)} (h : At (evI F) u) (h' : At (evI F) u') : At (evI F) (Matrix.fromCols u u') :=
  fun s hs => by
    ext i j
    rcases j with j | j
    · exact congrFun (congrFun (h s hs) i) j
    · exact congrFun (congrFun (h' s hs) i) j

theorem box_D (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) {D Dd} (hD : IsD d D) (hDd : IsD dd Dd) {u : Matrix α β (AE F E)}
    (hu : At (evI F) u) {B : SInf F (κ ⊕ κ)} {f f' : SInf F κ} (hB : ∀ x, B x = f (x ∘ Sum.inl) * f' (x ∘ Sum.inr)) (x) :
    Dd (Matrix.fromCols u 0) B x = D u f (x ∘ Sum.inl) * f' (x ∘ Sum.inr) := by
  let L1 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
  let L2 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)
  have h1 := ((f.hasFDerivAt (L1 x)).comp x L1.hasFDerivAt).mul ((f'.hasFDerivAt (L2 x)).comp x L2.hasFDerivAt)
  have h2 : fderiv ℝ B x = _ := (congrArg (fderiv ℝ · x) (funext hB)).trans h1.fderiv
  have e1 : L1 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = fun i => evI F ((d.e u).1 i) := rfl
  have e2 : L2 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = 0 := funext fun _ => Der.evI_zero
  rw [hDd _ (at_cols hu fun _ _ => smul_zero _), hD u hu, hdd, h2, hB, map_zero]
  simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, e1, e2, map_zero, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Der.evI_zero, mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul, Function.comp_apply]
  show _ + f' (x ∘ Sum.inr) * fderiv ℝ f (x ∘ Sum.inl) _ - _ = _
  ring

end PositivityTheory.RL.Up

namespace PositivityTheory.RL

open Up

end PositivityTheory.RL

end
