module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section RationalPoints

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem cap_fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
theorem cap_fv_neg (x : Fin n → E) : fv F (-x) = - fv F x := by
  funext i
  simp [fv, TensorProduct.tmul_neg]

omit [NumberField E] in
theorem cap_fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i
  simp [fv]

omit [NumberField E] in
theorem cap_fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [cap_fv_zero]
  | succ d ih => rw [succ_nsmul, succ_nsmul, cap_fv_add, ih]

omit [NumberField E] in
theorem cap_gen_mem (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : Fin n → E) (hx : x ∈ L) :
    (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) ∈ hat F L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

omit [NumberField E] in
theorem cap_fv_mem (L : Set (Fin n → E)) (x : Fin n → E) (hx : x ∈ L) : fv F x ∈ hat F L :=
  cap_gen_mem F L 1 (fun v => (v.adicCompletionIntegers F).one_mem) x hx

omit [NumberField E] in
theorem cap_split (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, algebraMap_smul]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

omit [NumberField E] in
theorem cap_tmul_nsmul (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => a ⊗ₜ[F] (d • x) i : Fin n → RA F E)
      = d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [Pi.smul_apply]
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.tmul_add, ih]

theorem cap_exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target ..)

end RationalPoints

theorem hat_rational_points_and_approx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L hfg hsp
  have h3 : ∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
    have hadd : ∀ z w : Fin n → RA F E, (∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, w - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, z + w - fv F x ∈ (hat F (L : Set (Fin n → E)))) := by
      rintro z w ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      have := add_mem hx hy
      rw [cap_fv_add]
      convert this using 1
      abel
    have hzero : ∃ x : Fin n → E, (0 : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) :=
      ⟨0, by rw [cap_fv_zero, sub_zero]; exact zero_mem _⟩
    have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (y : Fin n → E), ∃ x : Fin n → E,
        (fun i => a ⊗ₜ[F] y i : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro a y
      obtain ⟨d, hd, hy⟩ := cap_exists_denom L hsp y
      obtain ⟨r, a', ha', rfl⟩ := (_root_.GlobalTheory.AdLat.strong_approximation_mod_nat F d hd).1 a
      refine ⟨algebraMap F E r • y, ?_⟩
      rw [cap_split, add_sub_cancel_left, ← cap_tmul_nsmul]
      exact cap_gen_mem F _ a' ha' _ hy
    have hsingle : ∀ (i : Fin n) (t : RA F E), ∃ x : Fin n → E,
        (Pi.single i t : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul a y =>
        have := hgen a (Pi.single i y)
        convert this using 4
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      | add s t hs ht =>
        rw [Pi.single_add]
        exact hadd _ _ hs ht
    intro z
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ (fun z => ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))))
      hadd hzero (fun i _ => hsingle i (z i))
  refine ⟨?_, ?_, h3, ?_⟩
  · intro v
    obtain ⟨s, e, c, -, hc, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
    have hv : fv F v = ∑ a, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr v a) : RA F E) • fv F (e a) := by
      funext i
      have h := congrFun (e.sum_repr v) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [fv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
      rw [← TensorProduct.tmul_sum, h]
    rw [hv, _root_.GlobalTheory.AdLat.mem_hat_pseudoBasis_iff F E n L e c hc, hc]
    exact forall_congr' fun a => (_root_.GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties F E).2.1 (c a) _
  · intro N hN z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨r, a', ha', rfl⟩ := (_root_.GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 a ha
      refine ⟨algebraMap F E (r : F) • x, ?_, _, cap_gen_mem F _ a' ha' x hx, cap_split F _ _ _ _⟩
      exact L.smul_mem (algebraMap (𝓞 F) (𝓞 E) r) hx
    | zero => exact ⟨0, L.zero_mem, 0, zero_mem _, by simp [cap_fv_zero]⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      obtain ⟨x', hx', w', hw', rfl⟩ := hz'
      refine ⟨x + x', L.add_mem hx hx', w + w', add_mem hw hw', ?_⟩
      rw [cap_fv_add, smul_add]
      abel
    | neg z _ hz =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      refine ⟨-x, L.neg_mem hx, -w, neg_mem hw, ?_⟩
      rw [cap_fv_neg, smul_neg]
      abel
  · intro z
    obtain ⟨x, hx⟩ := h3 z
    obtain ⟨d, hd, hdx⟩ := cap_exists_denom L hsp x
    refine ⟨d, hd, ?_⟩
    have := add_mem (nsmul_mem hx d) (cap_fv_mem F (L : Set (Fin n → E)) _ hdx)
    rw [cap_fv_nsmul, ← smul_add, sub_add_cancel] at this
    exact this

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodChange

open Complex Matrix NumberField in
private theorem matrix_eq_of_dotProduct_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] (M K : Matrix n n ℤ)
    (h : ∀ a b : n → ℤ, a ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ (K *ᵥ b)) : M = K := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

open Complex Matrix NumberField in
private theorem omegaStd_eq_neg_dotProduct_J {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b = -(a ⬝ᵥ (J (Fin g) ℤ *ᵥ b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
  simp [Matrix.J, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Finset.sum_sub_distrib,
    neg_mulVec, one_mulVec, Finset.sum_neg_distrib, mul_comm]
  ring

open Complex Matrix NumberField in
private theorem fromBlocks_swap_mul_J_mul_swap {g : ℕ} :
    fromBlocks (0 : Matrix (Fin g) (Fin g) ℤ) 1 1 0 * J (Fin g) ℤ * fromBlocks 0 1 1 0 =
      -J (Fin g) ℤ := by
  simp [Matrix.J, fromBlocks_multiply, fromBlocks_neg]


open Complex Matrix NumberField in
theorem _root_.GlobalTheory.PeriodChange.swap_mem_symplectic {g : ℕ} (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hN : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd (N *ᵥ a) (N *ᵥ b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) :
    Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∈
      Matrix.symplecticGroup (Fin g) ℤ := by
  set S : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := fromBlocks 0 1 1 0 with hS
  have hNJN : Nᵀ * J (Fin g) ℤ * N = J (Fin g) ℤ := by
    apply matrix_eq_of_dotProduct_mulVec_eq
    intro a b
    have := hN a b
    rw [omegaStd_eq_neg_dotProduct_J, omegaStd_eq_neg_dotProduct_J, neg_inj] at this
    rw [← this, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
  have hSt : Sᵀ = S := by simp [hS, fromBlocks_transpose]
  have hM : Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ =
      S * Nᵀ * S := by
    conv_rhs => rw [← fromBlocks_toBlocks N]
    simp [hS, fromBlocks_transpose, fromBlocks_multiply]
  rw [hM, SymplecticGroup.mem_iff]
  calc S * Nᵀ * S * J (Fin g) ℤ * (S * Nᵀ * S)ᵀ
      = S * (Nᵀ * ((S * J (Fin g) ℤ * S) * N)) * S := by
        simp only [transpose_mul, transpose_transpose, hSt, Matrix.mul_assoc]
    _ = -(S * (Nᵀ * J (Fin g) ℤ * N) * S) := by
        rw [fromBlocks_swap_mul_J_mul_swap]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    _ = J (Fin g) ℤ := by rw [hNJN, fromBlocks_swap_mul_J_mul_swap, neg_neg]


open Complex Matrix NumberField in
theorem _root_.GlobalTheory.PeriodChange.change_of_normalisation {g : ℕ} (h h' τ' A B L R : Matrix (Fin g) (Fin g) ℂ)
    (hA : h * L = A) (hB : h * R = B) (hL : h' * L = 1) (hR : h' * R = τ') (hs : τ'.IsSymm)
    (hu : IsUnit h.det) :
    τ' = Bᵀ * (Aᵀ)⁻¹ ∧ h' = ((Aᵀ)⁻¹)ᵀ * h ∧ h.det = (Aᵀ).det * h'.det := by
  have hL' : L = h⁻¹ * A := by
    rw [← hA, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have hAh : h' * h⁻¹ * A = 1 := by rw [Matrix.mul_assoc, ← hL', hL]
  have hA1 : A * (h' * h⁻¹) = 1 := mul_eq_one_comm.mp hAh
  have hAu : IsUnit A.det := isUnit_det_of_right_inverse hA1
  have hAinv : A⁻¹ = h' * h⁻¹ := inv_eq_right_inv hA1
  have hh' : h' = A⁻¹ * h := by
    rw [hAinv, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc τ' = τ'ᵀ := hs.eq.symm
      _ = Bᵀ * (Aᵀ)⁻¹ := by
        rw [← hR, hh', Matrix.mul_assoc, hB, transpose_mul, transpose_nonsing_inv]
  · rw [← transpose_nonsing_inv, transpose_transpose]; exact hh'
  · have : h = A * h' := by
      rw [hh', ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
    conv_lhs => rw [this]
    rw [det_mul, det_transpose]

open Complex Matrix NumberField in
private theorem addMonoidHom_eq_matrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℕ}
    (Q : (ι → ℤ) →+ (Fin g → ℂ)) (x : ι → ℤ) :
    Q x = (Matrix.of fun i u => Q (Pi.single u 1) i) *ᵥ fun u => (x u : ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  funext i
  simp only [Finset.sum_apply, mulVec, dotProduct, of_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hs : Pi.single u (x u) = x u • (Pi.single u 1 : ι → ℤ) := by
    ext v; by_cases hv : v = u <;> simp [hv]
  rw [hs, map_zsmul, Pi.smul_apply, zsmul_eq_mul, mul_comm]


open Complex Matrix NumberField in
theorem _root_.GlobalTheory.PeriodChange.period_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ)) (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ a, P' a = P (gam a)) → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → (∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → τ' ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → IsUnit h.det → ∃ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, γ = Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∧ τ' = _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∧ h' = ((_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹)ᵀ * h ∧ h.det = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * h'.det := by
  intro E _ _ _ H D g bas gam N P P' h h' τ τ' hEF hgam hNdef hP' hnorm hnorm' hτ hτ' hu
  have hτs : τ.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ; exact hτ.1
  have hτs' : τ'.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ'; exact hτ'.1
  have hNv : ∀ a, bas (N *ᵥ a) = gam (bas a) := by
    intro a
    let f₁ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) := (Matrix.mulVecLin N).toAddMonoidHom
    let f₂ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) :=
      bas.symm.toLinearMap.toAddMonoidHom.comp
        (gam.toAddEquiv.toAddMonoidHom.comp bas.toLinearMap.toAddMonoidHom)
    have hf : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun v x => ?_
      have hs : Pi.single v x = x • (Pi.single v 1 : Fin g ⊕ Fin g → ℤ) := by
        ext u; by_cases hu : u = v <;> simp [hu]
      rw [hs, map_zsmul, map_zsmul]
      congr 1
      funext u
      simp [f₁, f₂, hNdef, mulVec_single_one]
    have := DFunLike.congr_fun hf a
    change N *ᵥ a = bas.symm (gam (bas a)) at this
    rw [this, LinearEquiv.apply_symm_apply]
  have hγ := _root_.GlobalTheory.PeriodChange.swap_mem_symplectic N fun a b => by
    have := hEF (N *ᵥ a) (N *ᵥ b)
    rw [hNv, hNv, hgam, hEF] at this
    exact (neg_inj.mp this).symm
  have hcol : ∀ v, h *ᵥ P' (bas (Pi.single v 1)) =
      fun i => (N (Sum.inl i) v : ℂ) + ∑ j, τ i j * N (Sum.inr j) v := by
    intro v
    have hPb : ∀ x, P (bas x) =
        (Matrix.of fun i u => P (bas (Pi.single u 1)) i) *ᵥ fun u => (x u : ℂ) :=
      fun x => addMonoidHom_eq_matrix_mulVec (P.comp bas.toLinearMap.toAddMonoidHom) x
    rw [hP', ← hNv, hPb, mulVec_mulVec]
    funext i
    have hc : ∀ u, (h * Matrix.of fun i u => P (bas (Pi.single u 1)) i) i u
        = (h *ᵥ P (bas (Pi.single u 1))) i := by
      intro u; simp [Matrix.mul_apply, mulVec, dotProduct]
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [hc, (hnorm _).1, (hnorm _).2]
    simp [mulVec_single_one, Pi.single_apply]
  let A₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₁.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₁.map (fun x : ℤ => (x : ℂ))
  let B₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₂.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₂.map (fun x : ℤ => (x : ℂ))
  have hAL : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = A₀ := by
    ext i k
    have := congrFun (hcol (Sum.inl k)) i
    simp only [mulVec, dotProduct] at this
    simp [A₀, Matrix.mul_apply, this, toBlocks₁₁, toBlocks₂₁]
  have hBR : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = B₀ := by
    ext i k
    have := congrFun (hcol (Sum.inr k)) i
    simp only [mulVec, dotProduct] at this
    simp [B₀, Matrix.mul_apply, this, toBlocks₁₂, toBlocks₂₂]
  have hL1 : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = 1 := by
    ext i k
    have := congrFun (hnorm' k).1 i
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  have hRτ : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = τ' := by
    ext i k
    have := congrFun (hnorm' k).2 i
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Pi.single_apply]
  obtain ⟨e₁, e₂, e₃⟩ :=
    _root_.GlobalTheory.PeriodChange.change_of_normalisation h h' τ' A₀ B₀ _ _ hAL hBR hL1 hRτ hτs' hu
  have hj : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut (Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ) τ =
      A₀ᵀ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [A₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  refine ⟨_, hγ, rfl, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct
    rw [hj, e₁]
    congr 1
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [B₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  · rw [hj]; exact e₂
  · rw [hj]; exact e₃

end GlobalTheory.PeriodChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_mem_adelicCompletionOfElementSet {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (x : ι → RA F E) (h : ∀ i ∈ s, x i ∈ hat1 F (I i : Set E)) :
    ∏ i ∈ s, x i ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Algebra.TensorProduct.one_def]
    exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (h a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem det_mem_adelicCompletionOfElementSet {n : ℕ} (r s : Fin n → FractionalIdeal (𝓞 E)⁰ E)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((r i * s j : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    M.det ∈ hat1 F (((∏ i, r i) * ∏ j, s j : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  have := prod_mem_adelicCompletionOfElementSet F Finset.univ (fun j => r (σ j) * s j) (fun j => M (σ j) j)
    (fun j _ => h _ _)
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ r] at this
  rw [Units.smul_def]
  exact zsmul_mem this _

theorem cramer_mem_adelicCompletionOfElementSet {n : ℕ} (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
    (w : Fin n → RA F E) (hw : ∀ i, w i ∈ hat1 F (cI i : Set E)) (a : Fin n) :
    M.cramer w a ∈ hat1 F (cI a : Set E) := by
  rw [Matrix.cramer_apply]
  have := det_mem_adelicCompletionOfElementSet F cI (Function.update (fun j => (cI j)⁻¹) a 1) (M.updateCol a w) (by
    intro i j
    by_cases hj : j = a
    · subst hj
      simpa using hw i
    · simpa [hj] using h i j)
  have e : (∏ i, cI i) * ∏ j, Function.update (fun j => (cI j)⁻¹) a 1 j = cI a := by
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb, hc b]
    · simp
  rwa [e] at this

theorem algEquiv_mem_one (c : E ≃ₐ[F] E) (x : E) (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

end

theorem inv_mulVec_mem_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (c : E ≃ₐ[F] E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ z ∈ (hat F (L : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E)))) → (g : Matrix (Fin n) (Fin n) (RA F E)).det * sg (FiniteAdeleRing (𝓞 F) F) c (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ z ∈ (hat F (L : Set (Fin n → E))), ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g c hfg hsp hg hdet z hz
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd : G.det ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    have := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
    rwa [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i),
      hkdet] at this
  have hd' := galoisAut_mem_adelicCompletionOfElementSet F c (algEquiv_mem_one F c) hd
  have hw : ∀ a, (Q *ᵥ z) a ∈ hat1 F (cI a : Set E) := by
    rw [← key', Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hz
  have hu : P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z)) ∈
      hat F (L : Set (Fin n → E)) := by
    rw [key']
    intro a
    have := (adelicCompletion_fractionalIdeal_properties F E).1 1 (cI a) _ hd' _ (cramer_mem_adelicCompletionOfElementSet F cI hc k hk _ hw a)
    rwa [one_mul] at this
  have hz' : G *ᵥ (P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z))) = z := by
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_cramer, smul_smul, hkdet, mul_comm, hdet, one_smul, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec]
  rw [← hz', Matrix.mulVec_mulVec, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]
  exact hu

end GlobalTheory.AdLat
end

