module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem intValuation_of_span_eq_mul {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ 0) (hv : ¬ v.asIdeal ∣ I) (x : R)
    (hx0 : x ≠ 0) (hx : v.asIdeal * I = Ideal.span {x}) :
    v.intValuation x = WithZero.exp (-1) := by
  have hvd : v.asIdeal ∣ Ideal.span {x} := ⟨I, hx.symm⟩
  have hsq : ¬ v.asIdeal ^ 2 ∣ Ideal.span {x} := by
    rintro ⟨J, hJ⟩
    apply hv
    rw [← hx, pow_two, mul_assoc] at hJ
    exact ⟨J, mul_left_cancel₀ v.ne_bot hJ⟩
  have h1 : v.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd x 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hsq ((v.intValuation_le_pow_iff_dvd x 2).1 h)
  have hne : v.intValuation x ≠ 0 := v.intValuation_ne_zero x hx0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem exists_admissible_superset_finite_places : ∀ (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))), ∃ S, S₀ ⊆ S ∧ admitted F S := by
  intro F _ _ S₀
  classical
  choose J hJ using fun c : ClassGroup (𝓞 F) => ClassGroup.mk0_surjective c
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hprod : (∏ c : ClassGroup (𝓞 F), (J c : Ideal (𝓞 F))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro c _
    exact nonZeroDivisors.coe_ne_zero (J c)
  have hs : Ideal.span {(2 : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h2
  obtain ⟨M, hM, hM2, hMJ⟩ : ∃ M : Ideal (𝓞 F), M ≠ 0 ∧ Ideal.span {(2 : 𝓞 F)} ∣ M ∧
      ∀ c, (J c : Ideal (𝓞 F)) ∣ M :=
    ⟨_, mul_ne_zero hs hprod, dvd_mul_right _ _,
      fun c => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _⟩
  obtain ⟨S, hS0, hSM⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u.asIdeal ∣ M → u ∈ S :=
    ⟨S₀ ∪ (Ideal.finite_factors hM).toFinset, Finset.subset_union_left,
      fun u h => Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)⟩
  have hout : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ¬ u.asIdeal ∣ M :=
    fun u hu h => hu (hSM u h)
  have houtJ : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ∀ c, ¬ u.asIdeal ∣ (J c : Ideal (𝓞 F)) :=
    fun u hu c h => hout u hu (h.trans (hMJ c))
  refine ⟨S, hS0, ?_⟩
  intro v hv
  refine ⟨?_, ?_⟩
  · have h2 : ¬ v.asIdeal ∣ Ideal.span {(2 : 𝓞 F)} := fun h => hout v hv (h.trans hM2)
    have key : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun hm => h2 (Ideal.dvd_span_singleton.2 hm)
    rwa [map_ofNat] at key
  · let P : nonZeroDivisors (Ideal (𝓞 F)) := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
    let c : ClassGroup (𝓞 F) := (ClassGroup.mk0 P)⁻¹
    have hprod : ClassGroup.mk0 (P * J c) = 1 := by
      rw [map_mul, hJ c, mul_inv_cancel]
    have hprin : (v.asIdeal * (J c : Ideal (𝓞 F))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (P * J c).2).1 hprod
    obtain ⟨y, hy⟩ := hprin.principal
    have hy' : v.asIdeal * (J c : Ideal (𝓞 F)) = Ideal.span {y} := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
      exact (mul_ne_zero v.ne_bot (nonZeroDivisors.coe_ne_zero (J c))) hy'
    refine ⟨algebraMap (𝓞 F) F y, ?_, ?_⟩
    · rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_of_span_eq_mul v _ (nonZeroDivisors.coe_ne_zero _) (houtJ v hv c) y hy0 hy'
    · intro w hw hwv
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hyw
      have hdvd : w.asIdeal ∣ v.asIdeal * (J c : Ideal (𝓞 F)) := by
        rw [hy']
        exact Ideal.dvd_span_singleton.2 hyw
      rcases (Ideal.prime_of_isPrime w.ne_bot w.isPrime).dvd_or_dvd hdvd with h | h
      · apply hwv
        have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd h
        exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
      · exact houtJ w hw c h

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.exists_approx_mod_squares :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  intro F _ _ S y z hy hz
  set U : Set ((∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    (⋂ v : S, {p | ‖p.1 v * y v - 1‖ < min ‖(4 : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ 1}) ∩
      ⋂ σ, {p | 0 < p.2 σ * z σ} with hUdef
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · exact isOpen_lt
        ((((continuous_apply v).comp continuous_fst).mul continuous_const).sub continuous_const).norm
        continuous_const
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  have hne : U.Nonempty := by
    refine ⟨(fun v => (y v)⁻¹, z), ?_⟩
    simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun v => ?_, fun σ => mul_self_pos.2 (hz σ)⟩
    rw [inv_mul_cancel₀ (hy v), sub_self, norm_zero, lt_min_iff]
    have h4 := (map_ne_zero (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).2
      (by norm_num : (4 : F) ≠ 0)
    rw [map_ofNat] at h4
    exact ⟨norm_pos_iff.2 h4, one_pos⟩
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.LocalQuad.denseRange_finite_real F S).exists_mem_open hU hne
  simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨hxS, hxR⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨1, one_ne_zero, fun v hv => ?_, fun σ => ?_⟩
    · have h := hxS ⟨v, hv⟩
      simp at h
    · have h := hxR σ
      simp at h
  refine ⟨x, hx0, fun v hv => ?_, hxR⟩
  have h := (hxS ⟨v, hv⟩).trans_le (min_le_left _ _)
  exact _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ (Valued.toNormedField.norm_lt_iff.1 h)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGram
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isLog_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  intro ι _ _ x hx
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hx
  have hp : (xᴴ * x).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self x (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hs := hp.1.spectral_theorem
  refine ⟨_, (hp.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hp.1.eigenvalues i), ?_, rfl, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff).1 hp.1.eigenvectorUnitary.2
  · have he : (fun i => ((Real.exp (Real.log (hp.1.eigenvalues i)) : ℝ) : ℂ)) = RCLike.ofReal ∘ hp.1.eigenvalues := by
      funext i
      rw [Real.exp_log (hp.eigenvalues_pos i)]
      rfl
    rw [he]
    exact hs

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_isQuad : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E),
      IsQuad δ θ σ := by
  intro F _ _ δ hδ
  have hroot : ∀ b : F, b ^ 2 ≠ δ := fun b hb => hδ ⟨b, by rw [← hb, sq]⟩
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C δ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
  have hmon : (Polynomial.X ^ 2 - Polynomial.C δ).Monic := Polynomial.monic_X_pow_sub_C δ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C δ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C _
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C δ)) := ⟨hirr⟩
  set p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C δ with hp
  have hsq : AdjoinRoot.root p ^ 2 = AdjoinRoot.of p δ := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hneg : Polynomial.eval₂ (↑(Algebra.ofId F (AdjoinRoot p)) : F →+* AdjoinRoot p)
      (-AdjoinRoot.root p) (Polynomial.X ^ 2 - Polynomial.C δ) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, neg_sq, hsq, sub_eq_zero]
    rfl
  let τ : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot p)) (-AdjoinRoot.root p) hneg
  have hτ : τ (AdjoinRoot.root p) = -AdjoinRoot.root p := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hττ : τ.comp τ = AlgHom.id F (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hτ, map_neg, neg_neg]
  have hp0 : p ≠ 0 := hmon.ne_zero
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p)).injective
  have : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans F (AdjoinRoot p)
  refine ⟨AdjoinRoot p, inferInstance, { }, inferInstance, AdjoinRoot.root p,
    AlgEquiv.ofAlgHom τ τ hττ hττ, ⟨hδ, ?_, hτ, ?_⟩⟩
  · rw [AdjoinRoot.algebraMap_eq]; exact hsq
  · intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have hp1 : p ≠ 1 := fun h => by
      rw [h, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
    have hlt := Polynomial.natDegree_modByMonic_lt g hmon hp1
    rw [hdeg] at hlt
    have hr := Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hlt)
    refine ⟨(g %ₘ p).coeff 0, (g %ₘ p).coeff 1, ?_⟩
    have hmk : AdjoinRoot.mk p g = AdjoinRoot.mk p (g %ₘ p) := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div g p]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    conv_lhs => rw [hr]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq, add_comm]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectors
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UTrans.IsoBasis

variable {E : Type} [Field E] {n : ℕ}

def hfL (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf σ G x y
  map_add' u v := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hfL_apply (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    hfL σ G y x = hf σ G x y := rfl

theorem hf_symm {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hG.invol, hG.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hfL_ne {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) {y : Fin n → E}
    (hy : y ≠ 0) : ∃ x, hfL σ G y x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hy
  have h0 : G.mulVec (fun b => σ (y b)) = 0 := by
    funext a
    have := h (Pi.single a 1)
    simpa [hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel] using this
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0
  funext b
  have := congrFun h1 b
  simpa using this

theorem hf_comb {σ : E →+* E} (G : Matrix (Fin n) (Fin n) E) (a b : E) (u w : Fin n → E) :
    hf σ G (a • u + b • w) (a • u + b • w) =
      a * σ a * hf σ G u u + a * σ b * hf σ G u w + b * σ a * hf σ G w u + b * σ b * hf σ G w w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem exists_isotropic_avoid [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by
  obtain ⟨w, hw0, hw⟩ := hz
  obtain ⟨c, hc⟩ := hG.ne_id
  set δ := c - σ c with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hc.symm
  have hδσ : σ δ = -δ := by simp [hδ, hG.invol]
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun o : Option ι => o.elim (hfL σ G w) f) (by
      rintro (_ | i)
      · exact hfL_ne hG hw0
      · exact hf0 i)
  have huw : hf σ G u w ≠ 0 := hu none
  have hui : ∀ i, f i u ≠ 0 := fun i => hu (some i)
  set a := hf σ G w u with ha
  have hσa : σ a = hf σ G u w := hf_symm hG _ _
  have ha0 : a ≠ 0 := by
    intro h; apply huw; rw [← hσa, h, map_zero]
  have huu : σ (hf σ G u u) = hf σ G u u := hf_symm hG _ _
  let bad : ι → E := fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ
  have hfin : (Set.range bad).Finite := Set.finite_range bad
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by
    by_contra h
    push_neg at h
    exact (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin
  refine ⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩
  · rw [hf_comb, hw, ← ha, ← hσa]
    simp only [map_add (f := _), map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]
    ring
  · rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases h : f i w = 0
    · simp [h, ha0, hui i]
    · intro h'
      apply ht
      refine ⟨i, ?_⟩
      simp only [bad]
      field_simp
      linear_combination (-2 : E) * h'

theorem exists_isotropic_basis (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) (x y : Fin n → E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧
      ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  let S : Set (Fin n → E) := {z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}
  have hspan : Submodule.span E S = ⊤ := by
    by_contra h
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨z, hz0, hz1⟩ := exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by
      intro i
      fin_cases i
      · by_contra h
        push_neg at h
        exact hg0 (LinearMap.ext h)
      · exact hfL_ne hG hx
      · exact hfL_ne hG hy)
    have hzS : z ∈ S := by
      refine ⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩
      · show hf σ G z x = 0
        rw [← hf_symm hG, h, map_zero]
      · show hf σ G z y = 0
        rw [← hf_symm hG, h, map_zero]
    exact hz1 0 (hg (Submodule.subset_span hzS))
  obtain ⟨v, hvS, -, hv⟩ := Submodule.exists_fun_fin_finrank_span_eq E S
  have hn : n = Module.finrank E (Submodule.span E S) := by
    rw [hspan]; simp
  exact ⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩

end GlobalTheory.UTrans.IsoBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMinNormTensorOfIsClosedTensorSLOrbit
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.MinVec

theorem tpow_mul' {ι : Type} [Fintype ι] (d : ℕ) (x y : Matrix ι ι ℂ) :
    tpow d (x * y) = tpow d x * tpow d y := by
  classical
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem tpow_one' {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) :
    tpow d (1 : Matrix ι ι ℂ) = 1 := by
  ext a b
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem act_mul' {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ)
    (x y : Matrix ι ι ℂ) : act d (act d v x) y = act d v (x * y) := by
  funext k
  simp only [act]
  rw [tpow_mul', ← Matrix.vecMul_vecMul]

theorem act_one' {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) :
    act d v 1 = v := by
  funext k
  simp only [act]
  rw [tpow_one', Matrix.vecMul_one]

theorem norm_sq_le_nsq {κ : Type} [Fintype κ] (v : κ → ℂ) (k : κ) : ‖v k‖ ^ 2 ≤ nsq v :=
  Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

theorem continuous_nsq {κ : Type} [Fintype κ] : Continuous (nsq : (κ → ℂ) → ℝ) := by
  unfold nsq
  fun_prop

theorem exists_isMinVec_of_isClosed (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ)
    (v : TIdx ι d → ℂ) (hc : IsClosed (orb d v)) : ∃ w ∈ orb d v, IsMinVec d w := by
  have hv : v ∈ orb d v := ⟨1, det_one, (act_one' d v).symm⟩
  set K : Set (TIdx ι d → ℂ) := orb d v ∩ {w | nsq w ≤ nsq v} with hK
  have hKc : IsClosed K := hc.inter (isClosed_le continuous_nsq continuous_const)
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : TIdx ι d → ℂ)) (r := Real.sqrt (nsq v))).subset ?_
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    exact Real.le_sqrt_of_sq_le ((norm_sq_le_nsq w k).trans hw.2)
  have hcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  obtain ⟨w, hwK, hmin⟩ := hcomp.exists_isMinOn ⟨v, hv, le_refl (nsq v)⟩ continuous_nsq.continuousOn
  refine ⟨w, hwK.1, ?_⟩
  rintro u ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hwx⟩ := hwK.1
  have hu : act d w y ∈ orb d v := ⟨x * y, by rw [det_mul, hx, hy, one_mul], by rw [hwx, act_mul']⟩
  by_cases h : nsq (act d w y) ≤ nsq v
  · exact hmin (show act d w y ∈ K from ⟨hu, h⟩)
  · exact le_trans hwK.2 (le_of_lt (not_le.mp h))

end GlobalTheory.ClassFin.MinVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightAction
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mvPolynomial_ev_eq_act : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  intro ι _ _ m d t
  refine ⟨fun k => ∑ a : Fin (d k.1) → ι,
    MvPolynomial.C (t ⟨k.1, a⟩) * ∏ i, MvPolynomial.X (a i, k.2 i), ?_⟩
  intro R _ _ y k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ev, act, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod,
    MvPolynomial.aeval_X]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivApplyNeOfIsAlgebraic
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_apply_ne_of_isAlgebraic :
    ∀ z : ℂ, IsAlgebraic ℚ z → (∀ q : ℚ, z ≠ q) → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z _ hz
  by_contra h
  have hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z := fun σ => by_contra fun hne => h ⟨σ.toRingEquiv, hne⟩
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := ℚ) z hfix
  exact hz q (hq.symm.trans (by simp))

end GlobalTheory.ClassFin
end

