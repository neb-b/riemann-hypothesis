module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGLOfSpanRangeEqLocalRing
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

namespace GlobalTheory

theorem exists_det_add_mul_one_sub_mul_ne_zero {k : Type*} [Field k] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) k) :
    ∃ T : Matrix (Fin n) (Fin n) k, (A + T * (1 - B * A)).det ≠ 0 := by
  classical
  set LA := Matrix.toLin' A with hLA
  set K := LinearMap.ker LA
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.range LA)
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
  have h1 : Module.finrank k (LinearMap.range LA) + Module.finrank k K = Module.finrank k (Fin n → k) :=
    LinearMap.finrank_range_add_finrank_ker LA
  have h2 := Submodule.finrank_add_eq_of_isCompl hU
  have hdim : Module.finrank k K = Module.finrank k U := by omega
  let e : K ≃ₗ[k] U := LinearEquiv.ofFinrankEq K U hdim
  let f : (Fin n → k) →ₗ[k] (Fin n → k) :=
    U.subtype ∘ₗ (e : K →ₗ[k] U) ∘ₗ Submodule.linearProjOfIsCompl K K' hK'
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hfw : ∀ w, LinearMap.toMatrix' f *ᵥ w = f w := by
    intro w
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hfU : ∀ w, f w ∈ U := fun w => (e _).2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hfw] at hv
  have hAv : A *ᵥ v = 0 := by
    have hr : A *ᵥ v ∈ LinearMap.range LA := ⟨v, by rw [hLA, Matrix.toLin'_apply]⟩
    have hu : A *ᵥ v ∈ U := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (hfU _)
    exact (Submodule.disjoint_def.mp hU.disjoint) _ hr hu
  rw [hAv, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAv,
    Matrix.mulVec_zero, sub_zero] at hv
  have hvK : v ∈ K := by
    show LA v = 0
    rw [hLA, Matrix.toLin'_apply, hAv]
  have hp : Submodule.linearProjOfIsCompl K K' hK' v = ⟨v, hvK⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK' ⟨v, hvK⟩
  have he : e ⟨v, hvK⟩ = 0 := by
    apply Subtype.ext
    have : f v = 0 := hv
    change U.subtype ((e : K →ₗ[k] U) ⟨v, hvK⟩) = 0
    simpa only [f, LinearMap.comp_apply, hp] using this
  have he' : e ⟨v, hvK⟩ = e 0 := by
    exact he.trans (map_zero (e : K →ₗ[k] U)).symm
  have : (⟨v, hvK⟩ : K) = 0 := e.injective he'
  simpa using congrArg Subtype.val this

theorem exists_GL_of_span_range_eq : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] (n : ℕ) (x y : Fin n → M),
    Submodule.span O (Set.range x) = Submodule.span O (Set.range y) →
    ∃ h : GL (Fin n) O, ∀ i, y i = ∑ j, (h : Matrix (Fin n) (Fin n) O) i j • x j := by
  intro O M _ _ _ _ n x y hspan
  classical
  have hA : ∀ i, ∃ c : Fin n → O, ∑ j, c j • x j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hB : ∀ i, ∃ c : Fin n → O, ∑ j, c j • y j = x i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, A i j • x j = y i :=
    ⟨fun i => (hA i).choose, fun i => (hA i).choose_spec⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, B i j • y j = x i :=
    ⟨fun i => (hB i).choose, fun i => (hB i).choose_spec⟩
  have hmul : ∀ (P Q : Matrix (Fin n) (Fin n) O) (z : Fin n → M) i,
      ∑ j, (P * Q) i j • z j = ∑ l, P i l • ∑ j, Q l j • z j := by
    intro P Q z i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hC : ∀ l, ∑ j, ((1 : Matrix (Fin n) (Fin n) O) - B * A) l j • x j = 0 := by
    intro l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hmul, hA, hB]
    simp [Matrix.one_apply]
  let r := IsLocalRing.residue O
  obtain ⟨Tb, hTb⟩ := exists_det_add_mul_one_sub_mul_ne_zero (r.mapMatrix A) (r.mapMatrix B)
  obtain ⟨s, hs⟩ : ∃ s : IsLocalRing.ResidueField O → O, ∀ a, r (s a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  let T : Matrix (Fin n) (Fin n) O := Tb.map s
  have hT : r.mapMatrix T = Tb := by ext i j; simp [T, hs]
  let H : Matrix (Fin n) (Fin n) O := A + T * (1 - B * A)
  have hdet : IsUnit H.det := by
    have hne : r H.det ≠ 0 := by
      rw [RingHom.map_det]
      simp only [H, map_add (f := _), map_mul, map_sub, map_one, hT]
      exact hTb
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  refine ⟨hHu.unit, fun i => ?_⟩
  rw [IsUnit.unit_spec]
  simp only [H, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hA, hmul, hC, smul_zero,
    Finset.sum_const_zero, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLe
section
open TensorProduct

namespace GlobalTheory

theorem exists_span_eq_top_of_card_hom_residueField_le
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  set k := IsLocalRing.ResidueField Λ
  let V := k ⊗[Λ] A
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V

  have hsurj : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)

  have hspan : Submodule.span Λ (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b (fun i => hf i)

  let Φ : (V →ₗ[k] k) → (A →ₗ[Λ] k) := fun g =>
    (g.restrictScalars Λ).comp (TensorProduct.mk Λ k A 1)
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    have h' := LinearMap.congr_fun h y
    simp only [Φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply] at h'
    have e : x ⊗ₜ[Λ] y = x • ((1 : k) ⊗ₜ[Λ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul]
    exact congrArg (x • ·) h'

  have : Finite (A →ₗ[Λ] k) := by
    refine Finite.of_injective (fun g : A →ₗ[Λ] k => fun i => g (f i)) ?_
    intro g₁ g₂ h
    exact LinearMap.ext_on_range hspan (fun i => congr_fun h i)
  have hcard : Nat.card (V →ₗ[k] k) = Nat.card k ^ d := by
    rw [← Nat.card_congr (b.constr k).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
      Fintype.card_fin]
  have hle : Nat.card k ^ d ≤ Nat.card k ^ a := by
    rw [← hcard]; exact (Nat.card_le_card_of_injective Φ hΦ).trans h
  have hk : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hda : d ≤ a := (Nat.pow_le_pow_iff_right hk).mp hle

  refine ⟨fun i => if hi : (i : ℕ) < d then f ⟨i, hi⟩ else 0, ?_⟩
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hda⟩, by simp⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
section
open scoped BigOperators

namespace GlobalTheory


open Matrix in
theorem det_ne_zero_of_intertwines_of_span_eq_top {k : Type} [Field k] {G : Type} {r : ℕ}
    (M N : G → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (B : Matrix (Fin r) (Fin r) k) (i j : Fin r) (hB : B i j ≠ 0)
    (h : ∀ g, N g * B = B * M g) : B.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hall : ∀ X : Matrix (Fin r) (Fin r) k, ∃ Y, Y * B = B * X := by
    intro X
    have hle : Submodule.span k (Set.range M) ≤
        (LinearMap.range (LinearMap.mulRight k B)).comap (LinearMap.mulLeft k B) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_range]
      exact ⟨N g, by simp [h g]⟩
    have hX := hle (hM ▸ Submodule.mem_top : X ∈ Submodule.span k (Set.range M))
    rw [Submodule.mem_comap, LinearMap.mem_range] at hX
    obtain ⟨Y, hY⟩ := hX
    exact ⟨Y, by simpa using hY⟩
  obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv0 (funext hne)
  let X : Matrix (Fin r) (Fin r) k :=
    Matrix.of fun a b => if a = j then (if b = c then (v c)⁻¹ else 0) else 0
  have hXv : X *ᵥ v = Pi.single j 1 := by
    ext a
    by_cases ha : a = j
    · subst ha
      simp [X, Matrix.mulVec, dotProduct, hc]
    · simp [X, Matrix.mulVec, dotProduct, ha]
  obtain ⟨Y, hY⟩ := hall X
  have key : B *ᵥ (X *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hi := congrFun key i
  rw [hXv] at hi
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hi
  exact hB hi

theorem exists_gl_intertwiner_of_residual_span_eq_top :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  intro O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩
  by_cases hr : r = 0
  · subst hr
    exact ⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
    (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty
  have hdvd : ∀ x y, A p.1 p.2 ∣ A x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))
  have hd : A p.1 p.2 ≠ 0 := by
    intro h0
    apply hdet
    have hA0 : A = 0 := by
      ext x y
      have hxy := hdvd x y
      rw [h0, zero_dvd_iff] at hxy
      simpa using hxy
    rw [hA0, Matrix.det_zero]
  choose C hC using hdvd
  generalize hdd : A p.1 p.2 = d at hC hd
  have hC1 : C p.1 p.2 = 1 :=
    mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)
  have hAeq : A = d • Matrix.of C := by
    ext x y
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]
  have hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C =
      Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O) := by
    intro g
    have h1 := hA g
    rw [hAeq, Matrix.mul_smul, Matrix.smul_mul] at h1
    ext x y
    have hxy := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hd hxy
  have hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0 := by
    rw [Matrix.map_apply, Matrix.of_apply, hC1, map_one]
    exact one_ne_zero
  have hdet' := det_ne_zero_of_intertwines_of_span_eq_top
    (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O))
    (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan
    ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB
    (fun g => by rw [← Matrix.map_mul, ← Matrix.map_mul, hint g])
  have hunit : IsUnit (Matrix.of C).det := by
    by_contra hu
    apply hdet'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletion
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct Topology

namespace GlobalTheory

theorem exists_global_near_idempotent (E E' : Type) [Field E] [NumberField E] [Field E']
    [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E)
    (e : w.adicCompletion E ⊗[E] E') (he : e * e = e) (hψ : ψ e = 1)
    (p q : w.adicCompletion E ⊗[E] E') (n : ℕ) :
    ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧
      Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) -
        Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  set K := w.adicCompletion E with hK
  set B := Algebra.TensorProduct.basis K b with hB
  set Φ : (ι → K) → K ⊗[E] E' := fun t => ∑ i, t i • B i with hΦ
  have hrepr : ∀ t, B.repr (Φ t) = Finsupp.equivFunOnFinite.symm t := by
    intro t
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hΦ, map_sum, Finsupp.smul_apply, Finsupp.single_apply]
  have hM : Continuous fun t => Algebra.leftMulMatrix B (Φ t) := by
    have h : (fun t => Algebra.leftMulMatrix B (Φ t)) =
        fun t => ∑ i, t i • Algebra.leftMulMatrix B (B i) := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hΦ, map_sum, map_smul]
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

  set f1 : (ι → K) → ι → K := fun t => B.repr (Φ t * Φ t - Φ t) with hf1
  set f2 : (ι → K) → K := fun t => ψ (Φ t) - 1 with hf2
  set f3 : (ι → K) → K := fun t => Algebra.norm K (p + q * (Φ t - e)) - Algebra.norm K p with hf3
  have hf1c : Continuous f1 := by
    have h : f1 = fun t => Matrix.mulVec (Algebra.leftMulMatrix B (Φ t)) t - t := by
      funext t
      funext i
      simp only [hf1, map_sub, Finsupp.coe_sub, Pi.sub_apply]
      rw [← Algebra.leftMulMatrix_mulVec_repr, hrepr]
      simp
    rw [h]
    exact (hM.matrix_mulVec continuous_id).sub continuous_id
  have hf2c : Continuous f2 := by
    have hl : Continuous fun t => ψ (Φ t) := by
      have h := LinearMap.continuous_on_pi (ψ.toLinearMap ∘ₗ B.equivFun.symm.toLinearMap)
      convert h using 1
      funext t
      simp [hΦ, Module.Basis.equivFun_symm_apply]
    exact hl.sub continuous_const
  have hf3c : Continuous f3 := by
    have h : (fun t => Algebra.norm K (p + q * (Φ t - e))) = fun t =>
        (Algebra.leftMulMatrix B (p - q * e) + Algebra.leftMulMatrix B q *
          Algebra.leftMulMatrix B (Φ t)).det := by
      funext t
      rw [Algebra.norm_eq_matrix_det B, ← map_mul, ← map_add (f := _)]
      congr 2
      ring
    have : Continuous fun t => Algebra.norm K (p + q * (Φ t - e)) := by
      rw [h]
      exact (continuous_const.add (continuous_const.matrix_mul hM)).matrix_det
    exact this.sub continuous_const
  set t₀ : ι → K := fun i => B.repr e i with ht₀
  have hΦ₀ : Φ t₀ = e := by simp only [hΦ, ht₀]; exact B.sum_repr e
  have hball' : ∀ x₀ : K, Valued.v x₀ ≠ 0 → {z : K | Valued.v z ≤ Valued.v x₀} ∈ 𝓝 (0 : K) := by
    intro x₀ hx₀
    have hl : {y : K | Valued.v y = Valued.v x₀} ∈ 𝓝 x₀ := Valued.locally_const hx₀
    have hc : ContinuousAt (fun z : K => z + x₀) 0 := (continuous_id.add continuous_const).continuousAt
    have h' := hc.preimage_mem_nhds (by simpa using hl)
    filter_upwards [h'] with z hz
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    calc Valued.v z = Valued.v ((z + x₀) - x₀) := by rw [add_sub_cancel_right]
      _ ≤ max (Valued.v (z + x₀)) (Valued.v x₀) := Valuation.map_sub _ _ _
      _ = Valued.v x₀ := by rw [hz, max_self]
  have hva : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hx₀ : Valued.v ((algebraMap E K π) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hva, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : ∀ γ, γ = WithZero.exp (-(n : ℤ)) ∨ γ = 1 → {z : K | Valued.v z ≤ γ} ∈ 𝓝 (0 : K) := by
    rintro γ (rfl | rfl)
    · rw [← hx₀]
      exact hball' _ (by rw [hx₀]; exact WithZero.exp_ne_zero)
    · have := hball' 1 (by simp)
      simpa using this
  have h1 : ∀ᶠ t in 𝓝 t₀, ∀ i, Valued.v (f1 t i) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t => f1 t i) t₀ := ((continuous_apply i).comp hf1c).continuousAt
    have h0 : f1 t₀ i = 0 := by simp [hf1, hΦ₀, he]
    exact hc.preimage_mem_nhds (by rw [h0]; exact hball 1 (Or.inr rfl))
  have h2 : ∀ᶠ t in 𝓝 t₀, Valued.v (f2 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f2 t₀ = 0 := by simp [hf2, hΦ₀, hψ]
    exact hf2c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have h3 : ∀ᶠ t in 𝓝 t₀, Valued.v (f3 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f3 t₀ = 0 := by simp [hf3, hΦ₀]
    exact hf3c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have hd : DenseRange (Pi.map fun _ : ι => (algebraMap E K : E → K)) :=
    DenseRange.piMap fun _ => w.denseRange_algebraMap E
  obtain ⟨c, hc1, hc2, hc3⟩ := hd.mem_nhds (h1.and (h2.and h3))
  set ε : E' := ∑ i, c i • b i with hε
  have hΦc : Φ (Pi.map (fun _ : ι => (algebraMap E K : E → K)) c) = (1 : K) ⊗ₜ ε := by
    simp only [hΦ, Pi.map_apply, hε]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro i
    have h := hc1 i
    simp only [hf1, hΦc] at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub,
      hB, Algebra.TensorProduct.basis_repr_tmul] at h
    simp only [one_smul, Finsupp.mapRange_apply] at h
    rw [← hva]
    exact h
  · have h := hc2
    simpa only [hf2, hΦc] using h
  · have h := hc3
    simpa only [hf3, hΦc] using h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMem
section
namespace GlobalTheory

private theorem isClosed_submodule_padicInt_finite (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N]
    [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] [TopologicalSpace N] [IsModuleTopology ℤ_[l] N]
    (M : Submodule ℤ_[l] N) : IsClosed (M : Set N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hq := IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ
  rw [← hq.isClosed_preimage]
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[l] (M.comap π)
  have hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) :=
    IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)
  have hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hy
      obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
  rw [← hrange]
  exact (isCompact_range hc).isClosed

theorem exists_idempotent_sub_mem_of_pow_sub_mem (l : ℕ) [Fact l.Prime] {R : Type} [Ring R]
    [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R) :
    ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R),
      (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  letI : TopologicalSpace R := moduleTopology ℤ_[l] R
  haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R
  have hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R) := fun M => isClosed_submodule_padicInt_finite l M
  haveI : T2Space R := by
    rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
    simpa using hcl ⊥
  haveI : CompactSpace R := by
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] R
    have hc : Continuous π := IsModuleTopology.continuous_of_linearMap π
    exact ⟨by simpa [hπ.range_eq] using isCompact_range hc⟩
  obtain ⟨E, hES, hE⟩ := exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_const r)
    (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩
    isClosed_closure.isCompact (by
      intro x hx y hy
      refine map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      refine ⟨i + j + 1, ?_⟩
      show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)
      rw [← pow_add]
      congr 1
      omega)
  refine ⟨E, hE, fun M c h => ?_⟩
  have hC : IsClosed {x : R | x - c ∈ M} := (hcl M).preimage (continuous_id.sub continuous_const)
  exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNorm
section
open ValuativeRel

namespace GlobalTheory

theorem exists_isNonarchimedeanLocalField_spectralNorm :
    ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
      [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
      ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧
        ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  intro F _ _ _ _ K _ _ _
  letI nK : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField F K
  haveI : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := F) (L := K))
  letI rel : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  refine ⟨rel, inferInstance, ?_, fun x y => Iff.rfl⟩
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hc : (NormedField.valuation (K := K)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := K))
      (fun {s} => (NormedField.toValued (K := K)).is_topological_valuation s)
  · letI : NormedSpace F K := spectralNorm.normedSpace F K
    haveI : ProperSpace K := FiniteDimensional.proper F K
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := K))]
    infer_instance

end GlobalTheory
end

