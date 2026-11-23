module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeRealEmbeddings
section
open NumberField MeasureTheory Filter Topology

namespace GlobalTheory.Shintani

theorem denseRange_realEmbeddings :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
      DenseRange (fun (x : F) (σ : F →+* ℝ) => σ x) := by
  intro F _ _ _
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  let E : ∀ w : InfinitePlace F, w.Completion → ℝ := fun w z =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z
  have hs : Function.Surjective (Pi.map E) := by
    intro y
    refine ⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩
    funext w
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  have hc : Continuous (Pi.map E) := by
    refine continuous_pi fun w => ?_
    have : (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) := by
      funext z; exact InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z
    change Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have h2 := hs.denseRange.comp h1 hc
  let g : (F →+* ℝ) → InfinitePlace F := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    intro σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ := fun σ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)
  have hg : Function.Injective g := by
    intro σ τ h
    have := hemb σ
    rw [h, hemb τ] at this
    ext x
    have h3 := congrArg (fun f : F →+* ℂ => f x) this
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3
    exact h3.symm
  have hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x := by
    intro x σ
    change E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x
    rw [InfiniteAdeleRing.algebraMap_apply]
    apply Complex.ofReal_injective
    simp only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    change InfinitePlace.Completion.extensionEmbedding (g σ)
      (↑((WithAbs.equiv (g σ).1).symm x)) = (σ x : ℂ)
    rw [InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply, hemb σ]
    rfl

  let P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ) := fun y σ => y (g σ)
  have hPs : Function.Surjective P := fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩
  have hPc : Continuous P := continuous_pi fun σ => continuous_apply (g σ)
  convert hPs.denseRange.comp h2 hPc using 1
  funext x σ
  exact (hval x σ).symm

end GlobalTheory.Shintani
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
section
open Matrix Finset

namespace GlobalTheory.DetDeriv

theorem derivation_prod {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type} [DecidableEq ι] (δ : Derivation K R R) (s : Finset ι) (f : ι → R) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * δ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih,
      add_comm, Finset.smul_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      smul_eq_mul]
    ring

theorem derivation_det_rows {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ t, (M.updateRow t fun u => δ (M t u)).det := by
  have key : ∀ N : Matrix ι ι R,
      N.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, δ.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    derivation_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]

theorem det_updateRow_eq_sum_adjugate {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (t : ι) (v : ι → R) :
    (M.updateRow t v).det = ∑ j, M.adjugate j t * v j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec]
  simp [dotProduct, transpose_apply]

theorem derivation_det {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  rw [derivation_det_rows]
  exact Finset.sum_congr rfl fun i _ => det_updateRow_eq_sum_adjugate M i _

theorem main : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R),
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) :=
  fun δ _ _ _ M => derivation_det δ M

end GlobalTheory.DetDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendMvPolynomial
section
open IsLocalRing TensorProduct

namespace GlobalTheory


open MvPolynomial in
noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (D (p.coeff s))

open MvPolynomial in
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    (coeffDerivFun D p).coeff m = D (p.coeff m) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change AddMonoidAlgebra.coeff (coeffDerivFun D _) m = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul_monomial, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _)]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _)]; ring

theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationFamilyCotangentBasis
section
open IsLocalRing

namespace GlobalTheory.CoordsAlg

noncomputable def cotFun {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) : Module.Dual R I.Cotangent :=
  ((I • ⊤ : Submodule A I).restrictScalars R).liftQ f (fun x hx => by
      refine LinearMap.mem_ker.mpr (hf x ?_)
      rw [← Ideal.toCotangent_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (I • ⊤ : Submodule A I)).symm.toLinearMap

theorem coords_of_derivation_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  intro R A _ _ _ _ _ _ e he hfree hfin n dv hadd hmul halg huniq
  set I := RingHom.ker e with hIdef
  let dH : Fin n → A →+ R := fun a => AddMonoidHom.mk' (dv a) (hadd a)
  have hdH : ∀ a x, dv a x = dH a x := fun _ _ => rfl
  have hsmul : ∀ a r x, dv a (algebraMap R A r * x) = r * dv a x := by
    intro a r x; rw [hmul, he, halg]; ring
  have hI2 : ∀ a x, x ∈ I ^ 2 → dv a x = 0 := by
    intro a x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro u hu v hv
      rw [hmul, (RingHom.mem_ker).1 hu, (RingHom.mem_ker).1 hv]; ring
    · intro u v hu hv; rw [hadd, hu, hv, add_zero]
  have hdec : ∀ x : A, x - algebraMap R A (e x) ∈ I := fun x => by
    simp [I, RingHom.mem_ker, he]
  let fa : Fin n → (I →ₗ[R] R) := fun a =>
    { toFun := fun x => dv a x
      map_add' := fun x y => hadd a x y
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, RingHom.id_apply, smul_eq_mul]
        exact hsmul a r x }
  let ℓ : Fin n → Module.Dual R I.Cotangent := fun a => cotFun I (fa a) (fun x hx => hI2 a x hx)
  have hℓ : ∀ a (x : I), ℓ a (I.toCotangent x) = dv a x := fun _ _ => rfl
  let Ψ : (Fin n → R) →ₗ[R] Module.Dual R I.Cotangent :=
    ∑ a, (LinearMap.proj a : (Fin n → R) →ₗ[R] R).smulRight (ℓ a)
  have hΨ : ∀ c (x : I), Ψ c (I.toCotangent x) = ∑ a, c a * dv a x := by
    intro c x
    simp [Ψ, LinearMap.sum_apply, hℓ]

  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∀ x : A, ∑ a, c a * dv a x = 0 := by
      intro x
      have hx := hΨ c ⟨_, hdec x⟩
      rw [hc] at hx
      have : ∀ a, dv a (x - algebraMap R A (e x)) = dv a x := by
        intro a; rw [hdH, map_sub, ← hdH, ← hdH, halg, sub_zero]
      simp only [this] at hx
      exact hx.symm
    obtain ⟨c0, -, hc0⟩ := huniq (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp)
      (fun _ => rfl)
    have h1 : c = c0 := hc0 c (fun x => (h0 x).symm)
    have h2 : (0 : Fin n → R) = c0 := hc0 0 (fun x => by simp)
    rw [h1, ← h2]
  have hΨsurj : Function.Surjective Ψ := by
    intro φ
    let D : A → R := fun x => φ (I.toCotangent ⟨_, hdec x⟩)
    have Dadd : ∀ x y, D (x + y) = D x + D y := by
      intro x y
      simp only [D, ← map_add (f := _)]
      congr 2
      ext; simp; ring
    have Dalg : ∀ r, D (algebraMap R A r) = 0 := by
      intro r
      simp only [D]
      have : (⟨_, hdec (algebraMap R A r)⟩ : I) = 0 := by ext; simp [he]
      rw [this, map_zero, map_zero]
    have Dmul : ∀ x y, D (x * y) = e x * D y + e y * D x := by
      intro x y
      have hsq : (x - algebraMap R A (e x)) * (y - algebraMap R A (e y)) ∈ I ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul (hdec x) (hdec y)
      have key : (⟨_, hdec (x * y)⟩ : I) = e x • (⟨_, hdec y⟩ : I) + e y • (⟨_, hdec x⟩ : I) +
          ⟨_, Ideal.pow_le_self two_ne_zero hsq⟩ := by
        ext
        simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
        ring
      have hw0 : I.toCotangent ⟨(x - algebraMap R A (e x)) * (y - algebraMap R A (e y)),
          Ideal.pow_le_self two_ne_zero hsq⟩ = 0 := (I.toCotangent_eq_zero _).2 hsq
      simp only [D]
      rw [key]
      simp only [map_add (f := _), LinearMap.map_smul_of_tower, hw0,
        map_zero, add_zero, map_smul, smul_eq_mul]
    obtain ⟨c, hc, -⟩ := huniq D Dadd Dmul Dalg
    refine ⟨c, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, ← hc]
    simp only [D]
    congr 2
    ext
    simp [(RingHom.mem_ker).1 x.2]
  let Ψe : (Fin n → R) ≃ₗ[R] Module.Dual R I.Cotangent :=
    LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨsingle : ∀ a, Ψ (Pi.single a 1) = ℓ a := by
    intro a
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, hℓ]
    simp [Pi.single_apply]
  let w : Fin n → I.Cotangent := fun i =>
    (Module.evalEquiv R I.Cotangent).symm
      ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ Ψe.symm.toLinearMap)
  have hw : ∀ a i, ℓ a (w i) = if a = i then 1 else 0 := by
    intro a i
    simp only [w, Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.proj_apply]
    have : Ψe.symm (ℓ a) = Pi.single a 1 := by
      rw [LinearEquiv.symm_apply_eq]; exact (hΨsingle a).symm
    rw [this]
    by_cases h : a = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  choose y hy using fun i => I.toCotangent_surjective (w i)
  have hzI : ∀ i, (y i : A) ∈ I := fun i => (y i).2
  have hdz : ∀ a i, dv a (y i : A) = if a = i then 1 else 0 := by
    intro a i; rw [← hℓ, hy, hw]
  have hImax : I ≤ maximalIdeal A := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [(RingHom.mem_ker).1 hx] at this
    exact not_isUnit_zero this
  have hnak : I ≤ Ideal.span (Set.range fun i => (y i : A)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian I) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      set s := ∑ a, algebraMap R A (dv a x) * (y a : A) with hs
      have hsI : s ∈ Ideal.span (Set.range fun i => (y i : A)) :=
        Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
      have hsI' : s ∈ I := Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hzI a)
      have hr : x - s ∈ I := I.sub_mem hx hsI'
      have hdr : ∀ b, dv b (x - s) = 0 := by
        intro b
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hdH, map_sub, hs, map_sum]
        simp only [← hdH, hsmul, hdz]
        simp
      have hcot : I.toCotangent ⟨x - s, hr⟩ = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
        obtain ⟨c, rfl⟩ := hΨsurj φ
        rw [hΨ]; simp [hdr]
      have hsq : x - s ∈ I ^ 2 := (I.toCotangent_eq_zero _).1 hcot
      have hxs : x = s + (x - s) := by ring
      rw [hxs]
      refine Submodule.add_mem_sup hsI ?_
      rw [pow_two] at hsq
      exact Submodule.smul_mono_left hImax hsq
  refine ⟨fun i => (y i : A), fun i => (RingHom.mem_ker).1 (y i).2, hdz, ?_⟩
  have hmapR : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [he] at this
    exact (mem_maximalIdeal r).1 hr this
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : algebraMap R A (e x) ∈ maximalIdeal A := by
        have := (maximalIdeal A).sub_mem hx (hImax (hdec x))
        simpa using this
      exact (mem_maximalIdeal _).1 h1 (hu.map _)
    have hxe : x = algebraMap R A (e x) + (x - algebraMap R A (e x)) := by ring
    rw [hxe]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hex) (hnak (hdec x))
  · refine sup_le hmapR ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hImax (hzI i)

end GlobalTheory.CoordsAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpand
section
namespace GlobalTheory.DeterminantProductExpansion

theorem det_mul_expand {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) := by
  let g : Fin i → Fin N → (Fin i → R) := fun a k => A a k • (fun j => B k j)
  have hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k) := by
    ext a j
    simp [g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Matrix.det (A * B) =
      (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k) := by
    rw [hrow]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [g]
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem main : ∀ {R : Type} [inst : CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R), Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) :=
  fun A B => det_mul_expand A B

end GlobalTheory.DeterminantProductExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpandAlt
section
namespace GlobalTheory.DeterminantExpansion

theorem det_mul_expand {V : Type} [inst : CommRing V] {m g : ℕ}
    (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    Matrix.det (M * C) =
      ∑ J : Fin m → Fin g, (∏ i : Fin m, M i (J i)) * Matrix.det (Matrix.submatrix C J id) := by
  classical
  have h : (M * C : Matrix (Fin m) (Fin m) V) = fun i => ∑ k : Fin g, M i k • C k := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  let f : (Fin m → Fin m → V) →ₘₗ[V] V := Matrix.detRowAlternating.toMultilinearMap
  have hf : ∀ A : Matrix (Fin m) (Fin m) V, Matrix.det A = f A := fun A => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, h, f.map_sum (fun i k => M i k • C k)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [f.map_smul_univ (fun i => M i (J i)) (fun i => C (J i)), hf, smul_eq_mul]
  rfl

end GlobalTheory.DeterminantExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
section
namespace GlobalTheory

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  intro K _ _ x hx
  classical
  have hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact Ideal.absNorm_mem _
  have hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hx b
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]
  have hprod := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ
    (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [map_natCast] at hα
  have hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x) := by
    rw [← hα]
    exact α.isIntegral_coe
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h]
    simpa using hint
  · rw [h]
    simpa using hint.neg

end GlobalTheory
end

