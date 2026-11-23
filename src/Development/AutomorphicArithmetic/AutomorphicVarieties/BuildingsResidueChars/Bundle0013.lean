module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardQuotientSpanUniformizerPow
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

private theorem card_step {O : Type} [CommRing O] [IsDomain O] (π : O) (h0 : π ≠ 0) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {π ^ (n + 1)}) =
      Nat.card (O ⧸ Ideal.span {π ^ n}) * Nat.card (O ⧸ Ideal.span {π}) := by
  have hrange : (AddMonoidHom.mulLeft (π ^ n)).range = (Ideal.span {π ^ n}).toAddSubgroup := by
    ext r
    simp [Ideal.mem_span_singleton', mul_comm]
  have hcomap : (Ideal.span {π ^ (n + 1)}).toAddSubgroup.comap (AddMonoidHom.mulLeft (π ^ n)) =
      (Ideal.span {π}).toAddSubgroup := by
    ext r
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    show π ^ (n + 1) ∣ π ^ n * r ↔ π ∣ r
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n h0)]
  have hle : (Ideal.span {π ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {π ^ n}).toAddSubgroup := by
    intro r hr
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hr ⊢
    exact (pow_dvd_pow π (Nat.le_succ n)).trans hr
  show (Ideal.span {π ^ (n + 1)}).toAddSubgroup.index =
    (Ideal.span {π ^ n}).toAddSubgroup.index * (Ideal.span {π}).toAddSubgroup.index
  rw [← AddSubgroup.relIndex_mul_index hle, ← hcomap, AddSubgroup.index_comap, hrange, mul_comm]

theorem UpperTheory.card_quotient_span_uniformizer_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → ∀ π : O, Irreducible π → ∀ n : ℕ, Nat.card (O ⧸ Ideal.span {π ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro O K _ _ _ _ _ Δ τ hL π hπ n
  have hres : Nat.card (IsLocalRing.ResidueField O) = Nat.card (O ⧸ Ideal.span {π}) := by
    rw [← hπ.maximalIdeal_eq]
    rfl
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    show (⊤ : Ideal O).toAddSubgroup.index = 1
    simp
  | succ k ih =>
    rw [card_step π hπ.ne_zero k, ih, hres, pow_succ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterTensorProductLeSupMapCenter
section
theorem UpperTheory.center_tensorProduct_le_sup_map_center :
    ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B], Subalgebra.center ℂ (TensorProduct ℂ A B) ≤ (Subalgebra.center ℂ A).map (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) ⊔ (Subalgebra.center ℂ B).map (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) := by
  intro A B _ _ _ _ z hz
  have hz' := Subalgebra.mem_center_iff.1 hz
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B).range :
        Set (TensorProduct ℂ A B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact hz' g
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B) w = z := hw
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := B)
      (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
    exact h
  have h2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[ℂ] TensorProduct ℂ (Subalgebra.center ℂ A) B).range :
        Set (TensorProduct ℂ (Subalgebra.center ℂ A) B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    apply hinj
    rw [map_mul, map_mul, hw']
    exact hz' _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h2
  obtain ⟨v, hv⟩ := h2
  have hv' : Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
      (Subalgebra.center ℂ B).val v = w := hv
  rw [← hw', ← hv']
  clear hv' hv hw' hw hz' hz
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ hx hy
  | tmul a b =>
    have e : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)
        (Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
          (Subalgebra.center ℂ B).val (a ⊗ₜ[ℂ] b)) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) (a : A) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) (b : B) := by
      simp
    rw [e]
    exact Algebra.mul_mem_sup ⟨a, a.2, rfl⟩ ⟨b, b.2, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFormWithPrescribedIwahoriValues
section
open IsLocalRing Matrix UpperTheory.V.Hi

private noncomputable def rhoT {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) :
    Representation Ω (A × B) (Matrix m n Ω) where
  toFun k :=
    { toFun := fun v => (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ)
      map_add' := fun v w => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by simp [smul_comm c] }
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' k k' := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mul_assoc, smul_smul, mul_comm]

private theorem rhoT_apply {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) (k : A × B)
    (v : Matrix m n Ω) :
    rhoT σ ξ ψ k v = (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ) := rfl

private theorem mulVec_row {Ω m n : Type} [Field Ω] [Fintype n] (M : Matrix n n Ω) (v : Matrix m n Ω) (i : m) :
    M *ᵥ v i = (v * Mᵀ) i := by
  ext k
  simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → X.Free τ θ U → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ v : Fin N → Fin m → Fin (W.d + 1) → Ω, ∃ F ∈ X.ClO W τ U c φ, ∀ n i k, X.unt m W F i (x n) k = v n i k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hφ hθ hfree N x hcov huniq v
  obtain ⟨ψ, hψ⟩ := UpperTheory.exists_iwahori_character_extending_torus_character Gp X.I Ωˣ c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)
    (fun t ht => by simp [hφ t ht])
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  set τ' := (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ with hτ'
  let j : U × X.I.Iw c →* Ga × Gp := (X.Ub.subtype.comp U.subtype).prodMap (X.I.Iw c).subtype
  have hj : ∀ k : U × X.I.Iw c, j k = (((k.1 : X.Ub) : Ga), (k.2 : Gp)) := fun _ => rfl
  obtain ⟨Φ, h1, h2, h3⟩ := UpperTheory.exists_automorphic_function_with_values_on_coset_reps Γ (Ga × Gp) (U × X.I.Iw c) Ω
    (Matrix (Fin m) (Fin (W.d + 1)) Ω) (Fin N) X.glob j
    (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ) x
    (fun g => by
      obtain ⟨γ, i, u, hu, b, hb, h⟩ := hcov g
      exact ⟨γ, i, (⟨u, hu⟩, ⟨b, hb⟩), h⟩)
    (fun i i' γ k h => huniq i i' γ k.1 k.1.2 k.2 k.2.2 h)
    (fun i γ k h => by
      obtain ⟨hc, hb, e⟩ := hfree (x i) γ k.1 k.1.2 k.2 (hle k.2.2) h
      refine LinearMap.ext fun w => ?_
      have hξ : (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) = (W.χ ⟨k.2, X.I.T_le hb⟩ : Ω) • (1 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) := by
        ext a b
        rw [W.central ⟨k.2, X.I.T_le hb⟩ hc a b]
        simp [Matrix.one_apply]
      have e' : algebraMap O Ω (θ ⟨k.2, hb⟩) • (τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) = 1 := by
        ext a b
        have := congrArg (algebraMap O Ω) (congrFun (congrFun e a) b)
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply] at this ⊢
        rw [apply_ite (algebraMap O Ω), map_one, map_zero] at this
        exact this
      rw [hθ] at e'
      rw [rhoT_apply, (hψ k.2).2.2 hb]
      show algebraMap O Ω (φ ⟨k.2, hb⟩) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) * w *
        (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = w
      rw [hξ, transpose_smul, transpose_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        ← Matrix.smul_mul, e', Matrix.one_mul])
    (fun n => Matrix.of (v n))
  have h2' : ∀ g (k : U × X.I.Iw c), (ψ k.2 : Ω) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) *
      Φ (g * j k) * (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = Φ g := by
    intro g k
    have := congrArg (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ k) (h2 g k)
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one] at this
    exact this
  have hp : ∀ b : X.I.Iw c, X.rpF Ω (W.d + 1) m b
      (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) =
      (((ψ b)⁻¹ : Ωˣ) : Ω) • (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) := by
    intro b
    funext i g
    show (Φ (g * j (1, b)) * (W.ξ (g.2 * b) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i =
      ((((ψ b)⁻¹ : Ωˣ) : Ω) • (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i
    rw [← h2' g (1, b)]
    simp [smul_smul, Matrix.mul_assoc]
  refine ⟨fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i, ⟨⟨fun i _ γ g => ?_, fun u hu => ?_⟩,
    fun b hb => ?_, fun b hb => ?_, fun t => ?_⟩, fun n i k => ?_⟩
  · show _ = _ *ᵥ (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i
    rw [mulVec_row]
    simp [h1, Matrix.mul_assoc]
  · funext i g k
    show ((τ' u : Matrix (Fin m) (Fin m) Ω) *
      (Φ (g * j (⟨u, hu⟩, 1)) * (W.ξ (g.2 * 1) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i k = (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i k
    rw [← h2' g (⟨u, hu⟩, 1)]
    simp [Matrix.mul_assoc]
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).1 hb] at this
    simpa using this
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_right hb
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).2.1 hb] at this
    simpa using this
  · have hb' : (t : Gp) ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_right t.2)
    have := hp ⟨t, hb'⟩
    rw [(hψ ⟨t, hb'⟩).2.2 t.2] at this
    exact this
  · rw [Frame.unt_apply]
    show (_ *ᵥ (Φ (x n) * (W.ξ (x n).2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) k = _
    rw [mulVec_row, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one, h3]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDiscriminantNormalForm
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_discriminant_normal_form :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range → ∀ (s : O) (ε : Oˣ), τ ^ 2 - 4 = algebraMap O K (ε * s ^ 2) → ∃ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x ∧ Ideal.span {s} = Ideal.span {π ^ n} := by
  intro O K _ _ _ _ _ Δ τ hL hτ hτr s ε hs
  haveI := hL.frac
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨t, rfl⟩ := hτr
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs]
    simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have h2K : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := by
    have h1 : (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := hL.two.val_inv_mul
    have h3 := congrArg (algebraMap O K) h1
    rw [map_mul, map_one, map_ofNat] at h3
    exact h3
  have two_ne : (2 : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2K
    exact zero_ne_one h2K
  have hI : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) = 2⁻¹ := by
    field_simp
    exact h2K
  have hP : algebraMap O K (ϖ ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ inj]
    exact pow_ne_zero _ hϖ.ne_zero
  have hrel : algebraMap O K t ^ 2 - 4
      = algebraMap O K ε * algebraMap O K μ ^ 2 * algebraMap O K (ϖ ^ n) ^ 2 := by
    rw [hs, hμ]
    simp only [map_mul, map_pow]
    ring
  set T := algebraMap O K t with hT
  set P := algebraMap O K (ϖ ^ n) with hPdef
  let x : Etau K T := ⟨-T / 2 / P, 1 / P⟩
  have hxre : x.re = -T / 2 / P := rfl
  have hxim : x.im = 1 / P := rfl
  have htr : trace x = 0 := by
    rw [trace_def, hxre, hxim]
    field_simp
    ring
  refine ⟨ϖ, n, ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹, t * (((hL.two.unit)⁻¹ : Oˣ) : O), x,
    ⟨hϖ, ⟨?_, ?_, ?_⟩, htr, ?_, ?_⟩, ?_⟩
  · rw [htr]
    exact ⟨0, map_zero _⟩
  · refine ⟨-((ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹ : Oˣ) : O), ?_⟩
    rw [norm_def, hxre, hxim]
    simp only [map_neg, Units.val_mul, map_mul, hI]
    field_simp
    linear_combination hrel
  · refine ⟨ε * μ * μ, ?_⟩
    rw [hxim, hrel]
    simp only [Units.val_mul, map_mul]
    field_simp
  · apply QuadraticAlgebra.ext
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, hxre, hxim]
      simp only [Units.val_mul, map_mul, hI]
      field_simp
      linear_combination hrel
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, hxre, hxim]
      field_simp
      ring
  · apply QuadraticAlgebra.ext
    · show (0 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).re + (yy ϖ n x).re
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re]
      simp only [yy, QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, hI, hxre]
      rw [← hT, ← hPdef]
      field_simp
      ring
    · show (1 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).im + (yy ϖ n x).im
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im]
      simp only [yy, QuadraticAlgebra.im_smul, smul_eq_mul, hxim]
      rw [← hPdef]
      field_simp
      ring
  · rw [Ideal.span_singleton_eq_span_singleton, hμ]
    exact associated_unit_mul_left _ _ μ.isUnit
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsUnitSmulOrderOfMemGs
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_unit_smul_order_of_mem_gs :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (t : Kˣ) (S : Set (Etau K τ)), S ∈ PS.Gs O τ t 1 → ∃ (m : ℕ) (r : Kˣ) (u : (Etau K τ)ˣ), u ∈ Gu O τ ∧ S = PS.ml (PS.sc τ r * u) (Ord O (yy π m x)) := by
  intro O K _ _ _ _ _ Δ τ hL hτ π n e h x hC t S hS
  obtain ⟨hfix, c, hc, hgen⟩ := hS
  rw [one_mul] at hgen
  obtain ⟨r, u, hu1, hu2, hcu⟩ := hC.gen.cint hL hc
  obtain ⟨s0, hs0⟩ := hfix.fg
  subst hs0
  set N : Submodule O (Etau K τ) := Submodule.span O (s0 : Set (Etau K τ)) with hN
  have hcS : (c : Etau K τ) ∈ N := hgen.1
  have hint : ∀ w ∈ N, ∃ a b : O, ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w
      = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x :=
    fun w hw => (hC.gen.int_iff hL _).1 (hgen.2 w hw)
  let B : Ideal O :=
    { carrier := {b | ∃ a : O,
        (c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x) ∈ N}
      add_mem' := by
        rintro b1 b2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (a1 + a2) + algebraMap O (Etau K τ) (b1 + b2) * x)
            = (c : Etau K τ) * (algebraMap O (Etau K τ) a1 + algebraMap O (Etau K τ) b1 * x)
              + (c : Etau K τ) * (algebraMap O (Etau K τ) a2 + algebraMap O (Etau K τ) b2 * x) := by
          simp only [map_add (f := _)]
          ring
        rw [key]
        exact N.add_mem h1 h2
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp only [map_zero, zero_mul, add_zero, mul_zero]
        exact N.zero_mem
      smul_mem' := by
        rintro k b ⟨a, hab⟩
        refine ⟨k * a, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (k * a) + algebraMap O (Etau K τ) (k • b) * x)
            = k • ((c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x)) := by
          rw [smul_eq_mul, Algebra.smul_def, map_mul, map_mul]
          ring
        rw [key]
        exact N.smul_mem k hab }
  have hB : B ≠ ⊥ := by
    have hωc : ω * (c : Etau K τ) ∈ N := hfix.stab _ hcS
    obtain ⟨a, b, hab⟩ := hint _ hωc
    have hω : (ω : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x := by
      rw [← hab, mul_left_comm, Units.inv_mul, mul_one]
    have hb : b ∈ B := ⟨a, by rw [← hω, mul_comm]; exact hωc⟩
    intro hbot
    rw [hbot] at hb
    have hb0 : b = 0 := (Submodule.mem_bot O).1 hb
    rw [hb0, map_zero, zero_mul, add_zero] at hω
    have him := congrArg QuadraticAlgebra.im hω
    rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im] at him
    exact one_ne_zero him
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hB hC.irr
  have hyy : yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
    rw [yy, Algebra.smul_def, algebraMap_etau (O := O) (π ^ m)]
  have hpm : π ^ m ∈ B := by
    rw [hm]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := hpm
  refine ⟨m, r, u, ⟨hu1, hu2⟩, ?_⟩
  rw [← hcu]
  ext w
  rw [PS.mem_ml]
  show w ∈ N ↔ _ ∈ Submodule.span O {1, yy π m x}
  rw [Submodule.mem_span_pair]
  constructor
  · intro hw
    obtain ⟨a, b, hab⟩ := hint w hw
    have hbB : b ∈ B := ⟨a, by rw [← hab, ← mul_assoc, Units.mul_inv, one_mul]; exact hw⟩
    rw [hm, Ideal.mem_span_singleton'] at hbB
    obtain ⟨k, rfl⟩ := hbB
    refine ⟨a, k, ?_⟩
    rw [hab, hyy, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  · rintro ⟨a, k, hak⟩
    have hw : w = (c : Etau K τ) * (a • 1 + k • yy π m x) := by
      rw [hak, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hw, mul_add, hyy]
    apply N.add_mem
    · rw [mul_smul_comm, mul_one]
      exact N.smul_mem a hcS
    · rw [mul_smul_comm]
      apply N.smul_mem
      have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (π ^ m) * x)
          = (c : Etau K τ) * (algebraMap O (Etau K τ) a0 + algebraMap O (Etau K τ) (π ^ m) * x)
            - a0 • (c : Etau K τ) := by
        rw [Algebra.smul_def]
        ring
      rw [key]
      exact N.sub_mem ha0 (N.smul_mem a0 hcS)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd
section
open GroundTheory.Automorphic.HarishChandra in
private noncomputable def UpperTheory.V.Af.CuspFin.vermaRep {n : ℕ} (lam : Fin n → ℂ) :
    U n →ₐ[ℂ] Module.End ℂ (U n ⧸ vermaIdeal lam) where
  toFun x := (vermaIdeal lam).mapQ (vermaIdeal lam) (LinearMap.mulLeft ℂ x)
    (fun _ hy => mul_mem_vermaIdeal lam x hy)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (a * b * y) : U n ⧸ vermaIdeal lam) = Submodule.Quotient.mk (a * (b * y))
    rw [mul_assoc]
  map_zero' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_add' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk ((a + b) * y) : U n ⧸ vermaIdeal lam) =
      Submodule.Quotient.mk (a * y) + Submodule.Quotient.mk (b * y)
    rw [add_mul, Submodule.Quotient.mk_add]
  commutes' r := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (algebraMap ℂ (U n) r * y) : U n ⧸ vermaIdeal lam) =
      r • Submodule.Quotient.mk y
    rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.vermaRep_one {n : ℕ} (lam : Fin n → ℂ) (x : U n) :
    UpperTheory.V.Af.CuspFin.vermaRep lam x (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x := by
  change Submodule.Quotient.mk (x * 1) = _
  rw [mul_one]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.one_notMem_vermaIdeal {n : ℕ} (lam : Fin n → ℂ) :
    (1 : U n) ∉ vermaIdeal lam := by
  intro h
  have h0 := vermaCoord_vermaIdeal lam h
  have hnu : ¬ HasUpper (0 : Fin n × Fin n →₀ ℕ) := by
    rintro ⟨b, -, hne⟩
    exact hne rfl
  have hd : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [← canon_zero, vermaCoord_canon_of_not lam hnu, hd, Finsupp.single_eq_zero] at h0
  simp at h0

open GroundTheory.Automorphic.HarishChandra UpperTheory.V.Af.CuspFin in
theorem UpperTheory.harishChandraProj_quantumDet_eq_prod :
    ∀ (n : ℕ) (u : ℂ), GroundTheory.Automorphic.HarishChandra.hcProjLin (Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) = ∏ k : Fin n, (MvPolynomial.C (u - (k : ℂ)) + MvPolynomial.X k) := by
  intro n u
  refine MvPolynomial.funext fun lam => ?_
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := fun a b c d => e_mul_sub_mul (a, b) (c, d)
  have hgl' : Formalism.REAL.GlRel (fun i j : Fin n => vermaRep lam (e (i, j))) := fun a b c d => by
    have h := congrArg (vermaRep lam) (hgl a b c d)
    simp only [map_sub, map_mul, apply_ite (vermaRep lam), map_zero] at h
    exact h
  have hup : ∀ a, IsUpper a → vermaRep lam (e a) (Submodule.Quotient.mk 1) = 0 := fun a ha => by
    rw [vermaRep_one, Submodule.Quotient.mk_eq_zero]
    exact nPlusU_le_vermaIdeal lam (Submodule.subset_span ⟨1, a, ha, one_mul _⟩)
  have hH : ∀ k, vermaRep lam (e (k, k)) (Submodule.Quotient.mk 1) =
      lam k • (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) := fun k => by
    rw [vermaRep_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← Algebra.algebraMap_eq_smul_one]
    simpa using mul_e_sub_mem_vermaIdeal lam 1 k
  have h1 := rep_apply_of_highestWeight (vermaRep lam) lam hup hH
    (z := Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u)
    (fun k => (Formalism.REAL.qDetCentral _ n _ hgl u k k).symm)
  have h2 := Formalism.REAL.qDetHW _ n _ lam (Submodule.Quotient.mk 1) hgl'
    ⟨hH, fun a b hab => hup (a, b) hab⟩ u
  rw [map_qdet, h2] at h1
  have hv : (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) ≠ 0 := fun h =>
    one_notMem_vermaIdeal lam ((Submodule.Quotient.mk_eq_zero _).1 h)
  rw [← smul_left_injective ℂ hv h1]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerOrderLevelZero
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.relIndex_stabilizer_order_level_zero :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (Hu O (yy π 0 x)).relIndex (Gu O τ) = 1 := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  have hy : yy π 0 x = x := by simp [yy]
  have hO : PK.Ord O (yy π 0 x) = (PK.Mx O τ : Set (Etau K τ)) := by
    rw [hy, Gen1.span L hc.gen]
    rfl
  rw [Subgroup.relIndex_eq_one]
  intro u hu
  show PS.ml u (PK.Ord O (yy π 0 x)) = PK.Ord O (yy π 0 x)
  rw [hO]
  exact ml_Mx hu.1 hu.2
end

