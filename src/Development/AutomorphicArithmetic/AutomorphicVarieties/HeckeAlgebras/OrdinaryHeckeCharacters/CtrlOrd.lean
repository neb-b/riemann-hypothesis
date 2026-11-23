module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpOperatorMapsLatticeOfControlValues
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveOnSpanOfIntegralFreeSubmodule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0010

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ctrlOrd_per {A B M : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [Module B M]
    (V : Submodule A M) (T : Module.End B M) (hT : ∀ v ∈ V, T v ∈ V) :
    (∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V) ∧ ∀ (n j : ℕ) (v : M), (T ^ n) v - v ∈ V → (T ^ (n * j)) v - v ∈ V := by
  have h1 : ∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (hT v hv)
  refine ⟨h1, fun n j v hv => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hx : (T ^ (n * (j + 1))) v - v = (T ^ (n * j)) ((T ^ n) v - v) + ((T ^ (n * j)) v - v) := by
      rw [Nat.mul_succ, pow_add, mul_apply_eq_comp, map_sub]
      abel
    rw [hx]
    exact V.add_mem (h1 _ _ hv) ih

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O] [IsCNL O]
  [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}

private theorem ctrlOrd_val (k : ℕ) (f : X.Fn O m) : f ∈ X.valIn O m k ↔ ∀ g i, f g i ∈ maximalIdeal O ^ k := by
  unfold Frame.valIn
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

private theorem ctrlOrd_valU (k : ℕ) (f : X.Fn O m) (hf : f ∈ X.valIn O m k) : X.U O m X.I.z f ∈ X.valIn O m k := by
  unfold Frame.U Iwa.uOp Frame.rp
  refine finsum_induction (fun T : Module.End O (X.Fn O m) => T f ∈ X.valIn O m k) (by simp)
    (fun a b ha hb => by simpa using Submodule.add_mem _ ha hb) (fun q => ?_)
  rw [ctrlOrd_val] at hf ⊢
  intro g i
  simp [UpperTheory.V.Hi.rtr]
  exact hf _ _

private theorem ctrlOrd_map (hinj : Function.Injective (algebraMap O Ω)) (k : ℕ) (f : X.Fn O m)
    (h : ∀ g i, X.mapFn (B := Ω) f g i ∈ mIm O Ω k) : f ∈ X.valIn O m k := by
  rw [ctrlOrd_val]
  intro g i
  obtain ⟨x, hx, hxe⟩ := mem_mIm.1 (h g i)
  unfold Frame.mapFn at hxe
  simp at hxe
  rw [← hinj hxe]
  exact hx

private theorem ctrlOrd_nat (F : Fin m → X.Fn Ω (W.d + 1)) (f : X.Fn O m) (h : X.mapFn (B := Ω) f = X.ctrl m W F) (n : ℕ) :
    X.mapFn (B := Ω) ((X.U O m X.I.z ^ n) f) = X.ctrl m W ((X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F) := by
  have hU : ∀ g : X.Fn O m, X.mapFn (B := Ω) (X.U O m X.I.z g) = X.U Ω m X.I.z (X.mapFn (B := Ω) g) := by
    intro g
    unfold Frame.U
    refine uOpNat Gp X.I O (X.Fn O m) (X.rp O m) Ω (X.Fn Ω m) (X.rp Ω m)
      (X.mapFn (B := Ω)).toAddMonoidHom X.I.z X.I.z_mem g ?_
    intro u hu
    ext x i
    unfold Frame.rp Frame.mapFn
    simp [UpperTheory.V.Hi.rtr]
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, hU, ih,
      (ctrlEq Γ Ga Gp X O Ω W m 1).2.1]

private theorem ctrlOrd_stab (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)) (hF : F ∈ X.Lat m W Λ) :
    X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W Λ := by
  refine UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m Λ Λ (fun a _ w hw => Λ.smul_mem a hw) F hF ?_
  intro g i
  have h := hF i g 0
  rw [Frame.unt_apply] at h
  unfold Frame.ctrl
  exact h

private theorem ctrlOrd_inj (hinj : Function.Injective (algebraMap O Ω)) (F : Fin m → X.Fn Ω (W.d + 1))
    (hF : F ∈ X.Lat m W (mIm O Ω 0))
    (hp : ∀ k, ∃ n : ℕ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ (n + 1)) F - F ∈ X.Lat m W (mIm O Ω k))
    (h0 : X.ctrl m W F = 0) : F = 0 := by
  have hKrull : ⨅ k : ℕ, maximalIdeal O ^ k = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top
  have hstep : ∀ k, F ∈ X.Lat m W (mIm O Ω k) → F ∈ X.Lat m W (mIm O Ω (k + 1)) := by
    intro k hk
    obtain ⟨n, hn⟩ := hp (k + 1)
    have hsm : ∀ a ∈ maximalIdeal O, ∀ w ∈ mIm O Ω k, a • w ∈ mIm O Ω (k + 1) := by
      intro a ha w hw
      obtain ⟨x, hx, rfl⟩ := mem_mIm.1 hw
      refine mem_mIm.2 ⟨a * x, ?_, by rw [Algebra.smul_def, map_mul]⟩
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha hx
    have h1 : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W (mIm O Ω (k + 1)) := by
      refine UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m _ _ hsm F hk ?_
      intro g i
      rw [h0]
      exact (mIm O Ω (k + 1)).zero_mem
    have h2 := (ctrlOrd_per (X.Lat m W (mIm O Ω (k + 1))) (X.UF m W ⟨X.I.z, X.I.z_mem⟩)
      (fun v hv => ctrlOrd_stab X W _ v hv)).1 n _ h1
    rw [← mul_apply_eq_comp, ← pow_succ] at h2
    have h3 := Submodule.sub_mem _ h2 hn
    simpa using h3
  have hall : ∀ k, F ∈ X.Lat m W (mIm O Ω k) := by
    intro k
    induction k with
    | zero => exact hF
    | succ k ih => exact hstep k ih
  funext i g
  have hu : X.unt m W F i g = 0 := by
    funext j
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hall 0 i g j)
    have hxm : x ∈ ⨅ k : ℕ, maximalIdeal O ^ k := by
      rw [Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy, hye⟩ := mem_mIm.1 (hall k i g j)
      rw [← hinj (hye.trans hx.symm)]
      exact hy
    rw [hKrull, Ideal.mem_bot] at hxm
    rw [← hx, hxm, map_zero]
    rfl
  rw [Frame.unt_apply] at hu
  have hv := congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu
  simpa [Matrix.mulVec_mulVec] using hv

private theorem ctrlOrd_prescribed_values (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ)
    (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ)
    (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1)
    (hθ : ∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩)
    (hfree : X.Free τ θ U) (N : ℕ) (x : Fin N → Ga × Gp)
    (hcov : ∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b))
    (huniq : ∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j)
    (v : Fin N → Fin m → Fin (W.d + 1) → Ω) :
    ∃ F ∈ X.ClO W τ U c φ, ∀ n i k, X.unt m W F i (x n) k = v n i k := by
  let rhoT {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
      [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) :
      Representation Ω (A × B) (Matrix m n Ω) :=
    { toFun := fun k =>
        { toFun := fun v => (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ)
          map_add' := fun v w => by simp [Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun c v => by simp [smul_comm c] }
      map_one' := by
        refine LinearMap.ext fun v => ?_
        simp
      map_mul' := by
        intro k k'
        refine LinearMap.ext fun v => ?_
        simp [Matrix.mul_assoc, smul_smul, mul_comm] }
  have rhoT_apply {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
      [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) (k : A × B)
      (v : Matrix m n Ω) :
      rhoT σ ξ ψ k v = (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ) := rfl
  have mulVec_row {Ω m n : Type} [Field Ω] [Fintype n] (M : Matrix n n Ω) (v : Matrix m n Ω) (i : m) :
      M *ᵥ v i = (v * Mᵀ) i := by
    ext k
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
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

private theorem ctrlOrd_classical (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ)
    (U : Subgroup X.Ub) :
    (∀ (c : ℕ), W.c0 ≤ c → ∀ (N : ℕ) (x : Fin N → Ga × Gp),
      (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) →
      ∀ F ∈ X.ClO W τ U c φ, ∀ Λ : Submodule O Ω,
        (∀ n i k, X.unt m W F i (x n) k ∈ Λ) → F ∈ X.Lat m W Λ) ∧
    (∀ (c : ℕ) (θ : X.I.T →* Oˣ), Function.Injective (algebraMap O Ω) →
      (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) →
      ∀ F ∈ X.ClO W τ U c φ, F ∈ X.Lat m W (mIm O Ω 0) →
        ∃ f ∈ X.Sp τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F ∧
          ∀ k c' : ℕ, c ≤ c' →
            (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k,
              W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) →
            ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k) ∧
    (∀ (c : ℕ), (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ) ∧
      ∀ e n : ℕ, e ≤ n → ∀ F ∈ X.ClO W τ U (c + e) φ,
        (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F ∈ X.ClO W τ U c φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc N x hx F hF Λ hΛ
    have lattice_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
        (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
        (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
      rw [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem L fun j _ => ?_
      obtain ⟨r, hr⟩ := hM k j
      rw [← hr, ← Algebra.smul_def]
      exact L.smul_mem r (hv j)
    simp only [Frame.ClO, Frame.Cl, Submodule.mem_inf] at hF
    obtain ⟨⟨hA, hU⟩, hE⟩ := hF
    obtain ⟨hN, hNm, hT⟩ := hE
    have hA' : ∀ i γ g, F i (X.glob γ * g) =
        ((W.ξ (X.glob γ).2 : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g :=
      fun i γ g => (Submodule.mem_pi.mp hA i (Set.mem_univ i)) γ g
    have hU' : ∀ u ∈ U, ∀ i g k,
        (((((GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u : GL _ Ω) : Matrix (Fin m) (Fin m) Ω) *ᵥ
          (fun j => F j (g * ((u : Ga), 1)) k)) i = F i g k :=
      fun u hu i g k => congrFun (congrFun (congrFun (hU u hu) i) g) k
    have key : ∀ (h : Ga × Gp) (b : Gp) (s : O),
        (∀ i j, ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) i j ∈
          (algebraMap O Ω).range) →
        (∀ i, F i (h * (1, b)) = algebraMap O Ω s • F i h) →
        (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
      intro h b s hMb hFb hG i k
      have e : X.unt m W F i (h * (1, b)) =
          ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ
            (algebraMap O Ω s • X.unt m W F i h) := by
        simp only [Frame.unt_apply, hFb i, Prod.snd_mul, map_mul, map_inv, _root_.mul_inv_rev,
          GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
      rw [e]
      refine lattice_mulVec Λ _ hMb _ (fun j => ?_) k
      rw [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
      exact Λ.smul_mem s (hG i j)
    have stepN : ∀ h, ∀ b ∈ X.I.N, (∀ i k, X.unt m W F i h k ∈ Λ) →
        ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
      intro h b hb hG
      refine key h b 1 (W.int_N _ (X.I.N.inv_mem hb)) (fun i => ?_) hG
      rw [map_one, one_smul]
      exact congrFun (congrFun (hN b hb) i) h
    have stepM : ∀ h, ∀ b ∈ X.I.Nm c, (∀ i k, X.unt m W F i h k ∈ Λ) →
        ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
      intro h b hb hG
      refine key h b 1 (W.int_Nm _ (X.I.Nm_anti hc ((X.I.Nm c).inv_mem hb))) (fun i => ?_) hG
      rw [map_one, one_smul]
      exact congrFun (congrFun (hNm b hb) i) h
    have stepT : ∀ h, ∀ b ∈ X.I.T, (∀ i k, X.unt m W F i h k ∈ Λ) →
        ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
      intro h b hb hG
      refine key h b ((φ ⟨b, hb⟩)⁻¹ : Oˣ) (W.integral_torusCharacter _ (X.I.T.inv_mem hb)) (fun i => ?_) hG
      have := congrFun (congrFun (hT ⟨b, hb⟩) i) h
      refine this.trans ?_
      simp
    have stepU : ∀ h, ∀ u ∈ U, (∀ i k, X.unt m W F i h k ∈ Λ) →
        ∀ i k, X.unt m W F i (h * ((u : Ga), 1)) k ∈ Λ := by
      intro h u hu hG i k
      have hv : ∀ i, F i (h * ((u : Ga), 1)) =
          fun l => ∑ j, algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) i j) * F j h l := by
        intro i
        funext l
        have := hU' u⁻¹ (U.inv_mem hu) i (h * ((u : Ga), 1)) l
        rw [← this]
        have hh : h * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = h := by
          ext <;> simp
        simp only [Matrix.mulVec, dotProduct, hh]
        rfl
      have e : X.unt m W F i (h * ((u : Ga), 1)) k =
          ((Matrix.of fun a b => algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) a b)) *ᵥ
            fun j => X.unt m W F j h k) i := by
        simp only [Frame.unt_apply, Prod.snd_mul, mul_one, hv, Matrix.mulVec, dotProduct, Finset.mul_sum,
          Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring
      rw [e]
      exact lattice_mulVec Λ _ (fun a b => ⟨_, rfl⟩) _ (fun j => hG j k) i
    have stepG : ∀ γ h, (∀ i k, X.unt m W F i h k ∈ Λ) →
        ∀ i k, X.unt m W F i (X.glob γ * h) k ∈ Λ := by
      intro γ h hG i k
      have e : X.unt m W F i (X.glob γ * h) = X.unt m W F i h := by
        rw [Frame.unt_apply, Frame.unt_apply, hA' i γ h]
        simp [Prod.snd_mul, Matrix.mulVec_mulVec, _root_.mul_inv_rev, mul_assoc]
      rw [e]
      exact hG i k
    show ∀ i g k, X.unt m W F i g k ∈ Λ
    intro i g k
    obtain ⟨γ, n, u, hu, b, hb, rfl⟩ := hx g
    obtain ⟨y1, hy1, t, ht, y2, hy2, rfl⟩ := ((iwMem Gp X.I c b).1).1 hb
    have eq : X.glob γ * x n * ((u : Ga), y1 * t * y2) =
        X.glob γ * (x n * ((u : Ga), 1) * (1, y1) * (1, t) * (1, y2)) := by
      ext <;> simp [mul_assoc]
    rw [eq]
    exact stepG γ _ (stepM _ y2 hy2 (stepT _ t ht (stepN _ y1 hy1
      (stepU _ u hu (fun i k => hΛ n i k))))) i k
  · intro c θ hinj hθ F hF hL
    have translate_trace {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O]
        [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (F : Fin m → X.Fn Ω (W.d + 1))
        (g : Ga × Gp) (b : Gp) (i : Fin m) :
        X.ctrl m W F (g * (1, b)) i =
          ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ (X.rpF Ω (W.d + 1) m b F i g)) j := by
      rw [Frame.ctrl_apply, Frame.unt_apply]
      show _ = ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ F i (g * (1, b))) j
      rw [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, map_inv]
      rfl
    have hL' : ∀ i g k, X.unt m W F i g k ∈ mIm O Ω 0 := fun i g k => hL i g k
    have hv : ∀ i g k, ∃ a : O, algebraMap O Ω a = X.unt m W F i g k := by
      intro i g k
      obtain ⟨a, -, ha⟩ := mem_mIm.1 (hL' i g k)
      exact ⟨a, ha⟩
    choose v hv0 using hv
    have hu : ∀ i g j, ((W.ξ g.2)⁻¹.val *ᵥ F i g) j = algebraMap O Ω (v i g j) := by
      intro i g j
      rw [hv0, Frame.unt_apply]
    obtain ⟨f, hf⟩ : ∃ f : X.Fn O m, ∀ g i, algebraMap O Ω (f g i) = X.ctrl m W F g i :=
      ⟨fun g i => v i g 0, fun g i => by rw [Frame.ctrl_apply, hv0]⟩
    have hf0 : ∀ g i, algebraMap O Ω (f g i) = algebraMap O Ω (v i g 0) := by
      intro g i
      rw [hf, Frame.ctrl_apply, hv0]
    have hs : ∀ (b : Gp) (a : Ω), X.rpF Ω (W.d + 1) m b F = a • F → ∀ g i,
        algebraMap O Ω (f (g * (1, b)) i) = a * ∑ j, (W.ξ b⁻¹).val 0 j * algebraMap O Ω (v i g j) := by
      intro b a hb g i
      rw [hf, translate_trace, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul, hu]
      ring
    have hE := hF.2
    have hUF := hF.1.2
    have hA : ∀ i (γ : Γ) (g : Ga × Gp), F i (X.glob γ * g) = (W.ξ (X.glob γ).2).val *ᵥ F i g :=
      fun i γ g => hF.1.1 i (Set.mem_univ i) γ g
    have key : ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
      intro k c' hc hξ y hy g _ i _
      have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hc hy
      choose a ha hae using fun j => hξ y⁻¹ (inv_mem hy) 0 j
      have h1 : f (g * (1, y)) i - f g i = ∑ j, a j * v i g j := by
        apply hinj
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, hs y 1 (by rw [one_smul]; exact hE.2.1 y hyc) g i, hf0, one_mul, map_sum]
        simp only [hae, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_mul]
        ring
      show f (g * (1, y)) i - f g i ∈ maximalIdeal O ^ k
      rw [h1]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (ha j)
    refine ⟨f, ?_, ?_, key⟩
    · refine Submodule.mem_inf.2 ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro γ g
        funext i
        apply hinj
        rw [hf, hf, Frame.ctrl_apply, Frame.ctrl_apply, Frame.unt_apply, Frame.unt_apply, hA, Prod.snd_mul, map_mul,
          Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      · intro u hu'
        funext g i
        apply hinj
        show algebraMap O Ω (f (g * (1, u)) i) = algebraMap O Ω (f g i)
        rw [hs u 1 (by rw [one_smul]; exact hE.1 u hu') g i, hf0, one_mul]
        simp only [W.row_N _ (X.I.N_le (inv_mem hu')), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      · intro t
        funext g i
        apply hinj
        show algebraMap O Ω (f (g * (1, (t : Gp))) i) = algebraMap O Ω (((θ t)⁻¹ : Oˣ) * f g i)
        rw [hs (t : Gp) _ (hE.2.2 t) g i, map_mul, hf0]
        have hr : ∀ j, (W.ξ (t : Gp)⁻¹).val 0 j = if j = 0 then (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) else 0 :=
          fun j => W.torusAction ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ j
        have hχ : (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) = (W.χ ⟨t, X.I.T_le t.2⟩ : Ω)⁻¹ := by
          rw [← Units.val_inv_eq_inv_val, ← map_inv]
          rfl
        have hθ' : algebraMap O Ω (((θ t)⁻¹ : Oˣ) : O) = (algebraMap O Ω (θ t))⁻¹ := map_units_inv (algebraMap O Ω) (θ t)
        simp only [hr, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [hχ, hθ', hθ t]
        simp only [MonoidHom.comp_apply, Units.coe_map, Units.val_inv_eq_inv_val]
        rw [mul_inv, mul_assoc]
        rfl
      · intro k
        obtain ⟨c1, hc1⟩ := W.cont_Nm k
        refine ⟨max c c1, fun y hy g i => ?_⟩
        have h := key k (max c c1) (le_max_left _ _)
          (fun y hy => hc1 y (X.I.Nm_anti (le_max_right _ _) hy)) y hy g (Set.mem_univ _) i (Set.mem_univ _)
        exact h
      · intro u hu'
        funext g i
        apply hinj
        rw [Frame.ra_apply, hf, ← hUF u hu',
          (ctrlEq Γ Ga Gp X O Ω W m ((GeneralLinearGroup.map (algebraMap O Ω)).comp τ)).1 u F, Frame.ra_apply]
        simp [Matrix.mulVec, dotProduct, hf]
    · funext g i
      exact hf g i
  · intro c hφ
    have lower_step {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
        [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
        (τ : X.Ub →* GL (Fin m) Ω) (φ : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ)
        (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) :
        ∀ F ∈ X.Cl τ W.ξ U (c + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Cl τ W.ξ U c φ := by
      classical
      intro F hF
      obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem
      have hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F =
          (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F := by
        rw [← (h2 s hs hu).2 F hF.2.1]; rfl
      refine ⟨?_, ?_⟩
      · rw [hsum]
        refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
        · change F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))
          rw [mul_assoc]
          exact hF.1.1 i trivial γ _
        · rw [(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]
      · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)
    have mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ := by
      intro c' hc F hF
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hF
      refine Submodule.mem_inf.2 ⟨h1, ?_⟩
      exact ⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩
    have step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ,
        X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ := by
      intro e F hF
      exact lower_step X W _ _ U (c + e)
        (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF
    have down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ,
        (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ := by
      intro e
      induction e with
      | zero =>
        intro F hF
        simpa using hF
      | succ e ih =>
        intro F hF
        rw [pow_succ, mul_apply_eq_comp]
        exact ih _ (step e F hF)
    have stay : ∀ F ∈ X.ClO W τ U c φ,
        X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ :=
      fun F hF => step 0 F (mono _ (Nat.le_succ c) hF)
    refine ⟨stay, ?_⟩
    intro e n hen F hF
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hen
    rw [add_comm e k, pow_add, mul_apply_eq_comp]
    exact (ctrlOrd_per _ _ stay).1 k _ (down e F hF)

private theorem ctrlOrd_approx (hinj : Function.Injective (algebraMap O Ω)) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ)
    (c : ℕ) (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1)
    (hθ : ∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩)
    (U : Subgroup X.Ub) (hU : X.FinLevel U) (hF : X.Free τ θ U) (f : X.Fn O m) (hf : f ∈ X.Ord τ θ U) :
    ∃ G ∈ X.ClO W τ U c φ, G ∈ X.Lat m W (mIm O Ω 0) ∧ ∃ h : X.Fn O m, X.mapFn (B := Ω) h = X.ctrl m W G ∧
      h - f ∈ X.valIn O m 1 := by
  obtain ⟨lattice, lift, stable⟩ := ctrlOrd_classical X W τ φ U
  obtain ⟨hSp, hper⟩ := (mem_ord_iff X τ θ U f).1 hf
  have hA := (Submodule.mem_inf.1 hSp).1
  unfold Frame.Amb at hA
  obtain ⟨c2, hc2⟩ := hA.2.2.2 1
  obtain ⟨c1, hc1⟩ := W.cont_Nm 1
  obtain ⟨n, hn⟩ := hper 1
  set e := c1 + c2 with he
  set c' := c + e with hc'
  set M := (n + 1) * (e + 1) with hM
  have heM : e ≤ M := by
    rw [hM]
    nlinarith
  have hcc' : c ≤ c' := Nat.le_add_right c e
  have hc1' : c1 ≤ c' := by omega
  have hc2' : c2 ≤ c' := by omega
  have hφ' : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → φ t = 1 := fun t ht => hφ t (X.I.Tc_anti hcc' ht)
  obtain ⟨N, x, hcov, hdis⟩ := UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c'
  obtain ⟨F', hF', hval⟩ := ctrlOrd_prescribed_values X W τ φ U c' θ hφ' hθ hF N x hcov hdis
    (fun n i k => if k = 0 then algebraMap O Ω (f (x n) i) else 0)
  have hLat' : F' ∈ X.Lat m W (mIm O Ω 0) := by
    refine lattice c' (le_trans hc hcc') N x hcov F' hF' _ ?_
    intro n i k
    rw [hval]
    split_ifs
    · exact mem_mIm.2 ⟨f (x n) i, by simp, rfl⟩
    · exact (mIm O Ω 0).zero_mem
  obtain ⟨h', hh'Sp, hh'map, hcong⟩ := lift c' θ hinj hθ F' hF' hLat'
  have hrp : ∀ (y : Gp) (g : X.Fn O m) (a : Ga × Gp) (i : Fin m), X.rp O m y g a i = g (a * (1, y)) i := by
    intro y g a i
    unfold Frame.rp
    simp [UpperTheory.V.Hi.rtr]
  have hdiff : h' - f ∈ X.valIn O m 1 := by
    refine UpperTheory.mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X O m τ θ U 1 c' N x hcov (h' - f) (Submodule.sub_mem _ hh'Sp hSp) ?_ ?_
    · intro y hy
      have h1 := hcong 1 c' le_rfl (fun y' hy' => hc1 y' (X.I.Nm_anti hc1' hy')) y hy
      have h2 : X.rp O m y f - f ∈ X.valIn O m 1 := by
        rw [ctrlOrd_val]
        intro a i
        simp only [Pi.sub_apply, hrp]
        exact hc2 y (X.I.Nm_anti hc2' hy) a i
      have h3 := Submodule.sub_mem _ h1 h2
      rw [map_sub]
      convert h3 using 1
      abel
    · intro i j
      have hv := congrFun (congrFun hh'map (x i)) j
      have hc : X.ctrl m W F' (x i) j = algebraMap O Ω (f (x i) j) := by
        have h0 := hval i j 0
        rw [Frame.unt_apply] at h0
        unfold Frame.ctrl
        simpa using h0
      rw [hc] at hv
      unfold Frame.mapFn at hv
      simp at hv
      rw [Pi.sub_apply, Pi.sub_apply, hinj hv, sub_self]
      exact Submodule.zero_mem _
  have hstabV : ∀ v ∈ X.valIn O m 1, X.U O m X.I.z v ∈ X.valIn O m 1 := fun v hv => ctrlOrd_valU X 1 v hv
  have hper1 := ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) hstabV
  have hLper := ctrlOrd_per (X.Lat m W (mIm O Ω 0)) (X.UF m W ⟨X.I.z, X.I.z_mem⟩)
    (fun v hv => ctrlOrd_stab X W _ v hv)
  refine ⟨(X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ M) F', ?_, hLper.1 M _ hLat', (X.U O m X.I.z ^ M) h', ?_, ?_⟩
  · exact (stable c hφ).2 e M heM F' hF'
  · exact ctrlOrd_nat X W F' h' hh'map M
  · have hfM : (X.U O m X.I.z ^ M) f - f ∈ X.valIn O m 1 := by
      rw [hM]
      exact hper1.2 (n + 1) (e + 1) f hn
    have hx : (X.U O m X.I.z ^ M) h' - f = (X.U O m X.I.z ^ M) (h' - f) + ((X.U O m X.I.z ^ M) f - f) := by
      rw [map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem _ (hper1.1 M _ hdiff) hfM

end

theorem UpperTheory.V.Hi.ctrlOrd :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) →
      ∀ (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ) (c : ℕ), W.c0 ≤ c →
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) →
      ∀ U : Subgroup X.Ub, X.FinLevel U → X.Free τ θ U → (∀ F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), X.ctrl m W F = 0 → F = 0) ∧ (X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)).map (X.ctrl m W) = Submodule.span Ω (X.mapFn (A := O) (B := Ω) '' (X.Ord τ θ U : Set (X.Fn O m))) := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ _ _ hinj W m τ θ φ c hc hφ hθ U hU hF
  have hcont : X.I.ContChar θ := by
    unfold Iwa.ContChar
    intro k
    obtain ⟨c3, hc3⟩ := W.continuous_torusCharacter k
    refine ⟨max c c3, fun t ht => ?_⟩
    obtain ⟨y, hy, hye⟩ := hc3 ⟨t, X.I.T_le t.2⟩ (X.I.Tc_anti (le_max_right _ _) ht)
    have h1 := hθ t
    rw [hφ t (X.I.Tc_anti (le_max_left _ _) ht), Units.val_one, map_one, one_mul, hye] at h1
    have h2 : algebraMap O Ω ((θ t : O) - 1) = algebraMap O Ω y := by
      rw [map_sub, h1, map_one]
      ring
    rw [hinj h2]
    exact hy
  obtain ⟨hfin, -, -, hdiv, -⟩ := ordStruct X τ θ hcont U hU hF
  obtain ⟨N, x, hcov, hdis⟩ := UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c
  obtain ⟨lattice, lift, stable⟩ := ctrlOrd_classical X W τ φ U
  let ev : (Fin m → X.Fn Ω (W.d + 1)) →ₗ[Ω] (Fin N × Fin m × Fin (W.d + 1)) → Ω :=
    { toFun := fun F p => X.unt m W F p.2.1 (x p.1) p.2.2
      map_add' := fun F G => by
        funext p
        simp [map_add (f := _)]
      map_smul' := fun a F => by
        funext p
        simp [map_smul] }
  have hev : ∀ F p, ev F p = X.unt m W F p.2.1 (x p.1) p.2.2 := fun F p => rfl
  have hlat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.ClO W τ U c φ →
      (∀ p, ev F p ∈ Λ) → F ∈ X.Lat m W Λ := fun Λ F hFC hv =>
    lattice c hc N x hcov F hFC Λ (fun n i k => hv (n, i, k))
  have hctrlLat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.Lat m W Λ →
      ∀ g i, X.ctrl m W F g i ∈ Λ := by
    intro Λ F hFL g i
    have h := hFL i g 0
    rw [Frame.unt_apply] at h
    unfold Frame.ctrl
    exact h
  have hzero : ∀ F : Fin m → X.Fn Ω (W.d + 1), (∀ i g, X.unt m W F i g = 0) → F = 0 := by
    intro F hF0
    funext i g
    have hu := hF0 i g
    rw [Frame.unt_apply] at hu
    have hv := congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu
    simpa [Matrix.mulVec_mulVec] using hv
  have hTC : ∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ :=
    (stable c hφ).1
  have hbij : Set.BijOn ev (X.ClO W τ U c φ) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro F1 h1 F2 h2 he
      have hD : F1 - F2 ∈ X.ClO W τ U c φ := Submodule.sub_mem _ h1 h2
      have hL := hlat ⊥ (F1 - F2) hD (fun p => by
        rw [map_sub, Pi.sub_apply, he, sub_self]
        exact Submodule.zero_mem _)
      have h0 := hzero (F1 - F2) (fun i g => by
        funext k
        exact (Submodule.mem_bot O).1 (hL i g k))
      exact sub_eq_zero.1 h0
    · intro v _
      obtain ⟨F, hFC, hFv⟩ := ctrlOrd_prescribed_values X W τ φ U c θ hφ hθ hF N x hcov hdis
        (fun n i k => v (n, i, k))
      exact ⟨F, hFC, funext fun p => hFv p.1 p.2.1 p.2.2⟩
  have hint : ∀ F ∈ X.ClO W τ U c φ, (∀ p, ev F p ∈ mIm O Ω 0) →
      ∀ p, ev (X.UF m W ⟨X.I.z, X.I.z_mem⟩ F) p ∈ mIm O Ω 0 := by
    intro F hFC hv p
    have hL := ctrlOrd_stab X W (mIm O Ω 0) F (hlat _ F hFC hv)
    exact hL p.2.1 (x p.1) p.2.2
  obtain ⟨S, hSfree, hSspan, hSprop, hSapprox⟩ := UpperTheory.exists_free_lattice_spanning_ordinary_part O Ω (Fin m → X.Fn Ω (W.d + 1))
    (Fin N × Fin m × Fin (W.d + 1)) (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) ev hinj hbij hTC hint
  have hClOrd : X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c
      ((Units.map (algebraMap O Ω).toMonoidHom).comp φ) = Submodule.span Ω (S : Set _) := by
    rw [← hSspan]
    rfl
  have hSC : ∀ F ∈ S, F ∈ X.ClO W τ U c φ := fun F h => (hSprop F h).1
  have hSlat : ∀ F ∈ S, F ∈ X.Lat m W (mIm O Ω 0) := fun F h => hlat _ F (hSprop F h).1 (hSprop F h).2.1
  have hCper := ctrlOrd_per (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) hTC
  have hSper : ∀ F ∈ S, ∀ k, ∃ n : ℕ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ (n + 1)) F - F ∈ X.Lat m W (mIm O Ω k) := by
    intro F h k
    obtain ⟨n, hn⟩ := (hSprop F h).2.2 k
    exact ⟨n, hlat _ _ (Submodule.sub_mem _ (hCper.1 (n + 1) F (hSprop F h).1) (hSprop F h).1) hn⟩
  have hSord : ∀ F ∈ S, ∃ f ∈ X.Ord τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F := by
    intro F h
    obtain ⟨f, hfSp, hfmap, -⟩ := lift c θ hinj hθ F (hSC F h) (hSlat F h)
    refine ⟨f, (mem_ord_iff X τ θ U f).2 ⟨hfSp, fun k => ?_⟩, hfmap⟩
    obtain ⟨n, hn⟩ := hSper F h k
    refine ⟨n, ctrlOrd_map X hinj k _ (fun g i => ?_)⟩
    rw [map_sub, ctrlOrd_nat X W F f hfmap (n + 1), hfmap, ← map_sub]
    exact hctrlLat _ _ hn g i
  refine ⟨fun F hF0 h0 => ?_, ?_⟩
  · rw [hClOrd] at hF0
    exact UpperTheory.injective_on_span_of_integral_free_submodule O Ω (Fin m → X.Fn Ω (W.d + 1)) (Ga × Gp) m (X.ctrl m W) S hinj hSfree
      (fun F h g i => by
        obtain ⟨y, -, hy⟩ := mem_mIm.1 (hctrlLat _ F (hSlat F h) g i)
        exact ⟨y, hy⟩)
      (fun F h h0 => ctrlOrd_inj X W hinj F (hSlat F h) (hSper F h) h0) F hF0 h0
  · rw [hClOrd, Submodule.map_span]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨F, hFS, rfl⟩
      obtain ⟨f, hf, hfm⟩ := hSord F hFS
      exact ⟨f, hf, hfm⟩
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      let L : Submodule O (X.Ord τ θ U) :=
        ((Submodule.span Ω (X.ctrl m W '' (S : Set _))).restrictScalars O).comap
          ((X.mapFn (B := Ω)).comp (X.Ord τ θ U).subtype)
      have hV := ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) (fun v hv => ctrlOrd_valU X 1 v hv)
      have hle : (⊤ : Submodule O (X.Ord τ θ U)) ≤ L ⊔ maximalIdeal O • ⊤ := by
        intro g _
        obtain ⟨G, hGC, hGlat, h, hhmap, hhf⟩ := ctrlOrd_approx X W hinj τ θ φ c hc hφ hθ U hU hF g g.2
        obtain ⟨F', hF'S, hF'ap⟩ := hSapprox G hGC (fun p => hGlat p.2.1 (x p.1) p.2.2)
        obtain ⟨J, hJ⟩ := hF'ap 1
        obtain ⟨n, hn⟩ := ((mem_ord_iff X τ θ U g).1 g.2).2 1
        obtain ⟨q, hq⟩ : (n + 1) ∣ (max J (n + 1)).factorial :=
          Nat.dvd_factorial (Nat.succ_pos n) (le_max_right _ _)
        obtain ⟨g', hg'Ord, hg'map⟩ := hSord F' hF'S
        have hmem : (g : X.Fn O m) - g' ∈ X.valIn O m 1 := by
          have e1 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g ∈ X.valIn O m 1 := by
            rw [hq]
            exact hV.2 (n + 1) q g hn
          have e2 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) ∈ X.valIn O m 1 := hV.1 _ _ hhf
          have e3 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g' ∈ X.valIn O m 1 := by
            apply ctrlOrd_map X hinj 1
            intro a i
            rw [map_sub, ctrlOrd_nat X W G h hhmap, hg'map, ← map_sub]
            apply hctrlLat (mIm O Ω 1)
            apply hlat _ _ (Submodule.sub_mem _ (hCper.1 _ G hGC) (hSC F' hF'S))
            intro p
            exact hJ _ (le_max_left _ _) p
          have hx : (g : X.Fn O m) - g' = ((X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g') -
              (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) -
              ((X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g) := by
            rw [map_sub]
            abel
          rw [hx]
          exact Submodule.sub_mem _ (Submodule.sub_mem _ e3 e2) e1
        refine Submodule.mem_sup.2 ⟨⟨g', hg'Ord⟩, ?_, g - ⟨g', hg'Ord⟩, ?_, by abel⟩
        · show X.mapFn (B := Ω) g' ∈ Submodule.span Ω (X.ctrl m W '' (S : Set _))
          rw [hg'map]
          exact Submodule.subset_span ⟨F', hF'S, rfl⟩
        · have hd := hdiv 1 (g - ⟨g', hg'Ord⟩) hmem
          rwa [pow_one] at hd
      have hL : L = ⊤ := top_le_iff.1
        (Submodule.le_of_le_smul_of_le_jacobson hfin.fg_top
          (by simpa only [Ideal.jacobson_bot] using IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal O)) hle)
      have hfL : (⟨f, hf⟩ : X.Ord τ θ U) ∈ L := by
        rw [hL]
        trivial
      exact hfL
