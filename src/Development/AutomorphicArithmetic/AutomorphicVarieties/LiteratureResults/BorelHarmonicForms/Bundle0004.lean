module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmAbs
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem compactSpace_unitary_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    CompactSpace (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
      Set.univ.pi fun _ : T => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  have hof : Continuous (Matrix.of : (Fin a → Fin a → T → ℂ) → Matrix (Fin a) (Fin a) (T → ℂ)) :=
    continuous_id
  refine (hK.image hof).of_isClosed_subset isClosed_unitary ?_
  intro U hU
  refine ⟨Matrix.of.symm U, ?_, by ext i j; rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i j t
  have hM : U.map (fun f => f t) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext k l
    have h : (U * star U) k l t = (1 : Matrix (Fin a) (Fin a) (T → ℂ)) k l t := by
      rw [Unitary.mul_star_self_of_mem hU]
    by_cases hkl : k = l
    · subst hkl
      simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply] using h
    · simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, hkl] using h
  simpa using entry_norm_bound_of_unitary hM i j

private theorem continuous_unitary_toUnits_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    Continuous (Unitary.toUnits : unitary (Matrix (Fin a) (Fin a) (T → ℂ)) →
      (Matrix (Fin a) (Fin a) (T → ℂ))ˣ) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · simpa [Function.comp_def, Unitary.val_toUnits_apply] using continuous_subtype_val
  · simp only [Unitary.val_inv_toUnits_apply]
    exact continuous_subtype_val.comp continuous_inv

private theorem conjTranspose_D_mul_add_mul_D_eq_zero_of_skew {T : Type} [Fintype T] {a d : ℕ}
    {R : GL (Fin a) (T → ℂ) →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hR : IsHolRep R D) (G : Matrix (Fin d) (Fin d) ℂ)
    (hinv : ∀ U : unitary (Matrix (Fin a) (Fin a) (T → ℂ)),
      (R (Unitary.toUnits U))ᴴ * G * R (Unitary.toUnits U) = G)
    (Y : Matrix (Fin a) (Fin a) (T → ℂ)) (hY : star Y = -Y) :
    (D Y)ᴴ * G + G * D Y = 0 := by
  have hcd : ∃ c : ℝ → GL (Fin a) (T → ℂ), c 0 = 1 ∧
      (∀ s, (c s : Matrix (Fin a) (Fin a) (T → ℂ)) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ))) ∧
      ∀ (i j : Fin a) (t : T), HasDerivAt (fun s => (c s : Matrix (Fin a) (Fin a) (T → ℂ)) i j t)
        (Y i j t) 0 := by
    letI : NormedRing (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin a) (Fin a) (T → ℂ)) := FiniteDimensional.complete ℝ _
    let S : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] Matrix (Fin a) (Fin a) (T → ℂ) :=
      { toFun := star
        map_add' := star_add
        map_smul' := fun r M => by simp [star_smul] }
    haveI : @ContinuousStar (Matrix (Fin a) (Fin a) (T → ℂ))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
      ⟨S.continuous_of_finiteDimensional⟩
    have hmem : ∀ s : ℝ, NormedSpace.exp (s • Y) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ)) :=
      fun s => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
        rw [skewAdjoint.mem_iff, star_smul, hY]
        simp)
    refine ⟨fun s => Unitary.toUnits ⟨NormedSpace.exp (s • Y), hmem s⟩, ?_, fun s => ?_, ?_⟩
    · ext1
      simp [Unitary.val_toUnits_apply]
    · simpa [Unitary.val_toUnits_apply] using hmem s
    · intro i j t
      have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
      let L0 : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun M => M i j t
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let L : Matrix (Fin a) (Fin a) (T → ℂ) →L[ℝ] ℂ := ⟨L0, L0.continuous_of_finiteDimensional⟩
      exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hexp
  obtain ⟨c, hc0, hcu, hcd⟩ := hcd
  have hr := hR.der c Y hc0 hcd
  have hconst : ∀ s, (R (c s))ᴴ * G * R (c s) = G := by
    intro s
    have h := hinv ⟨c s, hcu s⟩
    have hu : Unitary.toUnits ⟨(c s : Matrix (Fin a) (Fin a) (T → ℂ)), hcu s⟩ = c s := by
      ext1
      simp [Unitary.val_toUnits_apply]
    rwa [hu] at h
  have h1 : R (c 0) = 1 := by rw [hc0, map_one]
  ext i j
  have e : ∀ s, ((R (c s))ᴴ * G * R (c s)) i j =
      ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j := by
    intro s
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hF := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        ((hr k i).star).mul_const (G k l))).mul (hr l j))
  have hF0 : HasDerivAt (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) 0 0 := by
    have : (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) = fun _ => G i j := by
      funext s
      rw [← e, hconst]
    rw [this]
    exact hasDerivAt_const _ _
  have hu := hF.unique hF0
  rw [h1] at hu
  simp [Matrix.one_apply] at hu
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simpa [Finset.sum_add_distrib] using hu

theorem UpperTheory.V.Lit.Bor.admissible_abs_bound :
    UpperTheory.V.Lit.Bor.AdmAbs := by
  intro T _ a d R D hR
  haveI := compactSpace_unitary_matrix_pi_complex T a
  obtain ⟨G, hG, hinv⟩ := avgPos (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) d
    (R.comp Unitary.toUnits) (fun i j => (hR.cont i j).comp (continuous_unitary_toUnits_matrix_pi_complex T a))
  refine ⟨G, hG, fun Z => ?_⟩
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin a) (Fin a) (T → ℂ), X = (1 / 2 : ℂ) • (Z - star Z) := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Matrix (Fin a) (Fin a) (T → ℂ),
      V = (-(Complex.I / 2)) • (Z + star Z) := ⟨_, rfl⟩
  have hX : star X = -X := by
    subst hXd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hV : star V = -V := by
    subst hVd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hZ : Z = X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hsZ : star Z = -X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have eX : (D X)ᴴ * G = -(G * D X) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv X hX)
  have eV : (D V)ᴴ * G = -(G * D V) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv V hV)
  have hDZ : D Z = D X + Complex.I • D V := by
    conv_lhs => rw [hZ]
    rw [map_add (f := _), map_smul]
  rw [hDZ, hsZ, map_add (f := _), map_neg, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.smul_mul, eX, eV, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul]
  simp [Complex.star_def]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem comm_sq {A : Type} [Ring A] (x y z : A) (h : x * y - y * x = z) :
    x * (y * y) - y * y * x = z * y + y * z := by
  rw [← h]; noncomm_ring

theorem UpperTheory.V.Lit.Bor.casComm :
    UpperTheory.V.Lit.Bor.CasComm := by
  intro E _ _ _ a n e he A _ _ _ _ L hL X
  obtain ⟨h1, h2⟩ := frameBr E a n e he A
  let l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] A :=
    { toFun := fun Y => L (toL Y)
      map_add' := fun Y Z => L.map_add (toL Y) (toL Z)
      map_smul' := fun c Y => L.map_smul c (toL Y) }
  have hl : ∀ Y Z, l Y * l Z - l Z * l Y = l (Y * Z - Z * Y) := hL
  let J : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    { toFun := fun Y => Complex.I • Y
      map_add' := fun Y Z => smul_add _ _ _
      map_smul' := fun c Y => smul_comm _ _ _ }
  let s : Herm E a →ₗ[ℝ] A := l ∘ₗ (Herm E a).subtype
  let t : Herm E a →ₗ[ℝ] A := l ∘ₗ J ∘ₗ (Herm E a).subtype
  have key : ∀ Y, l Y * cas L e - cas L e * l Y =
      ∑ j, (l (Y * (e j).1 - (e j).1 * Y) * l (e j).1 + l (e j).1 * l (Y * (e j).1 - (e j).1 * Y)) -
      ∑ j, (l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y) * l (Complex.I • (e j).1) +
        l (Complex.I • (e j).1) * l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y)) := fun Y => by
    have hc : cas L e = ∑ j, (l (e j).1 * l (e j).1 - l (Complex.I • (e j).1) * l (Complex.I • (e j).1)) := rfl
    rw [hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← comm_sq _ _ _ (hl Y _), ← comm_sq _ _ _ (hl Y _)]
    noncomm_ring
  have hskew : ∀ Z, star Z = -Z → l Z * cas L e - cas L e * l Z = 0 := fun Z hZ => by
    have a1 : ∑ j, l (Z * (e j).1 - (e j).1 * Z) * l (e j).1 + ∑ j, l (e j).1 * l (Z * (e j).1 - (e j).1 * Z) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ s s) Z hZ
    have a2 : ∑ j, l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) * l (Complex.I • (e j).1) +
        ∑ j, l (Complex.I • (e j).1) * l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ t t) Z hZ
    rw [key]
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, Finset.sum_add_distrib]
    rw [a1, a2, sub_zero]
  have hherm : ∀ Y : Herm E a, l Y.1 * cas L e - cas L e * l Y.1 = 0 := fun Y => by
    have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
      have h : star (e j).1 = (e j).1 := (e j).2
      rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
    have a1 : ∑ j, (l (Y.1 * (e j).1 - (e j).1 * Y.1) * l (e j).1 + l (e j).1 * l (Y.1 * (e j).1 - (e j).1 * Y.1)) =
        -∑ j, (l (Complex.I • (e j).1) * l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) +
          l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) * l (Complex.I • (e j).1)) :=
      h2 ((LinearMap.mul ℝ A).compl₁₂ l s + (LinearMap.mul ℝ A).flip.compl₁₂ l s) Y hs
    rw [key, a1, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← neg_sub (Y.1 * (Complex.I • (e j).1)), map_neg]
    noncomm_ring
  let Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X
  have hY : Y = (hp (toL Y)).1 + (1 / 2 : ℝ) • (Y - star Y) := by
    rw [hp_val]; module
  have hZ : star ((1 / 2 : ℝ) • (Y - star Y)) = -((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [star_smul, star_trivial, star_sub, star_star, ← smul_neg, neg_sub]
  have hX : L X = l (hp (toL Y)).1 + l ((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [← map_add (f := _), ← hY]; rfl
  rw [hX]
  exact Commute.add_right (Commute.symm (sub_eq_zero.1 (hherm _))) (Commute.symm (sub_eq_zero.1 (hskew _ hZ)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.delCochain :
    UpperTheory.V.Lit.Bor.DelCochain := by
  intro E _ _ _ a n e he M _ _ _ _ κ L h q ω hω k X
  let β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] M :=
    LinearMap.mk₂ ℝ (fun Y Z => L (toL Y.1) (ω.curryLeft Z fun i => adHerm k (X i)))
      (fun Y Y' Z => LinearMap.congr_fun (map_add L (toL Y.1) (toL Y'.1)) _)
      (fun c Y Z => LinearMap.congr_fun (map_smul L c (toL Y.1)) _)
      (fun Y Z Z' => by rw [map_add (f := _), AlternatingMap.add_apply, map_add (f := _)])
      (fun c Y Z => by
        rw [map_smul, AlternatingMap.smul_apply]
        exact ((L (toL Y.1)).restrictScalars ℝ).map_smul c _)
  have hβ : ∀ Y Z, β Y Z = L (toL Y.1) (ω (Matrix.vecCons Z fun i => adHerm k (X i))) := fun _ _ => rfl
  have key := UpperTheory.V.Lit.Bor.frameAd E a n e he M β k
  simp only [hβ] at key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [del_apply, del_apply, map_sum, ← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Matrix.vecCons (adHerm k (e j)) fun i => adHerm k (X i)) =
      fun i => adHerm k (Matrix.vecCons (e j) X i) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hc, hω k]
  exact (LinearMap.congr_fun (h k (e j)) _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem diff_translate {T : Type} [Fintype T] {a : ℕ} (Φ : (Fin a → Fin a → T → ℂ) → ℂ)
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (A B : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (A.val * Matrix.of x * B.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ
      (fun x : Fin a → Fin a → T → ℂ => (fun i j => (A.val * Matrix.of x * B.val) i j : Fin a → Fin a → T → ℂ)) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  exact (A.isUnit.mul hx).mul B.isUnit

theorem UpperTheory.V.Lit.Bor.holId :
    UpperTheory.V.Lit.Bor.HolId := by
  intro E _ _ _ a
  have hv : ∀ y : GL (Fin a) (Cinf E),
      (GeneralLinearGroup.map (emb E) y).val = Matrix.of (fun i j => emb E (y.val i j)) := fun y => rfl
  let S : Submonoid (GL (Fin a) ((E →+* ℂ) → ℂ)) :=
    { carrier := {g | ∀ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ,
        DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
        (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) → Φ (fun i j => g.val i j) = 0}
      one_mem' := fun Φ _ h0 => by
        have h := h0 1
        have e : (fun i j => emb E ((1 : GL (Fin a) (Cinf E)).val i j)) =
            fun i j => (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val i j := by
          have := hv 1
          rw [map_one] at this
          exact this.symm
        rwa [e] at h
      mul_mem' := fun {g h} hg hh Φ hΦ h0 => by
        have h1 : ∀ y : GL (Fin a) (Cinf E),
            Φ (fun i j => ((GeneralLinearGroup.map (emb E) y).val * h.val) i j) = 0 := fun y => by
          have := hh _ (diff_translate Φ hΦ (GeneralLinearGroup.map (emb E) y) 1) fun z => by
            have h2 := h0 (y * z)
            have h3 := hv (y * z)
            rw [map_mul, Units.val_mul, hv z] at h3
            simp only [Units.val_one, mul_one, h3]
            exact h2
          simp only [Units.val_one, mul_one] at this
          exact this
        have := hg _ (diff_translate Φ hΦ 1 h) fun z => by
          simp only [Units.val_one, one_mul]
          exact h1 z
        simp only [Units.val_one, one_mul] at this
        exact this }
  intro Φ hΦ h0 g
  refine expGenPi _ a S (fun X y hy Ψ hΨ h1 => ?_) g Φ hΦ h0
  rw [hy]
  exact holIdExp E a Ψ hΨ h1 X
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ImportsVariant
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indep :
    UpperTheory.V.Lit.Bor.Indep := by
  intro E _ _ _ a d q s π hπ ω h0 hV c hc
  have hind : iSupIndep fun i => (π i).V :=
    UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx)
      (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))
  have key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0 := by
    intro X k i
    have h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))),
        (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X := fun t f => by
      induction t using Finset.cons_induction with
      | empty => rfl
      | cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]
    have h1 : ∑ j, c j • cmp k (ω j X) = 0 := by
      have h2 := congrArg (fun η => cmp k (η X)) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [h, map_sum, smul_apply, map_smul, zero_apply, map_zero] using h2
    exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X))
      (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)
  funext i
  by_contra hci
  refine h0 i (AlternatingMap.ext fun X => ?_)
  rw [← sum_cmp (ω i X), zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ring_sq {R : Type} [Ring R] {x y : R} (h : Commute x y) : (y - x) * (x + y) = y * y - x * x := by
  have h' := h.eq
  rw [sub_mul, mul_add, mul_add, h']
  abel

private theorem ring_br {R : Type} [Ring R] {x y x' y' : R} (h : Commute x y') (h' : Commute x' y) :
    (x + y) * (y' - x') - (y' - x') * (x + y) = (y * y' - y' * y) - (x * x' - x' * x) := by
  simp only [sub_mul, mul_add, add_mul, mul_sub, h.eq, h'.eq]
  abel

theorem UpperTheory.V.Lit.Bor.kugaSucc :
    UpperTheory.V.Lit.Bor.KugaSucc := by
  intro E _ _ _ a n e he M _ _ _ _ A B hA hB hAB q ω hω X
  have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have hsq : ∀ (Z : Lie E a) (m : M), (B - A) Z ((A + B) Z m) = (B Z * B Z - A Z * A Z) m := fun Z m =>
    LinearMap.congr_fun (ring_sq (hAB Z Z)) m
  have hbr : ∀ (Y Z : Matrix (Fin a) (Fin a) (Cinf E)) (m : M),
      (A + B) (toL Y) ((B - A) (toL Z) m) - (B - A) (toL Z) ((A + B) (toL Y) m) =
        (B - A) (toL (Y * Z - Z * Y)) m := fun Y Z m => by
    have h := ring_br (hAB (toL Y) (toL Z)) (hAB (toL Z) (toL Y))
    rw [hA, hB] at h
    exact LinearMap.congr_fun h m
  have hup : ∀ (i : Fin (q + 1)) (Y : Herm E a),
      (-1 : ℤ) ^ (i : ℕ) • ω (Matrix.vecCons Y (i.removeNth X)) = ω (Function.update X i Y) := fun i Y => by
    rw [← Fin.insertNth_removeNth, AlternatingMap.map_insertNth]
  have hfr : ∀ i : Fin (q + 1),
      ∑ j, (B - A) (toL ((X i).1 * (e j).1 - (e j).1 * (X i).1)) (ω (Function.update X i (e j))) =
        -∑ j, (B - A) (toL (Complex.I • (e j).1)) (ω (Function.update X i (brH _ (hs j) (X i)))) := fun i =>
    (frameBr E a n e he M).2
      (LinearMap.mk₂ ℝ (fun Z Y => (B - A) (toL Z) (ω (Function.update X i Y)))
        (fun Z Z' Y => LinearMap.congr_fun (map_add (B - A) (toL Z) (toL Z')) _)
        (fun c Z Y => LinearMap.congr_fun (map_smul (B - A) c (toL Z)) _)
        (fun Z Y Y' => by rw [AlternatingMap.map_update_add, map_add (f := _)])
        (fun c Z Y => by rw [AlternatingMap.map_update_smul, LinearMap.map_smul_of_tower])) (X i) hs
  have h1 : dCo (A + B) (del (B - A) e ω) X =
      ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) := by
    rw [dCo_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [del_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hup, map_zsmul, map_zsmul]
  have h2 : del (B - A) e (dCo (A + B) ω) X =
      ∑ j, ((B - A) (toL (e j).1) ((A + B) (toL (e j).1) (ω X)) -
        ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j))))) := by
    rw [del_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dCo_cons, map_sub, dCo_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hup, map_zsmul, map_zsmul, map_zsmul]
    rfl
  have h3 : ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) -
      ∑ j, ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j)))) =
      -∑ j, (B - A) (toL (Complex.I • (e j).1)) ((A + B) (toL (Complex.I • (e j).1)) (ω X)) := by
    simp only [← Finset.sum_sub_distrib, hbr]
    rw [Finset.sum_comm]
    simp only [hfr]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hω _ (hs j), map_sum]
  rw [h1, h2, Finset.sum_sub_distrib, add_sub_left_comm, h3, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    cas, cas, ← Finset.sum_sub_distrib, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsq, hsq]
  simp only [LinearMap.sub_apply]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneEig
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.oneEig :
    UpperTheory.V.Lit.Bor.OneEig := by
  intro E _ _ _ a π Ξ r hr hC
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π 1
  have hc' : ∀ ψ ∈ π.V, lie E a (oneL E a) ψ = c • ψ := hc
  have h0 : c + (r : ℂ) = 0 := by
    by_contra hne
    refine not_hasCohomology_of_central hne (fun m => ?_) hC
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
    | tmul φ v =>
      have e : π.op (.lie (oneL E a)) φ = c • φ := Subtype.ext (hc' φ.1 φ.2)
      have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
      rw [tensorLie_tmul, e, hr', Matrix.smul_mulVec, Matrix.one_mulVec, add_smul, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul]
  intro φ hφ
  rw [hc' φ hφ, eq_neg_of_add_eq_zero_left h0]
end

