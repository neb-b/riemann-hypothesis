module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_map_coord {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  classical
  have hc : Continuous fun M : Matrix (Fin a) (Fin a) (ι → ℂ) => M.map fun x => x w :=
    continuous_id.matrix_map (continuous_apply w)
  have key := open scoped Norms.Operator in
    NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix :
      Matrix (Fin a) (Fin a) (ι → ℂ) →+* Matrix (Fin a) (Fin a) ℂ) hc X
  exact key

private theorem gen_prod {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : (ι → Matrix (Fin a) (Fin a) ℂ) → Matrix (Fin a) (Fin a) (ι → ℂ),
      J = fun g => Matrix.of fun i j v => g v i j := ⟨_, rfl⟩
  have Jmap : ∀ g v, (J g).map (fun x => x v) = g v := by
    intro g v
    subst hJ
    ext i j
    rfl
  have Jmul : ∀ g h, J (g * h) = J g * J h := by
    intro g h
    subst hJ
    ext i j v
    simp [Matrix.mul_apply, Finset.sum_apply]
  have Jone : J 1 = 1 := by
    subst hJ
    ext i j v
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij]
  have Jext : ∀ M N : Matrix (Fin a) (Fin a) (ι → ℂ),
      (∀ v, M.map (fun x => x v) = N.map (fun x => x v)) → M = N := by
    intro M N h
    ext i j v
    exact congrFun (congrFun (h v) i) j
  have single : ∀ (w : ι) (m : Matrix (Fin a) (Fin a) ℂ), m.det ≠ 0 →
      J (Function.update 1 w m) ∈ H := by
    intro w m hm
    let K : Submonoid (Matrix (Fin a) (Fin a) ℂ) :=
      { carrier := {p | J (Function.update 1 w p) ∈ H}
        one_mem' := by
          show J (Function.update 1 w 1) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w 1 = 1 := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jone]
          exact H.one_mem
        mul_mem' := by
          intro p q hp hq
          show J (Function.update 1 w (p * q)) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w (p * q) =
              Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w p *
                Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w q := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jmul]
          exact H.mul_mem hp hq }
    have hK : ∀ X, NormedSpace.exp X ∈ K := by
      intro X
      show J (Function.update 1 w (NormedSpace.exp X)) ∈ H
      have : J (Function.update 1 w (NormedSpace.exp X)) =
          NormedSpace.exp (J (Function.update 0 w X)) := by
        apply Jext
        intro v
        rw [Jmap, exp_map_coord, Jmap]
        by_cases hv : v = w
        · subst hv
          simp
        · simp [hv, NormedSpace.exp_zero]
      rw [this]
      exact hH _
    exact UpperTheory.V.AlgRepEndIrreducible.expGenC a K hK m hm
  have hdet : ∀ v, (y.map fun x => x v).det ≠ 0 := by
    intro v
    have h1 := hy.map (Pi.evalRingHom (fun _ : ι => ℂ) v).mapMatrix
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    exact h1.ne_zero
  have all : ∀ s : Finset ι,
      J (fun v => if v ∈ s then y.map (fun x => x v) else 1) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun v => if v ∈ (∅ : Finset ι) then y.map (fun x => x v) else 1) = 1 := by
        funext v
        simp
      rw [this, Jone]
      exact H.one_mem
    | insert b s hb ih =>
      have : (fun v => if v ∈ insert b s then y.map (fun x => x v) else 1) =
          Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) b (y.map fun x => x b) *
            (fun v => if v ∈ s then y.map (fun x => x v) else 1) := by
        funext v
        by_cases hv : v = b
        · subst hv
          simp [hb]
        · simp [hv]
      rw [this, Jmul]
      exact H.mul_mem (single b _ (hdet b)) ih
  have hy' : y = J (fun v => if v ∈ (Finset.univ : Finset ι) then y.map (fun x => x v) else 1) := by
    apply Jext
    intro v
    rw [Jmap]
    simp
  rw [hy']
  exact all _

theorem UpperTheory.V.Lit.Bor.expGenPi :
    UpperTheory.V.Lit.Bor.ExpGenPi := by
  intro T _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_prod (ι := T) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameAd
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.frameAd :
    UpperTheory.V.Lit.Bor.FrameAd := by
  intro E _ _ _ a n e he N _ _ β k
  have hk1 : k.1 * star k.1 = 1 := k.2.2
  have hc : ∀ i j, trF (e i).1 (adHerm k (e j)).1 = trF (e j).1 (star k.1 * (e i).1 * k.1) := fun i j => by
    have h : ((e i).1 * (k.1 * (e j).1 * star k.1)).trace = ((e j).1 * (star k.1 * (e i).1 * k.1)).trace := by
      rw [show (e i).1 * (k.1 * (e j).1 * star k.1) = ((e i).1 * k.1) * ((e j).1 * star k.1) by simp only [mul_assoc],
        Matrix.trace_mul_comm]
      simp only [mul_assoc]
    simp only [trF, adHerm, h]
  have hs : ∀ i, ∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j) = e i := fun i => by
    have h := congrArg Subtype.val (he ⟨star k.1 * (e i).1 * k.1, IsSelfAdjoint.conjugate' (e i).2 k.1⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hc]
    calc ∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (adHerm k (e j)).1
        = k.1 * (∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (e j).1) * star k.1 := by
          simp only [adHerm, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      _ = k.1 * (star k.1 * (e i).1 * k.1) * star k.1 := by rw [← h]
      _ = (k.1 * star k.1) * (e i).1 * (k.1 * star k.1) := by simp only [mul_assoc]
      _ = (e i).1 := by rw [hk1, one_mul, mul_one]
  calc ∑ j, β (adHerm k (e j)) (adHerm k (e j))
      = ∑ j, β (∑ i, trF (e i).1 (adHerm k (e j)).1 • e i) (adHerm k (e j)) :=
        Finset.sum_congr rfl fun j _ => by rw [← he (adHerm k (e j))]
    _ = ∑ j, ∑ i, trF (e i).1 (adHerm k (e j)).1 • β (e i) (adHerm k (e j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ i, β (e i) (∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j)) := by
        rw [Finset.sum_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
    _ = ∑ j, β (e j) (e j) := by simp only [hs]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameBr
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tr_one {R : Type} [CommRing R] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) R) :
    (A * (Z * B - B * Z)).trace = -(B * (Z * A - A * Z)).trace := by
  have h1 : (A * (Z * B)).trace = (B * (A * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (B * (Z * A)).trace = (A * (B * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_sub, Matrix.trace_sub, h1, h2]
  ring

private theorem trF_one {E : Type} [Field E] [NumberField E] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (Z * B - B * Z) = -trF B (Z * A - A * Z) := by
  unfold trF
  rw [tr_one, ← Finset.sum_neg_distrib]
  rfl

private theorem trF_neg {E : Type} [Field E] [NumberField E] {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (-B) = -trF A B := by
  unfold trF
  rw [Matrix.mul_neg, Matrix.trace_neg, ← Finset.sum_neg_distrib]
  rfl

theorem UpperTheory.V.Lit.Bor.frameBr :
    UpperTheory.V.Lit.Bor.FrameBr := by
  intro E _ _ _ a n e he N _ _
  refine ⟨fun β Z hZ => ?_, fun β X h => ?_⟩
  · have h1 : ∀ j, β (brH Z hZ (e j)) (e j) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e k) (e j) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    have h2 : ∀ j, β (e j) (brH Z hZ (e j)) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e j) (e k) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
      rfl
    simp only [h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [trF_one, neg_smul, neg_add_cancel]
  · have hb : ∀ j, (brH _ (h j) X).1 = -((Complex.I • X.1) * (e j).1 - (e j).1 * (Complex.I • X.1)) := by
      intro j
      change (Complex.I • (e j).1) * X.1 - X.1 * (Complex.I • (e j).1) = _
      simp only [Matrix.smul_mul, Matrix.mul_smul, neg_sub]
    have h1 : ∀ j, X.1 * (e j).1 - (e j).1 * X.1 =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • (Complex.I • (e k).1) := by
      intro j
      have h0 : (brH _ (h j) X).1 = ∑ k, trF (e k).1 (brH _ (h j) X).1 • (e k).1 := by
        conv_lhs => rw [he (brH _ (h j) X)]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      have h3 : X.1 * (e j).1 - (e j).1 * X.1 = Complex.I • (brH _ (h j) X).1 := by
        rw [hb]
        simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul,
          one_smul, neg_neg]
      rw [h3]
      conv_lhs => rw [h0]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have h2 : ∀ j, β (Complex.I • (e j).1) (brH _ (h j) X) =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • β (Complex.I • (e j).1) (e k) := by
      intro j
      conv_lhs => rw [he (brH _ (h j) X)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simp only [h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul β, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb, hb, trF_neg, trF_neg, trF_one, neg_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem frame_abs {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hs : LinearMap.IsSymm B) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ (n : ℕ) (e : Fin n → V), ∀ x, x = ∑ j, B (e j) x • e j := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  refine ⟨_, fun j => (Real.sqrt (B (v j) (v j)))⁻¹ • v j, fun x => ?_⟩
  conv_lhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : 0 < B (v j) (v j) := hp _ (v.ne_zero j)
  have h1 : B (v j) x = v.repr x j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have : B (v j) (v k) = 0 := hv (Ne.symm hk)
      simp [this]
    · simp
  have h2 : Real.sqrt (B (v j) (v j)) * Real.sqrt (B (v j) (v j)) = B (v j) (v j) := Real.mul_self_sqrt h0.le
  have h3 : Real.sqrt (B (v j) (v j)) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [smul_smul, map_smul, LinearMap.smul_apply, h1, smul_eq_mul]
  congr 1
  generalize Real.sqrt (B (v j) (v j)) = s at h2 h3
  rw [← h2]
  field_simp

private noncomputable def trB (E : Type) [Field E] [NumberField E] (a : ℕ) : LinearMap.BilinForm ℝ (Herm E a) :=
  LinearMap.mk₂ ℝ (fun X Y => trF X.1 Y.1)
    (fun X Y Z => by simp [trF, add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])
    (fun X Y Z => by simp [trF, mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])

private theorem trF_self {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Herm E a) :
    trF X.1 X.1 = ∑ w : InfinitePlace E, ∑ i, ∑ j, Complex.normSq (X.1 i j w) := by
  have h : star X.1 = X.1 := X.2
  have h' : ∀ i j w, X.1 j i w = starRingEnd ℂ (X.1 i j w) := fun i j w => by
    conv_lhs => rw [← h]
    rfl
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h' i j w, Complex.mul_conj, Complex.ofReal_re]

theorem UpperTheory.V.Lit.Bor.frameEx :
    UpperTheory.V.Lit.Bor.FrameEx := by
  intro E _ _ _ a
  refine frame_abs (trB E a) ⟨fun X Y => ?_⟩ fun X hX => ?_
  · change trF X.1 Y.1 = trF Y.1 X.1
    simp only [trF, Matrix.trace_mul_comm X.1 Y.1]
  · change 0 < trF X.1 X.1
    rw [trF_self]
    have hn : ∀ w i j, 0 ≤ Complex.normSq (X.1 i j w) := fun _ _ _ => Complex.normSq_nonneg _
    refine lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j)
      fun h => hX ?_
    refine Subtype.ext (Matrix.ext fun i j => funext fun w => ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h.symm w (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn w i j).1 h2 j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmLin
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rel_mono {P Q : Sm E a → Prop} (h : ∀ φ, P φ → Q φ) {q : ℕ}
    {ω : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsRelCochain Ξ P ω) :
    IsRelCochain Ξ Q ω :=
  ⟨hω.equiv, hω.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, h φ hφ, rfl⟩) (hω.val X)⟩

private theorem level_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) (φ : Sm E a) (hφ : IsLevelFn U Ξ φ) :
    IsLevelFn U' Ξ φ := ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩

variable {U : Subgroup (GL (Fin a) (Af E))} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem harm_zero {q : ℕ} :
    IsHarm U Ξ r e (0 : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  refine ⟨⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, ?_, ?_⟩
  · exact AlternatingMap.ext fun X => by simp [dCo_apply]
  · cases q with
    | zero => trivial
    | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem harm_comb {q : ℕ} (c : ℂ)
    {ω η : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsHarm U Ξ r e ω)
    (hη : IsHarm U Ξ r e η) : IsHarm U Ξ r e (c • ω + η) := by
  have ap : ∀ X, (c • ω + η) X = c • ω X + η X := fun X => rfl
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, ?_⟩
  · rw [ap, ap, hω.rel.equiv k X, hη.rel.equiv k X, map_add (f := _), map_smul]
  · rw [ap, hω.rel.basic X i hi, hη.rel.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hω.rel.val X)) (hη.rel.val X)
  · refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun hω.closed X
    have h2 := DFunLike.congr_fun hη.closed X
    rw [dCo_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, h2, add_zero]
    rw [← smul_zero c, ← h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · cases q with
    | zero => trivial
    | succ q =>
      refine AlternatingMap.ext fun X => ?_
      have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω.coclosed) X
      have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη.coclosed) X
      rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
      simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Bor.harmLin :
    UpperTheory.V.Lit.Bor.HarmLin := by
  intro E _ _ _ a n e U Ξ r q
  refine ⟨fun s ω c h => ?_, fun ω => ⟨fun h => rel_mono (fun _ hφ => hφ.1) h.rel, fun U' hU =>
    ⟨fun h => ⟨rel_mono (fun φ hφ => ⟨level_mono hU φ hφ.1, hφ.2⟩) h.rel, h.closed, h.coclosed⟩,
      rel_mono (level_mono hU)⟩⟩⟩
  induction (Finset.univ : Finset (Fin s)) using Finset.cons_induction with
  | empty => exact harm_zero
  | cons j t hj ih =>
    rw [Finset.sum_cons]
    exact harm_comb _ (h j) ih
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolExt
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.holExt :
    UpperTheory.V.Lit.Bor.HolExt := by
  intro E _ _ _ a f hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact ⟨fun x => x i j τ, by fun_prop, fun _ => rfl⟩
    · refine ⟨fun x => ((Matrix.of x).det τ)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) τ)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z τ)⁻¹) ((emb E).map_det y.val).symm
  | algebraMap c => exact ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩
  | add f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | mul f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Imports
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.count :
    UpperTheory.V.Lit.Bor.Count := by
  classical
  intro X S deg κ hκ
  have hq : ∀ q, Cardinal.mk {x : S // deg x = q} ≤ κ q := by
    intro q
    let e := Fintype.equivFin {x : S // deg x = q}
    rw [Cardinal.mk_fintype]
    refine hκ q _ (fun i => ((e.symm i).1 : X)) ?_ (fun i => ⟨(e.symm i).1.2, (e.symm i).2⟩)
    intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  calc (S.card : Cardinal) = Cardinal.mk S := (Cardinal.mk_coe_finset).symm
    _ = Cardinal.mk (Σ q, {x : S // deg x = q}) :=
        (Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x : S => deg x))).symm
    _ = Cardinal.sum (fun q => Cardinal.mk {x : S // deg x = q}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum κ := Cardinal.sum_le_sum _ _ hq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipDef :
    UpperTheory.V.Lit.Bor.IpDef := by
  intro E _ _ _ a n e he M _ _ _ _ H N hH q
  refine ⟨fun ω η => ?_, fun ω hω => ⟨?_, fun h0 => ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [ip, map_sum]
      exact Finset.sum_congr rfl fun I _ => hH.herm _ _
  · simp only [ip, Complex.re_sum]
    exact Finset.sum_nonneg fun I _ => hH.nonneg _ (hω _)
  · have hre : ∑ I : Fin q → Fin n, (H (ω fun i => e (I i)) (ω fun i => e (I i))).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re h0
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hH.nonneg _ (hω _))).1 hre
    have h2 : ∀ I : Fin q → Fin n, (ω fun i => e (I i)) = 0 := fun I => by
      refine hH.definite _ (hω _) (Complex.ext (h1 I (Finset.mem_univ _)) ?_)
      exact Complex.conj_eq_iff_im.1 (hH.herm _ _).symm
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : ω X = ∑ I : Fin q → Fin n, ω fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact ω.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [ω.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

