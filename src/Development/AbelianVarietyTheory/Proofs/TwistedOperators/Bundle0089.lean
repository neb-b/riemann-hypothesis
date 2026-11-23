module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsMultiplicationEquivariant
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem rev_ofFn_succ {A : Type} {m : ℕ} (α : Fin (m + 1) → A) :
    (List.ofFn α).reverse = α (Fin.last m) :: (List.ofFn (Fin.init α)).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem wordFun_move_letter {M : Type} [AddCommGroup M] {n : ℕ} (B : List (Fin n × Fin n) → M)
    (hB : ∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
      B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0))
    (c d : Fin n) : ∀ (m : ℕ) (α : Fin m → Fin n × Fin n) (p : List (Fin n × Fin n)),
      B (p ++ (c, d) :: (List.ofFn α).reverse) - B (p ++ ((List.ofFn α).reverse ++ [(c, d)])) =
        ∑ i, ((if d = (α i).1 then B (p ++ (List.ofFn (Function.update α i (c, (α i).2))).reverse) else 0) -
          (if (α i).2 = c then B (p ++ (List.ofFn (Function.update α i ((α i).1, d))).reverse) else 0)) := by
  intro m
  induction m with
  | zero => intro α p; simp
  | succ m ih =>
    intro α p
    rw [Fin.sum_univ_castSucc]
    have hl : ∀ q, (List.ofFn (Function.update α (Fin.last m) q)).reverse =
        q :: (List.ofFn (Fin.init α)).reverse := by
      intro q; rw [rev_ofFn_succ, Function.update_self, Fin.init_update_last]
    have hc : ∀ (i : Fin m) q, (List.ofFn (Function.update α i.castSucc q)).reverse =
        α (Fin.last m) :: (List.ofFn (Function.update (Fin.init α) i q)).reverse := by
      intro i q
      rw [rev_ofFn_succ, Function.update_of_ne (Fin.castSucc_ne_last i).symm, Fin.init_update_castSucc]
    simp only [hl, hc]
    have hi : ∀ i : Fin m, α i.castSucc = Fin.init α i := fun i => rfl
    simp only [hi]
    rw [rev_ofFn_succ α]
    have h1 := ih (Fin.init α) (p ++ [α (Fin.last m)])
    have h2 := hB p (List.ofFn (Fin.init α)).reverse c d (α (Fin.last m)).1 (α (Fin.last m)).2
    simp only [List.append_assoc, List.cons_append, List.nil_append, Prod.mk.eta] at h1 h2 ⊢
    rw [← h1, ← h2]
    abel

theorem jetRel_equivariant : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → ∀ c d : Fin n, ε c = ε d → ∀ y y' : W, j y' = E d c (j y) → ∀ G G' : (Fin m → Fin n × Fin n) → W, arrTo V n m (fun α => j (G' α)) = arrE E m c d (arrTo V n m fun α => j (G α)) → ∑ α, B (List.ofFn α).reverse y (G' α) = ∑ α, B (List.ofFn α).reverse y' (G α) := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hJ c d hcd y y' hy G G' hG
  have hex : ∀ x : W, ∃ x' : W, j x' = E c d (j x) := by
    intro x
    have h1 : j x ∈ kSpan ε E u := by
      rw [← hL.2.2.2.2]; exact ⟨x, rfl⟩
    have h2 := compact_span_compact_stable ε E u c d hcd _ h1
    rw [← hL.2.2.2.2] at h2
    exact h2
  choose T hT using hex
  have happ : ∀ (F : (Fin m → Fin n × Fin n) → V) α, arrTo V n m F α = F α := by
    intro F α; simp [arrTo]
  have hG' : ∀ α, G' α = ∑ i, ((if (α i).1 = c then G (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then G (Function.update α i ((α i).1, c)) else 0)) + T (G α) := by
    intro α
    apply j.injective
    have h := congrArg (fun F : Arr V n m => F α) hG
    simp only [arr_operator_apply, factorAction_apply', happ] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_add (f := _), map_sum, hT]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hR : ∀ α : Fin m → Fin n × Fin n, B (List.ofFn α).reverse y' (G α) =
      ∑ i, ((if d = (α i).1 then B (List.ofFn (Function.update α i (c, (α i).2))).reverse y (G α) else 0) -
          (if (α i).2 = c then B (List.ofFn (Function.update α i ((α i).1, d))).reverse y (G α) else 0)) +
        B (List.ofFn α).reverse y (T (G α)) := by
    intro α
    have h := wordFun_move_letter (fun l => B l y (G α)) (fun l₁ l₂ a b c d => by
      have := congrArg (fun φ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ => φ y (G α)) (hJ.1 l₁ l₂ a b c d)
      simp only [LinearMap.sub_apply] at this
      rw [this]
      split_ifs <;> simp) c d m α []
    simp only [List.nil_append] at h
    rw [← h, hJ.2.1 _ c d hcd y (G α) _ (hT _), hJ.2.2.1 _ c d hcd y y' _ hy]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hG', map_add (f := _), map_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sub, Finset.sum_sub_distrib]
  congr 1
  · refine ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      ((sum_update_first_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β))).trans ?_)
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h : (β i).1 = d
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · exact ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      (sum_update_second_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β)))

end GlobalTheory.SphJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicLeftInvariantDerivativeCalculusNearOn
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJetCalc

section General

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

theorem analyticAt_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) :
    AnalyticAt ℂ (fun w => fderiv ℂ f w (L w)) z := by

  have hd : AnalyticAt ℂ (fderiv ℂ f) z := hf.fderiv
  have hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z := hd.prod (L.analyticAt z)
  have hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z) :=
    (ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2)
    (f := fun w => (fderiv ℂ f w, L w)) hev hp

theorem fderiv_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) (M : A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z M
      = fderiv ℂ (fderiv ℂ f) z M (L z) + fderiv ℂ f z (L M) := by

  have hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have hP := hD.clm_apply L.hasFDerivAt
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem snd_symm {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (M N : A) :
    fderiv ℂ (fderiv ℂ f) z M N = fderiv ℂ (fderiv ℂ f) z N M := by

  have hS : IsSymmSndFDerivAt ℂ f z := hf.contDiffAt.isSymmSndFDerivAt_of_omega
  exact hS M N

theorem comm_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L K : A →L[ℂ] A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z (K z) - fderiv ℂ (fun w => fderiv ℂ f w (K w)) z (L z)
      = fderiv ℂ f z (L (K z) - K (L z)) := by

  rw [fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]
  abel

end General

theorem leftInvariant_calculus (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : Matrix (Fin n) (Fin n) ℂ → B) (hf : AnalyticAt ℂ f 1) :
    (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧
    (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧
    ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1]
      Rz Z (fun z => fderiv ℂ f z (Y * z)) := by

  let RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)
  let LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)
  have hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B),
      Rz Z g = fun w => fderiv ℂ g w (RM Z w) := fun Z g => rfl
  have hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  refine ⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩
  · rw [hRz]
    exact analyticAt_linField hf (RM Z)
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (RM A)
    have hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A) := by
      show z * A * Z - z * Z * A = z * (A * Z - Z * A)
      rw [mul_sub, mul_assoc, mul_assoc]
    rw [hb] at hc
    exact hc
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (LM Y)
    have hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0 := by
      show Y * z * Z - Y * (z * Z) = 0
      rw [mul_assoc, sub_self]
    rw [hb, map_zero, sub_eq_zero] at hc
    exact hc

end GlobalTheory.SphJetCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedDerivInnerExpEqWordJetForms
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.Taylor

variable {n : ℕ}

theorem analyticAt_Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (Rz Z f) 1 := by
  unfold Rz
  exact (ContinuousLinearMap.id ℂ (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B)).analyticAt_bilinear _ |>.comp₂ hf.fderiv
    (analyticAt_id.mul analyticAt_const)

theorem analyticAt_Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ε : Fin n → Bool)
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (l : List (Fin n × Fin n)) :
    AnalyticAt ℂ (Rw ε l f) 1 := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact analyticAt_Rz ih _

theorem hasDerivAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun t : ℂ => NormedSpace.exp (t • Z)) (NormedSpace.exp (s • Z) * Z) s :=
  hasDerivAt_exp_smul_const Z s

theorem analyticAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => NormedSpace.exp (t • Z)) s :=
  Differentiable.analyticAt (fun t => (hasDerivAt_expC Z t).differentiableAt) s

theorem analyticAt_comp {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) 0 := by
  have h1 : AnalyticAt ℂ (fun t : ℂ => L (g (NormedSpace.exp (t • Z)))) 0 :=
    (L.analyticAt _).comp (AnalyticAt.comp_of_eq hg (analyticAt_expC Z 0) (by simp))
  have h2 := AnalyticAt.comp_of_eq (h1.restrictScalars (𝕜 := ℝ)) (Complex.ofRealCLM.analyticAt 0) (by simp)
  exact h2

theorem deriv_comp_eventually {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) =ᶠ[𝓝 0]
      fun t : ℝ => L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z))) := by
  have hc : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) 0 :=
      (hasDerivAt_expC Z ((0 : ℝ) : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [hc.eventually hg.eventually_analyticAt] with t ht
  have h1 : HasDerivAt (fun s : ℂ => L (g (NormedSpace.exp (s • Z))))
      (L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z)))) (t : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expC Z t))
  exact h1.comp_ofReal.deriv

theorem Rz_thM {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B) (z : Matrix (Fin n) (Fin n) ℂ) :
    Rz (thM ε X) g z = ∑ p : Fin n × Fin n, X p.1 p.2 • Rz (thE ε p) g z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Rz, thM, Finset.mul_sum, map_sum, mul_smul_comm, map_smul]

theorem iteratedDeriv_inner_exp : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  intro V W _ _ _ _ n ε E _ j f hf hJ X m y x
  let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
  have hL : ∀ T : W →L[ℂ] W, L T = ⟪y, T x⟫_ℂ := fun T => rfl
  have key : ∀ (m : ℕ) (l : List (Fin n × Fin n)),
      iteratedDeriv m (fun t : ℝ => L (Rw ε l f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
        ⟪j y, (actM E X ^ m) (ew E l (j x))⟫_ℂ := by
    intro m
    induction m with
    | zero =>
      intro l
      have := congrArg (fun B => B y x) (hJ l)
      simp only [funJet_apply, modJet_apply] at this
      simpa [hL] using this
    | succ m ih =>
      intro l
      rw [iteratedDeriv_succ', (deriv_comp_eventually (analyticAt_Rw ε hf l) L _).iteratedDeriv_eq]
      have e : (fun t : ℝ => L (Rz (thM ε X) (Rw ε l f) (NormedSpace.exp ((t : ℂ) • thM ε X)))) =
          fun t : ℝ => ∑ p : Fin n × Fin n,
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X))) := by
        funext t
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Rz_thM, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      rw [e, iteratedDeriv_fun_sum (fun p _ =>
        contDiffAt_const.mul (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt)]
      have e2 : ∀ p : Fin n × Fin n, iteratedDeriv m (fun t : ℝ =>
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
          X p.1 p.2 * ⟪j y, (actM E X ^ m) (E p.1 p.2 (ew E l (j x)))⟫_ℂ := by
        intro p
        rw [iteratedDeriv_const_mul _ (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt, ih]
        simp [ew]
      simp only [e2]
      rw [pow_succ, Module.End.mul_apply]
      have e3 : ∀ v : V, actM E X v = ∑ p : Fin n × Fin n, X p.1 p.2 • E p.1 p.2 v := by
        intro v
        simp [actM, Fintype.sum_prod_type, LinearMap.sum_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e3, map_sum, inner_sum]
      simp only [map_smul, inner_smul_right]
  simpa [hL, Rw, ew] using key m []

end GlobalTheory.SphJet.Taylor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetRelPermAndCompactVanish
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem jetRel_perm_of_vanish_prefix {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} {j : W →ₗᵢ[ℂ] V}
    {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hB : JetRel ε E Λ u j B)
    (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    ∀ l₁ : List (Fin n × Fin n), (l₁ ++ l).length = m + 1 → B (l₁ ++ l) = B (l₁ ++ l') := by
  induction h with
  | nil => intro l₁ _; rfl
  | cons p _ ih =>
    intro l₁ hl
    have := ih (l₁ ++ [p]) (by simpa using hl)
    simpa using this
  | swap p q l =>
    intro l₁ hl
    obtain ⟨a, b⟩ := q
    obtain ⟨c, d⟩ := p
    have h1 := hB.1 l₁ l a b c d
    have hlen : ∀ r : Fin n × Fin n, B (l₁ ++ r :: l) = 0 := by
      intro r
      apply h0
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    rw [hlen, hlen, ite_self, ite_self, sub_zero] at h1
    exact sub_eq_zero.mp h1
  | trans h₁ _ ih₁ ih₂ =>
    intro l₁ hl
    rw [ih₁ l₁ hl, ih₂ l₁ (by rw [← hl]; simp [h₁.length_eq])]

theorem jetRel_perm_and_compact_vanish :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → (∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) → (∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l') ∧ ∀ l : List (Fin n × Fin n), l.length = m + 1 → (∃ p ∈ l, ε p.1 = ε p.2) → B l = 0 := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hB h0
  have hperm : ∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l' := by
    intro l l' h hl
    simpa using jetRel_perm_of_vanish_prefix hB h0 h [] (by simpa using hl)
  refine ⟨hperm, ?_⟩
  rintro l hl ⟨⟨a, b⟩, hp, hab⟩
  classical
  have hpe := List.perm_cons_erase hp
  have hlen : (l.erase (a, b)).length ≤ m := by
    have := hpe.length_eq
    simp only [List.length_cons] at this
    omega
  rw [hperm _ _ hpe hl]
  ext y x
  have hy : j y ∈ Formalism.REAL.kSpan ε E u := by
    rw [← hL.2.2.2.2]; exact ⟨y, rfl⟩
  have hy2 : E b a (j y) ∈ Formalism.REAL.kSpan ε E u := compact_span_compact_stable ε E u b a hab.symm _ hy
  rw [← hL.2.2.2.2] at hy2
  obtain ⟨y', hy'⟩ := hy2
  rw [hB.2.2.1 _ a b hab y y' x hy', h0 _ hlen]
  simp

end GlobalTheory.SphJet
end

