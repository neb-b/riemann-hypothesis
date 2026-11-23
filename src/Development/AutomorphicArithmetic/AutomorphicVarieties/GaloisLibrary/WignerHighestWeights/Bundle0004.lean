module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.GlNegOp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlphaAbs
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rp_eq {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (x : Fin n → X),
      rp n b x = (List.ofFn fun i => MulOpposite.op (b i (x i))).prod.unop := by
  intro n
  induction n with
  | zero => intro b x; rw [rp_zero]; simp
  | succ n ih =>
    intro b x
    rw [rp_succ, ih, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    rfl

private noncomputable def sh {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M :=
  A + (c • Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight 1

private theorem sh_apply {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    sh A c x = A x + (c * x.trace) • (1 : Module.End ℂ M) := rfl

private theorem trace_single' {n : ℕ} (i j : Fin n) :
    (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h]

private theorem sh_single {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    sh A c (Matrix.single i j 1) = Formalism.REAL.Tm (fun i j => A (Matrix.single i j 1)) c i j := by
  rw [sh_apply, trace_single', Formalism.REAL.Tm]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private theorem sh_single_op {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    MulOpposite.op (sh (-B) c (Matrix.single i j 1)) =
      Formalism.REAL.Tm (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) c i j := by
  rw [sh_apply, trace_single', Formalism.REAL.Tm]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private noncomputable def epsL {M : Type} [AddCommGroup M] [Module ℂ M] (n : ℕ) :
    ((Fin n → Matrix (Fin n) (Fin n) ℂ) → M) →ₗ[ℂ] M where
  toFun := eps
  map_add' u v := by simp [eps, Finset.sum_add_distrib]
  map_smul' c u := by simp [eps, Finset.smul_sum, smul_comm c]

private theorem map_eps {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (κ : Module.End ℂ M)
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M) : κ (eps μ) = eps fun x => κ (μ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eps, map_sum, map_zsmul]

theorem UpperTheory.V.AlgRepEndIrreducible.alphaAbs :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (arg : Fin n → ℂ),
      (∀ x y, Commute (A x) (B y)) →
      ∃ α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M,
        (∀ (m : M) (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M), (∀ x, f x = A x m + B x m) →
          α f = Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct (fun i j => A (Matrix.single i j 1)) arg m -
            (Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) arg).unop m) ∧
        (∀ (κ : Module.End ℂ M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 → (∀ x, κ * A x = A (g * x * g') * κ) →
          (∀ x, κ * B x = B (g * x * g') * κ) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
            (∀ x, κ (f x) = f' (g * x * g')) → κ (α f) = α f') ∧
        ∀ (D : Module.End ℂ M) (y : Matrix (Fin n) (Fin n) ℂ), (∀ x, D * A x - A x * D = A (y * x - x * y)) →
          (∀ x, D * B x - B x * D = B (y * x - x * y)) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
            (∀ x, D (f x) = f' x + f (y * x - x * y)) → D (α f) = α f' := by
  intro M _ _ n A B arg hc
  obtain ⟨T, hT⟩ := telML (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
  let α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M :=
    { toFun := fun f => eps (T f)
      map_add' := fun u v => by rw [map_add (f := _)]; exact (epsL n).map_add _ _
      map_smul' := fun c u => by rw [map_smul]; exact (epsL n).map_smul _ _ }
  have hα : ∀ f, α f = eps (T f) := fun _ => rfl
  refine ⟨α, fun m f hf => ?_, fun κ g g' hg hA hB f f' hf => ?_, fun D y hA hB f f' hf => ?_⟩
  · have h := telSum (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
      (fun i j x y => by
        rw [sh_apply, sh_apply]
        exact ((hc x y).neg_right.add_right ((Commute.one_right _).smul_right _)).add_left
          ((Commute.one_left _).smul_left _)) m f
      (fun i x => by rw [hf, sh_apply, sh_apply]; simp)
    rw [hα]
    unfold eps Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct Formalism.HermitianLatticeCounting.P.orderedTermProduct
    simp only [hT, h, rp_eq, units, sh_single_op]
    simp only [sh_single, ← zsmul_eq_mul, smul_smul, Finset.unop_sum,
      MulOpposite.unop_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (g * x * g').trace = x.trace := fun x => by
      rw [Matrix.trace_mul_cycle, hg, one_mul]
    have h := telGrp (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) κ
      (fun x => g * x * g')
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, hA]; simp)
      (fun i x => by
        rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, mul_neg, hB]
        simp) f f' hf
    rw [hα, hα, map_eps, ← epsGrp M n (T f') g g' hg]
    simp only [hT, h]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (y * x - x * y).trace = 0 := fun x => by
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    have h := telDer (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) D
      (fun x => y * x - x * y)
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, ← hA]; simp)
      (fun i x => by
        rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, ← hB]
        simp
        abel) f f' hf
    have e : (fun x => D (T f x)) =
        ⇑(T f') + fun x => ∑ k, T f (Function.update x k (y * x k - x k * y)) := by
      funext x
      simp only [hT, h, Pi.add_apply]
    rw [hα, hα, map_eps, e]
    refine ((epsL n).map_add _ _).trans ?_
    exact (congrArg (eps (T f') + ·) (epsDer M n (T f) y)).trans (add_zero _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AltFlip
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def UpperTheory.V.AlgRepEndIrreducible.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add (f := _), AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

theorem UpperTheory.V.AlgRepEndIrreducible.homot :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M),
      IsRetr κ L α → (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω) → ¬ HasCohomology κ L := by
  intro E _ _ _ a M _ _ _ _ κ L α hα hinf
  rintro (⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun Y => ?_)
    have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h4, hinf 0 ω h0 Z hZ Y]
      simp
    rw [← hα.retr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero, AlternatingMap.zero_apply]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := altFlip (ω.curryLeft ∘ₗ hp)
    have hF : ∀ Y X, F Y X = ω (Matrix.vecCons (hp X) Y) := fun _ _ => rfl
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine h2 (α.compAlternatingMap F) (fun k Y => ?_) (AlternatingMap.ext fun Y => ?_)
    · refine (hα.cpt k (F Y) (F fun i => adHerm k (Y i)) fun X => ?_).symm
      have e : hp (toL (k.1 * X * star k.1)) = adHerm k (hp (toL X)) := by
        apply Subtype.ext
        change _ = k.1 * (hp (toL X)).1 * star k.1
        rw [hp_val, hp_val, star_mul, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
          mul_assoc k.1 (star X)]
      rw [hF, hF, ← h0, e]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
        (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
      have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
        hα.lie _ _ _ fun X => (sub_add_cancel _ _).symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [dCo_apply, ← hα.retr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, ← h3]
        rfl
      · rw [LinearMap.sum_apply]
        exact homId E a M L q ω h1 (hinf _ ω h0) (Matrix.of X) Y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem qdet_negT {d n : ℕ} (X : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (h : Formalism.REAL.GlRel X) (u : ℂ) :
    Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2) =
      (-1 : ℂ) ^ n • (Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2))ᵀ := by
  have h1 := map_qdet (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2)
  have h2 := (glNegOp _ n X h).2 (u + ((n : ℂ) - 1) / 2)
  have e : (fun i j => (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (-(X i j)ᵀ)) =
      fun i j => -MulOpposite.op (X i j) := by
    funext i j
    simp
  have e' : (n : ℂ) - 1 - (u + ((n : ℂ) - 1) / 2) = -u + ((n : ℂ) - 1) / 2 := by ring
  rw [e, h2, e'] at h1
  have h3 : (Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2))ᵀ =
      (-1 : ℂ) ^ n • Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2) := MulOpposite.op_injective h1
  rw [← Matrix.transpose_smul, ← h3, Matrix.transpose_transpose]

private theorem prod_neg (m : Multiset ℂ) (u : ℂ) :
    ((m.map Neg.neg).map (-u + ·)).prod = (-1) ^ Multiset.card m * (m.map (u + ·)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

end UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

theorem UpperTheory.V.AlgRepEndIrreducible.dualIff :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ),
      UpperTheory.V.Af.AlgInfChar Ξ τ (m.map Neg.neg) ↔ GlobalTheory.WignerGL.HasDualInfChar Ξ τ m := by
  intro E _ _ _ a Ξ τ m
  have hR : Formalism.REAL.GlRel (eL Ξ.dmat τ) := (eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)).1 τ
  have hd : GlobalTheory.WignerGL.dualE Ξ τ = fun i j => -(eL Ξ.dmat τ i j)ᵀ := by
    funext i j
    exact dualE_eq Ξ τ i j
  have hs : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by rw [← mul_pow]; simp
  change (Multiset.card (m.map Neg.neg) = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (eL Ξ.dmat τ) (u + ((a : ℂ) - 1) / 2) =
    ((m.map Neg.neg).map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) ↔ _
  unfold GlobalTheory.WignerGL.HasDualInfChar
  rw [Multiset.card_map, hd]
  refine and_congr_right fun hm => ⟨fun h u => ?_, fun h u => ?_⟩
  · rw [QuantumDeterminantDual.qdet_negT _ hR, h, QuantumDeterminantDual.prod_neg, hm, Matrix.transpose_smul, Matrix.transpose_one, smul_smul,
      ← mul_assoc, hs, one_mul]
  · have h1 := congrArg (fun M => (-1 : ℂ) ^ a • Mᵀ) (h (-u))
    have h2 := QuantumDeterminantDual.prod_neg m (-u)
    simp only [QuantumDeterminantDual.qdet_negT _ hR, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one,
      smul_smul, hs, one_smul, neg_neg] at h1
    rw [neg_neg, hm] at h2
    rw [h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem exp_map_eval {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a))
    (Continuous.matrix_map continuous_id (continuous_apply w)) X

private theorem gen_pi {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  let e : Matrix (Fin a) (Fin a) (ι → ℂ) ≃+* (ι → Matrix (Fin a) (Fin a) ℂ) :=
    Matrix.piRingEquiv (β := fun _ : ι => ℂ)
  have he : ∀ X w, e X w = X.map (fun x => x w) := fun _ _ => rfl
  let H' : Submonoid (ι → Matrix (Fin a) (Fin a) ℂ) := H.comap (e.symm : _ →* _)
  have h1 : ∀ (w : ι) (g : Matrix (Fin a) (Fin a) ℂ), g.det ≠ 0 → Pi.mulSingle w g ∈ H' := by
    intro w g hg
    refine UpperTheory.V.AlgRepEndIrreducible.expGenC a (H'.comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)) ?_ g hg
    intro X
    change e.symm (Pi.mulSingle w (NormedSpace.exp X)) ∈ H
    have : e.symm (Pi.mulSingle w (NormedSpace.exp X)) = NormedSpace.exp (e.symm (Pi.single w X)) := by
      rw [RingEquiv.symm_apply_eq]
      funext v
      rw [he, exp_map_eval, ← he, RingEquiv.apply_symm_apply]
      by_cases hv : v = w
      · subst hv
        simp
      · simp [hv]
    rw [this]
    exact hH _
  have h2 : ∀ w, (e y w).det ≠ 0 := by
    intro w
    have : IsUnit (e y w) := (hy.map e).map (Pi.evalRingHom (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h3 : ∀ s : Finset ι, s.piecewise (e y) 1 ∈ H' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using H'.one_mem
    | insert w s hw ih =>
      have : (insert w s).piecewise (e y) 1 = Pi.mulSingle w (e y w) * s.piecewise (e y) 1 := by
        funext v
        by_cases hv : v = w
        · subst hv
          simp [Finset.piecewise, hw]
        · simp [Finset.piecewise, hv]
      rw [this]
      exact H'.mul_mem (h1 w _ (h2 w)) ih
  have h4 := h3 Finset.univ
  rw [Finset.piecewise_univ] at h4
  have h5 : e.symm (e y) ∈ H := h4
  simpa using h5

theorem UpperTheory.V.AlgRepEndIrreducible.expGen :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Submonoid (GL (Fin a) (Cinf E))),
      (∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)), y.val = NormedSpace.exp X → y ∈ H) → ∀ y, y ∈ H := by
  intro E _ _ _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_pi (ι := InfinitePlace E) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolMul
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem atEmb_add' {E : Type} [Field E] (τ : E →+* ℂ) (z w : ℂ) :
    atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

private noncomputable def atEmbHom {E : Type} [Field E] (τ : E →+* ℂ) : ℂ →+ Cinf E :=
  AddMonoidHom.mk' (atEmb τ) (atEmb_add' τ)

private theorem mul_atEmb_map {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    p * x.map (atEmb τ) = (p.map (coord τ) * x).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show atEmb τ (∑ k, coord τ (p i k) * x k j) = ∑ k, atEmb τ (coord τ (p i k) * x k j) from
    map_sum (atEmbHom τ) _ _]
  exact Finset.sum_congr rfl fun k _ => GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_mul {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    x.map (atEmb τ) * p = (x * p.map (coord τ)).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show atEmb τ (∑ k, x i k * coord τ (p k j)) = ∑ k, atEmb τ (x i k * coord τ (p k j)) from
    map_sum (atEmbHom τ) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (x i k)]
  exact GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_sub {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (x y : Matrix (Fin a) (Fin a) ℂ) :
    (x - y).map (atEmb τ) = x.map (atEmb τ) - y.map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.sub_apply, Matrix.map_apply]
  exact map_sub (atEmbHom τ) _ _

theorem UpperTheory.V.AlgRepEndIrreducible.holMul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N),
      (∀ p q : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (p * X * q))) →
        ∀ x, hol τ L' x = hol τ L (p.map (coord τ) * x * q.map (coord τ))) ∧
      ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (Y * X - X * Y))) →
        ∀ x, hol τ L' x = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ τ L L'
  refine ⟨fun p q h x => ?_, fun Y h x => ?_⟩
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← atEmb_map_sub, ← atEmb_map_sub, ← smul_sub]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HwIso
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.hwIso :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (F' : ι → Fin n → Fin n → Module.End ℂ V'),
      IsMultiGl F → IsMultiGl F' → (∀ W, Stab F W → W = ⊥ ∨ W = ⊤) → (∀ W, Stab F' W → W = ⊥ ∨ W = ⊤) →
      ∀ (ν : ι → Fin n → ℂ) (v : V) (v' : V'), v ≠ 0 → v' ≠ 0 → (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
        (∀ t, Formalism.REAL.IsHW (F' t) (ν t) v') → ∃ T : V ≃ₗ[ℂ] V', ∀ t i j x, T (F t i j x) = F' t i j (T x) := by
  intro ι V _ _ _ n F V' _ _ F' hF hF' hS hS' ν v v' hv0 hv0' hv hv'
  let P : ι → Fin n → Fin n → Module.End ℂ (V × V') := fun t i j => (F t i j).prodMap (F' t i j)
  have hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y) := fun _ _ _ _ _ => rfl
  have hP : IsMultiGl P := by
    refine ⟨fun t i j k l => ?_, fun s t hst i j k l => ?_⟩
    · refine LinearMap.ext fun z => ?_
      have e := LinearMap.congr_fun (hF.1 t i j k l) z.1
      have e' := LinearMap.congr_fun (hF'.1 t i j k l) z.2
      refine Prod.ext (e.trans ?_) (e'.trans ?_)
      · split_ifs <;> rfl
      · split_ifs <;> rfl
    · refine LinearMap.ext fun z => ?_
      exact Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1)
        (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)
  have hvv : ∀ t, Formalism.REAL.IsHW (P t) (ν t) (v, v') := fun t =>
    ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i),
      fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩
  obtain ⟨hm, hst⟩ := lowStab ι (V × V') n P hP ν (v, v') hvv
  have hl := lowLine ι (V × V') n P hP ν (v, v') hvv
  generalize low P (v, v') = W at hm hst hl
  have hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0 := by
    rcases hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inr_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : ((0 : V), v') ∈ W := (Submodule.eq_top_iff'.1 h v' :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.snd hc) hv0'
  have hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0 := by
    rcases hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inl_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : (v, (0 : V')) ∈ W := (Submodule.eq_top_iff'.1 h v :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.fst hc) hv0
  have hC : W.map (LinearMap.fst ℂ V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have hD : W.map (LinearMap.snd ℂ V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : x = 0)
      exact Subtype.ext (Prod.ext rfl (hA y hz))
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hC x
      exact ⟨⟨z, hz⟩, rfl⟩
  have b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : y = 0)
      exact Subtype.ext (Prod.ext (hB x hz) rfl)
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hD x
      exact ⟨⟨z, hz⟩, rfl⟩
  have key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2 := by
    intro z
    have : (LinearEquiv.ofBijective _ b1).symm z.1.1 = z := (LinearEquiv.ofBijective _ b1).symm_apply_apply z
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩
  obtain ⟨z, rfl⟩ := b1.2 x
  exact (key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)
end

