module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section P

variable {A : Type} (R : Type) [CommRing A] [CommRing R] [Algebra A R] {e n : ℕ}

private def PP (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) (DD R e) :=
  Matrix.of fun a b => ⟨algebraMap A R (M a b), fun j => algebraMap A R (Z j a b), 0, 0⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem congruenceCondition_mul (M M' : Matrix (Fin n) (Fin n) A) (Z Z' : Fin e → Matrix (Fin n) (Fin n) A) :
    PP R M Z * PP R M' Z' = PP R (M * M') (fun j => M * Z' j + Z j * M') := by
  ext a b j <;> simp [PP, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta, Finset.sum_add_distrib]

private theorem pair_matrix_transpose (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (PP R M Z)ᵀ = PP R Mᵀ (fun j => (Z j)ᵀ) := rfl

private theorem PP_map (M : Matrix (Fin n) (Fin n) A) :
    M.map (algebraMap A (DD R e)) = PP R M (fun _ => 0) := by
  ext a b j
  · rfl
  · simp only [PP, Matrix.of_apply, Matrix.zero_apply, map_zero]; rfl
  · rfl
  · rfl

private theorem PP_one : PP R (1 : Matrix (Fin n) (Fin n) A) (fun _ : Fin e => 0) = 1 := by
  rw [← PP_map]; exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem PP_add (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 + DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 Z := by
  rw [← PP_one (A := A) R]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_sub (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 - DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 (fun j => -Z j) := by
  rw [← PP_one (A := A) R, sub_eq_add_neg]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_apply (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) (a b : Fin n)
    (h : ∀ j, Z j a b = 0) : PP R M Z a b = algebraMap A (DD R e) (M a b) := by
  have := congrFun (congrFun (PP_map R (e := e) M) a) b
  rw [Matrix.map_apply] at this
  rw [this]
  simp [PP, h]

private theorem od_ev {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    Z * M ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ i k).1 hk), zero_mul]
  · rw [(Submodule.mem_bot A).1 ((hM k j).2 (by tauto)), mul_zero]

private theorem ev_od {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    M * Z ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ k j).1 (by tauto)), mul_zero]
  · rw [(Submodule.mem_bot A).1 ((hM i k).2 hk), zero_mul]

private theorem tri_mul {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    ∀ i j, j < i → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (lt_of_lt_of_le hij (not_lt.1 hk)), mul_zero]

end P

section K

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (R : Type) [CommRing R] [Algebra x.A R]

private theorem ρ1_eq (g : F.G₀) : k.ρ1 R g = PP R (x.ρX x.A g) (fun j => k.κ j g * x.ρX x.A g) := by
  have : x.ρX (DD R k.g) g = PP R (x.ρX x.A g) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.ρ1, PP_add, this, congruenceCondition_mul]; simp

private theorem weyl_lift_eq_pair (v) : k.w1 R v = PP R (x.wX x.A v) (fun j => -(k.Y j v * x.wX x.A v)) := by
  have : x.wX (DD R k.g) v = PP R (x.wX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.w1, PP_sub, this, congruenceCondition_mul]; simp

private theorem inverse_weyl_lift_eq_pair (v) : k.wi1 R v = PP R (x.wiX x.A v) (fun j => x.wiX x.A v * k.Y j v) := by
  have : x.wiX (DD R k.g) v = PP R (x.wiX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.wi1, PP_add, this, congruenceCondition_mul]; simp

end K

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rho1Tri :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (R : Type) [CommRing R] [Algebra x.A R], (∀ g g', k.ρ1 R (g * g') = k.ρ1 R g * k.ρ1 R g') ∧ k.ρ1 R 1 = 1 ∧ (∀ g, (k.ρ1 R g)ᵀ * k.ρ1 R (G0.frame.conj g) = algebraMap x.A (DD R k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD R k.g))) ∧ (∀ w, ∀ g ∈ G0.frame.Iu w, k.ρ1 R g = 1) ∧ (∀ g, k.ρ1 R g ∈ W1 n x.A R k.g x.a) ∧ ∀ v, k.w1 R v * k.wi1 R v = 1 ∧ k.wi1 R v * k.w1 R v = 1 ∧ ∀ g, (∀ i j, j < i → (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i j = 0) ∧ ∀ i, (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i i = algebraMap x.A (DD R k.g) (x.ψ v i g) := by
  intro l _ L G G0 h n x k R _ _
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := fun g => rfl
  have hmul : ∀ g g', x.ρX x.A (g * g') = x.ρX x.A g * x.ρX x.A g' := by
    intro g g'; simp [hρ, mat]
  have hone : x.ρX x.A 1 = 1 := by simp [hρ, mat]
  have hinv : ∀ g, x.ρX x.A g⁻¹ * x.ρX x.A g = 1 := by
    intro g; rw [← hmul, inv_mul_cancel, hone]
  have hev : ∀ g, x.ρX x.A g ∈ Ev x.A x.A n x.a := x.blk
  have hform : ∀ g, (x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g) =
      ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g
    have := x.form g
    rw [Units.val_one, Matrix.mul_one] at this
    exact this
  refine ⟨fun g g' => ?_, ?_, fun g => ?_, fun w g hg => ?_, fun g => ?_, fun v => ?_⟩
  · rw [ρ1_eq, ρ1_eq, ρ1_eq, congruenceCondition_mul, hmul]
    congr 1
    funext j
    rw [(k.mem j).2.2.1 g g', add_mul, add_comm, Matrix.mul_assoc (_ * _), ← Matrix.mul_assoc (x.ρX x.A g⁻¹), hinv]
    simp only [Matrix.mul_assoc, Matrix.one_mul]
  · rw [ρ1_eq, hone, ← PP_one (A := x.A) R]
    congr 1
    funext j
    have := (k.mem j).2.2.1 1 1
    simp only [mul_one, inv_one, hone, one_mul] at this
    rw [mul_one]
    exact left_eq_add.1 this
  · rw [ρ1_eq, ρ1_eq, pair_matrix_transpose, congruenceCondition_mul, hform]
    have : (fun j => (x.ρX x.A g)ᵀ * (k.κ j (G0.frame.conj g) * x.ρX x.A (G0.frame.conj g)) +
        (k.κ j g * x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g)) = fun _ => 0 := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, ← PP_map]
    ext1 a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [ρ1_eq, ← PP_one (A := x.A) R]
    have : x.ρX x.A g = 1 := by simp [hρ, mat, x.ine w g hg]
    rw [this]
    congr 1
    funext j
    rw [(k.mem j).2.2.2.2.1 w g hg, zero_mul]
  · rw [ρ1_eq]
    intro a b
    refine ⟨fun hab => ⟨by simp, fun _ => ?_, fun _ => rfl, fun _ => rfl⟩,
      fun hab => ⟨fun _ => ?_, by simp, fun _ => rfl, fun _ => rfl⟩⟩
    · funext j
      have := (Submodule.mem_bot _).1 ((od_ev ((k.mem j).1 g) (hev g) a b).1 hab)
      simp [PP, this]
    · have := (Submodule.mem_bot _).1 ((hev g a b).2 hab)
      simp [PP, this]
  · obtain ⟨h1, h2, h3, h4, -⟩ := oddDiag l L G G0 h n x x.A v
    refine ⟨?_, ?_, fun g => ?_⟩
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h1, ← PP_one (A := x.A) R]
      congr 1
      funext j
      rw [← Matrix.mul_assoc, h1, neg_mul, Matrix.mul_assoc, h1]; simp
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h2, ← PP_one (A := x.A) R]
      congr 1
      funext j
      simp [Matrix.mul_assoc]
    · set r := x.ρX x.A (G0.φ v g) with hr
      have key : k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v = PP R (x.wiX x.A v * r * x.wX x.A v)
          (fun j => x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v) := by
        rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, ρ1_eq, congruenceCondition_mul, congruenceCondition_mul]
        congr 1
        funext j
        rw [← hr]
        noncomm_ring
      rw [key]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · rw [PP_apply, (h4 g).1 a b hab, map_zero]
        intro j
        have e : x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v =
            (x.wiX x.A v * (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * x.wX x.A v) *
              (x.wiX x.A v * r * x.wX x.A v) := by
          have e1 : (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * r =
              k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v := by
            rw [dY, sub_mul, sub_mul, Matrix.mul_assoc _ _ r, hr, hinv, mul_one]; abel
          rw [← e1]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (x.wX x.A v), h1, one_mul]
        rw [e]
        exact tri_mul (k.loc j v g).1 (h4 g).1 a b hab
      · rw [PP_apply, (h4 g).2 a]
        · rfl
        intro j
        refine h3 _ ?_ a
        exact Submodule.sub_mem _ (Submodule.add_mem _ (od_ev ((k.mem j).1 _) (hev _)) (od_ev (k.Y_mem j v) (hev _)))
          (ev_od (k.Y_mem j v) (hev _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LaInj
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.laInj :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ μ ∈ S.La, S.laC μ ∈ BdM S.h S.x S.F → μ = 0 := by
  intro l _ S μ hμ hB
  obtain ⟨Y, -, -, hY⟩ := hB
  obtain ⟨-, p2, p3, p4, -⟩ := prAdd l S
  have hμ' : ∀ (b : S.Bh) y, μ (b • y) = S.rF b * μ y := hμ
  have hinv : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1 := by
    intro g
    simp only [Ctx.ρ, NP.ρX, mat]
    rw [← Matrix.map_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ∀ y : S.U.N, S.pr0 (y : S.U.AA) = 0 ∧ S.pr1 (y : S.U.AA) = y := by
    intro y
    simpa using p2 0 y
  have h0 : S.pr0 0 = 0 ∧ S.pr1 0 = 0 := hN 0
  have key : ∀ Z ∈ Submodule.span S.Bh (Set.range S.U.vr),
      Z.map (fun a => μ (S.pr1 a)) =
        Z.map (fun a => S.rF (S.pr0 a)) * Y - Y * Z.map (fun a => S.rF (S.pr0 a)) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      have e0 : (S.U.vr g).map (fun a => S.rF (S.pr0 a)) = S.ρ S.F g := by
        ext i j; exact (prVr l S g i j).1
      have e1 : (S.U.vr g).map (fun a => μ (S.pr1 a)) * S.ρ S.F g⁻¹ =
          S.ρ S.F g * Y * S.ρ S.F g⁻¹ - Y := congrFun hY g
      have e2 := congrArg (· * S.ρ S.F g) e1
      simp only [Matrix.mul_assoc, Matrix.sub_mul, hinv, Matrix.mul_one] at e2
      rw [e0, e2]
    | zero =>
      have a0 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => S.rF (S.pr0 a)) = 0 := by
        ext i j; simp [h0.1]
      have a1 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => μ (S.pr1 a)) = 0 := by
        ext i j; simp [h0.2]
      rw [a0, a1]; simp
    | add Z Z' _ _ h h' =>
      have a0 : (Z + Z').map (fun a => S.rF (S.pr0 a)) =
          Z.map (fun a => S.rF (S.pr0 a)) + Z'.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p3 _ _).1]
      have a1 : (Z + Z').map (fun a => μ (S.pr1 a)) =
          Z.map (fun a => μ (S.pr1 a)) + Z'.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p3 _ _).2]
      rw [a0, a1, h, h', Matrix.add_mul, Matrix.mul_add]; abel
    | smul b Z _ h =>
      have a0 : (b • Z).map (fun a => S.rF (S.pr0 a)) = S.rF b • Z.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p4 _ _).1]
      have a1 : (b • Z).map (fun a => μ (S.pr1 a)) = S.rF b • Z.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p4 _ _).2, hμ']
      rw [a0, a1, h, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  ext y
  rcases S.x.a_le.eq_or_lt with ha | ha
  · have hy : y = 0 := by
      apply Subtype.ext
      exact (S.U.typeI ha).le y.2
    rw [hy, map_zero, map_zero]
  · have hp := S.x.a_pos
    let i : Fin S.n := ⟨0, by omega⟩
    let j : Fin S.n := ⟨S.x.a, ha⟩
    have hm : Matrix.single i j (y : S.U.AA) ∈ Submodule.span S.Bh (Set.range S.U.vr) := by
      rw [S.U.span]
      intro i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        refine ⟨fun e => ?_, fun _ => by simp⟩
        exact absurd (e.1 (by simp only [i]; omega)) (by simp [j])
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ e]
        exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    have a0 : (Matrix.single i j (y : S.U.AA)).map (fun a => S.rF (S.pr0 a)) = 0 := by
      ext i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        simp [(hN y).1]
      · simp [Matrix.single_apply_of_ne _ _ _ _ _ e, h0.1]
    have k := key _ hm
    rw [a0] at k
    have k' := congrFun (congrFun k i) j
    simpa [(hN y).2] using k'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LiftsSub
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A)
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
  (V : Submodule A (Matrix (Fin n) (Fin n) R))

end

private theorem C_smul_mem_w2 {n : ℕ} {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {e a : ℕ}
    (c : X) (M : Matrix (Fin n) (Fin n) (DD X e)) (hM : M ∈ W2 n A X e a) :
    (DD.C c : DD X e) • M ∈ W2 n A X e a := by
  simp only [W2, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hM ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hM i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · obtain ⟨p, q, r, s⟩ := h1 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]
  · obtain ⟨p, q, r, s⟩ := h2 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]

private theorem smul_add_smul_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (d₁ d₂ : R) (hd₁ : ∀ M ∈ V, d₁ • M ∈ V) (hd₂ : ∀ M ∈ V, d₂ • M ∈ V)
    (z₁ z₂ : F.G₀ → Matrix (Fin n) (Fin n) R) (h₁ : z₁ ∈ SelZ F t ρ w wi V) (h₂ : z₂ ∈ SelZ F t ρ w wi V) :
    (fun g => d₁ • z₁ g + d₂ • z₂ g) ∈ SelZ F t ρ w wi V := by
  obtain ⟨a1, b1, c1, e1, f1, g1⟩ := h₁
  obtain ⟨a2, b2, c2, e2, f2, g2⟩ := h₂
  refine ⟨fun g => V.add_mem (hd₁ _ (a1 g)) (hd₂ _ (a2 g)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    have k1 := (b1 i j N).comp (fun q => Ideal.Quotient.mk _ d₁ * q)
    have k2 := (b2 i j N).comp (fun q => Ideal.Quotient.mk _ d₂ * q)
    convert k1.add k2 using 1
    funext g
    simp [Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_mul]
  · intro g g'
    simp only [c1, c2, smul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add]
    abel
  · intro g
    simp only [e1, e2, Matrix.transpose_add, Matrix.transpose_smul, smul_neg, neg_add]
  · intro u g hg
    simp [f1 u g hg, f2 u g hg]
  · intro v
    obtain ⟨Y1, hY1, L1⟩ := g1 v
    obtain ⟨Y2, hY2, L2⟩ := g2 v
    refine ⟨d₁ • Y1 + d₂ • Y2, V.add_mem (hd₁ _ hY1) (hd₂ _ hY2), ?_⟩
    intro γ
    obtain ⟨p1, q1⟩ := L1 γ
    obtain ⟨p2, q2⟩ := L2 γ
    have key : wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v
        = d₁ • (wi v * (z₁ (F.φ v γ) - dY F ρ Y1 (F.φ v γ)) * w v)
          + d₂ • (wi v * (z₂ (F.φ v γ) - dY F ρ Y2 (F.φ v γ)) * w v) := by
      simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_sub, smul_add]
      abel
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i j = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, p1 i j hij, p2 i j hij]
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i i = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, q1 hg i, q2 hg i]

private theorem zero_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) :
    (0 : F.G₀ → Matrix (Fin n) (Fin n) R) ∈ SelZ F t ρ w wi V := by
  refine ⟨fun g => V.zero_mem, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
    exact IsLocallyConstant.const 0
  · intro g g'
    simp
  · intro g
    simp
  · intro u g hg
    rfl
  · intro v
    refine ⟨0, V.zero_mem, fun γ => ⟨fun i j hij => ?_, fun hg i => ?_⟩⟩ <;> simp [dY]

private theorem bndF_mul_add_mul (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (c₁ c₂ : FractionRing (PowerSeries K)) (φ ψ : G → FractionRing (PowerSeries K))
    (h1 : BndF (PowerSeries.X : PowerSeries K) φ) (h2 : BndF (PowerSeries.X : PowerSeries K) ψ) :
    BndF (PowerSeries.X : PowerSeries K) (fun g => c₁ * φ g + c₂ * ψ g) := by
  obtain ⟨hc, hop, -⟩ := bndOps K G
  exact (hop _ _ (hop _ _ (hc c₁) h1).2.1 (hop _ _ (hc c₂) h2).2.1).1

private theorem bndD_C_smul_add_C_smul {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {n e : ℕ} (c₁ c₂ : FractionRing (PowerSeries K))
    (Ψ₁ Ψ₂ : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e))
    (h1 : BndD (PowerSeries.X : PowerSeries K) Ψ₁) (h2 : BndD (PowerSeries.X : PowerSeries K) Ψ₂) :
    BndD (PowerSeries.X : PowerSeries K)
      (fun g => (DD.C c₁ : DD (FractionRing (PowerSeries K)) e) • Ψ₁ g + (DD.C c₂ : DD _ e) • Ψ₂ g) := by
  intro i j
  obtain ⟨a1, b1, p1, e1⟩ := h1 i j
  obtain ⟨a2, b2, p2, e2⟩ := h2 i j
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_a, DD.mul_a, DD.C_a] using
      bndF_mul_add_mul K G c₁ c₂ _ _ a1 a2
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep, DD.mul_ep, DD.C_a, DD.C_ep] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (b1 k) (b2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep'] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (p1 k) (p2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_eta, DD.mul_eta, DD.C_a, DD.C_ep, DD.C_ep',
      DD.C_eta] using bndF_mul_add_mul K G c₁ c₂ _ _ e1 e2

theorem UpperTheory.V.Pa.liftsSub :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), Lifts h k 0 ∧ (∀ z z' : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr, Lifts h k z → Lifts h k z' → Lifts h k (z + z')) ∧ ∀ (c : x.Fr) (z : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), Lifts h k z → Lifts h k (c • z) := by
  intro l _ L G G0 h n x k
  have hV : ∀ (c : x.Fr), ∀ M ∈ W2 n x.A x.Fr k.g x.a, (DD.C c : DD x.Fr k.g) • M ∈ W2 n x.A x.Fr k.g x.a :=
    fun c M hM => C_smul_mem_w2 c M hM
  have lin : ∀ (c₁ c₂ : x.Fr) (z₁ z₂ : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr),
      Lifts h k z₁ → Lifts h k z₂ → Lifts h k (fun j γ => c₁ • z₁ j γ + c₂ • z₂ j γ) := by
    rintro c₁ c₂ z₁ z₂ ⟨Ψ₁, m1, b1, e1⟩ ⟨Ψ₂, m2, b2, e2⟩
    refine ⟨fun γ => (DD.C c₁ : DD x.Fr k.g) • Ψ₁ γ + (DD.C c₂ : DD x.Fr k.g) • Ψ₂ γ,
      smul_add_smul_mem_selZ _ _ _ _ _ _ _ _ (hV c₁) (hV c₂) _ _ m1 m2, bndD_C_smul_add_C_smul c₁ c₂ _ _ b1 b2, ?_⟩
    intro j γ a b
    simp [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep', e1 j γ a b, e2 j γ a b]
  refine ⟨?_, fun z z' hz hz' => ?_, fun c z hz => ?_⟩
  · refine ⟨0, zero_mem_selZ _ _ _ _ _ _, ?_, ?_⟩
    · intro i j
      obtain ⟨hc, -⟩ := bndOps x.K G.frame.G₀
      refine ⟨by simpa using hc 0, fun _ => by simpa using hc 0, fun _ => by simpa using hc 0, by simpa using hc 0⟩
    · intro j γ a b
      simp
  · convert lin 1 1 z z' hz hz' using 1
    funext j γ
    simp
  · convert lin c 0 z z hz hz using 1
    funext j γ
    simp
end

