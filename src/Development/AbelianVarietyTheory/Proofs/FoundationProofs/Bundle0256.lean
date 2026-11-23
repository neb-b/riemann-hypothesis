module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeAgreeOfTrivialAtPrime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.LocAgree

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  have hinv : (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j =
      Formalism.UG.sigR (D.host.conj : D.host.E →ₐ[ℚ] D.host.E)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (((k : GL (Fin N) (AE D)) : Matrix _ _ _) j i) := by
    have hU := k.2
    change Formalism.UG.cT (Formalism.UG.sigR (D.host.conj : D.host.E →ₐ[ℚ] D.host.E)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ((k : GL (Fin N) (AE D)) : Matrix _ _ _) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (Formalism.UG.inclE (F := ℚ) (E := D.host.E) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
      ((k : GL (Fin N) (AE D)) : Matrix _ _ _) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (Formalism.UG.inclE (F := ℚ) (E := D.host.E) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) at hU
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hU
    have he := Units.inv_eq_of_mul_eq_one_left hU
    exact congrFun (congrFun he i) j
  rw [hinv]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((m : D.host.E) • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  show δ * embT D τ ((m : D.host.E) * z i j) = m • (δ * embT D τ (z i j))
  rw [map_mul, map_natCast, nsmul_eq_mul]
  ring

theorem matrix_move {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {N N' : ℕ} (g₁ g₂ : GL (Fin N) A)
    (g₁' g₂' : GL (Fin N') A) (s s' : ℕ) (z : Matrix (Fin N') (Fin N) R) :
    ((g₂'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * (((s * s' : ℕ) : R) • z).map f *
      (g₂ : Matrix (Fin N) (Fin N) A) =
      ((s' : A) • ((g₂'⁻¹ * g₁' : GL (Fin N') A) : Matrix (Fin N') (Fin N') A)) *
      (((g₁'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * z.map f * (g₁ : Matrix (Fin N) (Fin N) A)) *
      ((s : A) • ((g₁⁻¹ * g₂ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
  have e1 : (((s * s' : ℕ) : R) • z).map f = ((s : A) * (s' : A)) • z.map f := by
    ext i j
    simp
  rw [e1]
  simp only [Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g₁ : Matrix (Fin N) (Fin N) A), Units.mul_inv, Matrix.one_mul,
    ← Matrix.mul_assoc (g₁' : Matrix (Fin N') (Fin N') A), Units.mul_inv, Matrix.one_mul]

theorem smul_mem_La (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : cc ≠ ⊥) {N N' : ℕ}
    (g₁ g₂ : GA D N) (g₁' g₂' : GA D N')
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h₁ : Moves D (g₁ : GL (Fin N) (AE D)) L₁) (h₁' : Moves D (g₁' : GL (Fin N') (AE D)) L₁')
    (h₂ : Moves D (g₂ : GL (Fin N) (AE D)) L₂) (h₂' : Moves D (g₂' : GL (Fin N') (AE D)) L₂')
    (s s' : ℕ)
    (hs : ∀ i j, (s : AE D) * (((g₁ : GL (Fin N) (AE D))⁻¹ * (g₂ : GL (Fin N) (AE D)) : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (hs' : ∀ i j, (s' : AE D) * (((g₂' : GL (Fin N') (AE D))⁻¹ * (g₁' : GL (Fin N') (AE D)) : GL (Fin N') (AE D)) :
      Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D)
    (x : VC D N N') (hx : x ∈ La D (tor0 D cc δ) L₁ L₁') : (s * s') • x ∈ La D (tor0 D cc δ) L₂ L₂' := by
  obtain ⟨z, rfl, hz⟩ := _root_.GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hc N N' g₁ g₁' L₁ L₁' h₁ h₁' x hx
  rw [← pt_nsmul]
  refine _root_.GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hc N N' g₂ g₂' L₂ L₂' h₂ h₂' _ ?_
  have hI := (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hc).2.2
  intro i j
  rw [matrix_move (inc D) (g₁ : GL (Fin N) (AE D)) _ (g₁' : GL (Fin N') (AE D)), Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine hI _ (hs l j) _ ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun r _ => hI _ (hs' i r) _ (hz r l)

end GlobalTheory.NormSum.LocAgree


open GlobalTheory.NormSum.LocAgree in
theorem GlobalTheory.NormSum.La_agree_of_trivAt : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  intro D hG cc δ hc N N' q h k h' k' L₁ L₂ L₁' L₂' hk hk' h₁ h₁' h₂ h₂'
  obtain ⟨s, hsq, hs, hsi⟩ := exists_int_mul D q k hk
  obtain ⟨s', hsq', hs', hsi'⟩ := exists_int_mul D q k' hk'
  refine ⟨fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩,
    fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩⟩
  · refine smul_mem_La D hG cc δ hc h (h * k) h' (h' * k') h₁ h₁' h₂ h₂' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi'
  · refine smul_mem_La D hG cc δ hc (h * k) h (h' * k') h' h₂ h₂' h₁ h₁' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaLatImage

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem pt_apply (z : Matrix (Fin N') (Fin N) D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_zero : pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt_apply]

theorem pt_add (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt_apply, mul_add]

theorem pt_neg (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt_apply]

theorem pt_smulK (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    (δ * D.host.φ₀ (c : D.host.E)) • embV D (tor0 D cc δ) A =
      pt D (tor0 D cc δ) δ ((c : D.host.E) • A) := by
  funext τ i j
  change (δ * D.host.φ₀ (c : D.host.E)) * embT D τ (A i j) = δ * embT D τ ((c : D.host.E) * A i j)
  rw [map_mul, (GlobalTheory.InducedType.induced_type D).1.1 τ c, mul_assoc]

theorem pt_injective (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp⟩⟩
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  rw [pt_apply, pt_apply] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem mem_homL {L : Lat D N} {L' : Lat D N'} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul o A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem o (hA x hx)

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ i, IntE D (x i) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one, IntE, RingHom.mem_range]

theorem smul_mem_RL {L : Lat D N} {L' : Lat D N'} {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') :
    ((c : D.host.K) : D.host.E) • A ∈ RL D cc L L' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, B, hB, rfl⟩ := hA
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, a, ha, rfl⟩, B, hB, smul_smul _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul o A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ o hA

theorem La_sub {L : Lat D N} {L' : Lat D N'} {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨_, smul_mem_RL hc hA, pt_smulK _ _⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [zero_smul, pt_zero]⟩
    | add w w' _ _ h h' =>
      obtain ⟨z, hz, e⟩ := h
      obtain ⟨z', hz', e'⟩ := h'
      exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [add_smul, e, e', pt_add]⟩
    | neg w _ h =>
      obtain ⟨z, hz, e⟩ := h
      exact ⟨-z, Submodule.neg_mem _ hz, by rw [neg_smul, e, pt_neg]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, pt_zero.symm⟩
  | add w w' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [e, e', pt_add]⟩
  | neg w _ h =>
    obtain ⟨z, hz, e⟩ := h
    exact ⟨-z, Submodule.neg_mem _ hz, by rw [e, pt_neg]⟩

theorem pt_mem_La {L : Lat D N} {L' : Lat D N'} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ RL D cc L L') (o : 𝓞 D.host.E) :
    pt D (tor0 D cc δ) δ (o • z) ∈ La D (tor0 D cc δ) L L' := by
  induction hz using Submodule.span_induction generalizing o with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    induction ht using Submodule.span_induction generalizing o with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      rw [mul_smul, smul_comm, ← pt_smulK]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, _,
        Submodule.smul_mem _ o (Submodule.subset_span ⟨a, ha, A, hA, rfl⟩), rfl⟩
    | zero => rw [zero_smul, smul_zero, pt_zero]; exact zero_mem _
    | add t t' _ _ h h' => rw [add_smul, smul_add, pt_add]; exact add_mem (h o) (h' o)
    | smul o' t _ h => rw [smul_assoc, smul_smul]; exact h _
  | zero => rw [smul_zero, pt_zero]; exact zero_mem _
  | add t t' _ _ h h' => rw [smul_add, pt_add]; exact add_mem (h o) (h' o)
  | smul o' t _ h => rw [smul_smul]; exact h _

def colM (D : D7) {N N' : ℕ} (j : Fin N) :
    (Fin N' → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun i k => if k = j then v i else 0
  map_add' v w := by ext i k; by_cases h : k = j <;> simp [h]
  map_smul' a v := by ext i k; by_cases h : k = j <;> simp [h]

def rowM (D : D7) {N N' : ℕ} (i : Fin N') :
    (Fin N → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun k j => if k = i then v j else 0
  map_add' v w := by ext k j; by_cases h : k = i <;> simp [h]
  map_smul' a v := by ext k j; by_cases h : k = i <;> simp [h]

theorem map_span_mem {M M' : Type} [AddCommGroup M] [Module D.host.E M] [Module (𝓞 D.host.E) M]
    [IsScalarTower (𝓞 D.host.E) D.host.E M] [AddCommGroup M'] [Module D.host.E M']
    [Module (𝓞 D.host.E) M'] [IsScalarTower (𝓞 D.host.E) D.host.E M'] (f : M →ₗ[D.host.E] M')
    {S : Set M} {S' : Set M'} (h : ∀ x ∈ S, f x ∈ S') {x : M}
    (hx : x ∈ Submodule.span (𝓞 D.host.E) S) : f x ∈ Submodule.span (𝓞 D.host.E) S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o hx

theorem mem_RL_cols (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈
      Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y} := by
  constructor
  · intro hz j
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N' → D.host.E) :=
      { toFun := fun z i => z i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, f A, ?_, map_smul _ _ _⟩
    have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      refine mem_stdL.2 fun i => ?_
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h2 := mem_homL.1 hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · intro h
    have e : z = ∑ j, colM D j (fun i => z i j) := by
      ext i k
      simp [colM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun j _ => map_span_mem (colM D j) ?_ (h j)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, colM D j y, mem_homL.2 fun x hx => ?_, map_smul _ _ _⟩
    obtain ⟨o, ho⟩ := mem_stdL.1 hx j
    have : (colM D j y).mulVec x = o • y := by
      funext i
      simp [colM, Matrix.mulVec, dotProduct, ← ho, Algebra.smul_def, mul_comm]
    rw [this]
    exact L'.smul_mem o hy

theorem mem_RL_rows (L : Lat D N) (hL : SD D L) (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E)
      {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  have hs := ((sd_iff D L).1 hL).2.2
  constructor
  · intro hz i
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N → D.host.E) :=
      { toFun := fun z => z i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, fun j => D.host.conj (A i j), (hs _).2 fun x hx => ?_, ?_⟩
    · have h2 := (mem_stdL.1 (mem_homL.1 hA x hx) i).conj
      have e : hE D (fun j => D.host.conj (A i j)) x = D.host.conj (A.mulVec x i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hE, Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e]; exact h2
    · simp only [conj_conj]; rfl
  · intro h
    have e : z = ∑ i, rowM D i (z i) := by
      ext i k
      simp [rowM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => map_span_mem (rowM D i) ?_ (h i)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, rowM D i _, mem_homL.2 fun x hx => mem_stdL.2 fun k => ?_, map_smul _ _ _⟩
    by_cases hk : k = i
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = hE D x y := by
        simp [rowM, Matrix.mulVec, dotProduct, hk, hE, mul_comm]
      rw [e]; exact (hs x).1 hx y hy
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = 0 := by
        simp [rowM, Matrix.mulVec, dotProduct, hk]
      rw [e]; exact zero_mem _

theorem theta_lattice_image : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  intro D cc δ hδ N N'
  refine ⟨pt_injective hδ, fun L L' x => ⟨La_sub, ?_⟩, mem_RL_cols, mem_RL_rows⟩
  rintro ⟨z, hz, rfl⟩
  simpa using pt_mem_La (δ := δ) hz 1

end GlobalTheory.ThetaLatImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZero
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaTranslateCoef

theorem sum_trivial_char_eq_zero {G ι : Type} [Monoid G] [Fintype ι] (κ : ι → (G →* ℂ)) (c : ι → ℂ)
    (h : ∀ y, ∑ i, c i * κ i y = 0) : ∑ i, (if κ i = 1 then c i else 0) = 0 := by
  have li := linearIndependent_monoidHom G ℂ
  rw [linearIndependent_iff] at li
  have h0 := li (∑ i, Finsupp.single (κ i) (c i)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext y
    simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h y)
  have h1 := congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by congr

def kap (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (z : VC D N N') :
    Multiplicative A →* ℂ where
  toFun y := bc D T ((Multiplicative.toAdd y : A) : VC D N N') z / bc D T z ((Multiplicative.toAdd y : A) : VC D N N')
  map_one' := by
    simp only [toAdd_one, ZeroMemClass.coe_zero, bc_zero_left, bc_zero_right, div_one]
  map_mul' x y := by
    simp only [toAdd_mul, AddMemClass.coe_add, bc_add_left, bc_add_right, mul_div_mul_comm]

theorem kap_eq_one_iff {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (z : VC D N N') : kap D T A z = 1 ↔ z ∈ A := by
  constructor
  · intro hk
    refine h.2.2 z fun y hy => ?_
    have := DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))
    change bc D T y z / bc D T z y = 1 at this
    exact ((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm
  · intro hz
    refine MonoidHom.ext fun y => ?_
    change bc D T _ z / bc D T z _ = 1
    rw [h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]

theorem Wd_Wd_fixed (D : D7) (T : Tor D) {N N' : ℕ} (y z : VC D N N') (e : VC D N N' → ℂ)
    (he : Wd D T y e = e) : Wd D T y (Wd D T z e) = (bc D T y z / bc D T z y) • Wd D T z e := by
  have h1 := Wd_Wd D T z y e
  rw [he, add_comm] at h1
  rw [Wd_Wd]
  conv_rhs => rw [h1]
  rw [smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]

def WdL (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T y
  map_add' := Wd_add D T y
  map_smul' := Wd_smul D T y

theorem coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A →
    ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'),
      (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  intro D T N N' A hA e he hne ι _ a z hrel
  have hfix := ((hA.mem_ThSp e).1 he).2
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hsum : ∑ i, a i • Wd D T (z i) e = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel w
  have key := sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by
    intro y
    have h1 := congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    have h2 := congrFun h1 v
    rw [Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change _ = a i * Wd D T _ (Wd D T (z i) e) v
    rw [Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]
    change a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)
    ring)
  have h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0 := by
    refine Eq.trans ?_ key
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : z i ∈ A
    · rw [if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]
    · rw [if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]
  exact (mul_eq_zero.1 h3).resolve_right hv

end GlobalTheory.ThetaTranslateCoef
end
end

