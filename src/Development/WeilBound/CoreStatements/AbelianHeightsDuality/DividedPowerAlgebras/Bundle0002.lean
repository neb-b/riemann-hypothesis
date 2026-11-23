module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.WeilBound.LevelCriteria.IsLevOneIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompAdd
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

namespace Pre

open GlobalTheory.PDA.Model TensorProduct

variable {B : Type} [CommRing B]

def liftL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n)) : L →ₐ[ℤ] B :=
  AlgHom.ofLinearMap (bL.constr ℤ c) (by rw [← bL_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul ℤ L).compr₂ (bL.constr ℤ c) =
        (LinearMap.mul ℤ B).compl₁₂ (bL.constr ℤ c) (bL.constr ℤ c) := by
      refine bL.ext fun m ↦ bL.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, bL_mul]
      rw [← nsmul_eq_mul, map_nsmul, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftL_bL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n))
    (n : ℕ) : liftL c h0 hm (bL n) = c n := bL.constr_basis ℤ c n

theorem cancel {n : ℕ} (hn : n ≠ 0) {x y : L ⊗[ℤ] L} (h : (n : L ⊗[ℤ] L) * x = n * y) : x = y := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul] at h
  refine (bL.tensorProduct bL).repr.injective (Finsupp.ext fun i ↦ ?_)
  have := congrArg (fun z ↦ (bL.tensorProduct bL).repr z i) h
  simp only [map_nsmul, Finsupp.smul_apply] at this
  rw [nsmul_eq_mul, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) this

theorem fact_mul {D : Type} [CommRing D] (u : ℕ → D) (h0 : u 0 = 1)
    (hm : ∀ m n, u m * u n = ((m + n).choose m : D) * u (m + n)) (n : ℕ) :
    (n.factorial : D) * u n = u 1 ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [pow_succ', ← ih, mul_left_comm, hm, Nat.factorial_succ, add_comm 1 n]
    simp; ring

theorem fact_sum {D : Type} [CommRing D] (x y : D) (w w' : ℕ → D) (hw : ∀ k, (k.factorial : D) * w k = x ^ k)
    (hw' : ∀ k, (k.factorial : D) * w' k = y ^ k) (m : ℕ) :
    (m.factorial : D) * ∑ k ∈ Finset.HasAntidiagonal.antidiagonal m, w k.1 * w' k.2 = (x + y) ^ m := by
  rw [(Commute.all x y).add_pow', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k.1 + k.2 = m := by simpa using hk
  rw [← hw, ← hw', ← hk', ← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
  push_cast
  rw [nsmul_eq_mul]; ring

theorem eq_ub {D : Type} [CommRing D] (hc : ∀ {n : ℕ}, n ≠ 0 → ∀ {x y : D}, (n : D) * x = n * y → x = y)
    (t : D) (z : ℕ → D) (hz : ∀ k, (k.factorial : D) * z k = t ^ k) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (m.factorial : D) * ((m.uniformBell n : D) * z (m * n)) = z n ^ m := by
  refine hc (n := n.factorial ^ m) (by positivity) ?_
  have h := congrArg (Nat.cast : ℕ → D) (Nat.uniformBell_mul_eq m hn)
  push_cast at h ⊢
  rw [← mul_pow, hz, ← pow_mul, mul_comm n m, ← hz, ← h]; ring

theorem comp_add {J : Ideal B} {γ : ℕ → B → B} (H : IsPreDP J γ) {a b : B} (ha : a ∈ J) (hb : b ∈ J)
    (ka : ∀ m n : ℕ, n ≠ 0 → γ m (γ n a) = (m.uniformBell n : B) * γ (m * n) a)
    (kb : ∀ m n : ℕ, n ≠ 0 → γ m (γ n b) = (m.uniformBell n : B) * γ (m * n) b) (m n : ℕ) (hn : n ≠ 0) :
    γ m (γ n (a + b)) = (m.uniformBell n : B) * γ (m * n) (a + b) := by
  let u : ℕ → L ⊗[ℤ] L := fun k ↦ bL k ⊗ₜ 1
  let v : ℕ → L ⊗[ℤ] L := fun k ↦ 1 ⊗ₜ bL k
  have hu : ∀ k, (k.factorial : L ⊗[ℤ] L) * u k = u 1 ^ k := fact_mul u (by simp only [u, bL_zero]; rfl) fun i j ↦ by
    simp only [u, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, smul_tmul']
  have hv : ∀ k, (k.factorial : L ⊗[ℤ] L) * v k = v 1 ^ k := fact_mul v (by simp only [v, bL_zero]; rfl) fun i j ↦ by
    simp only [v, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]
  let ψ : L ⊗[ℤ] L →ₐ[ℤ] B := Algebra.TensorProduct.lift
    (liftL (fun k ↦ γ k a) (H.zero a ha) fun i j ↦ H.mul_dpow i j a ha)
    (liftL (fun k ↦ γ k b) (H.zero b hb) fun i j ↦ H.mul_dpow i j b hb) fun _ _ ↦ Commute.all _ _
  have ψu : ∀ k, ψ (u k) = γ k a := fun k ↦ by simp [ψ, u, liftL_bL]
  have ψv : ∀ k, ψ (v k) = γ k b := fun k ↦ by simp [ψ, v, liftL_bL]
  let W : Ideal (L ⊗[ℤ] L) :=
    { carrier := {z | ψ z ∈ J ∧ ∀ k : ℕ, ∃ w, (k.factorial : L ⊗[ℤ] L) * w = z ^ k ∧ ψ w = γ k (ψ z)}
      zero_mem' := ⟨by simp, fun k ↦ by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨1, by simp, by rw [map_one, map_zero, H.zero _ J.zero_mem]⟩
        · refine ⟨0, by simp [hk.ne'], ?_⟩
          have := H.mul k 0 0 J.zero_mem
          rw [mul_zero, zero_pow hk.ne', zero_mul] at this
          rw [map_zero, this]⟩
      add_mem' := fun {x y} hx hy ↦ ⟨by rw [map_add (f := _)]; exact J.add_mem hx.1 hy.1, fun k ↦ by
        choose w hw hw' using hx.2
        choose w₁ hw₁ hw₁' using hy.2
        refine ⟨_, fact_sum x y w w₁ hw hw₁ k, ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), H.add k _ hx.1 _ hy.1, map_sum]
        simp only [map_mul, hw', hw₁']⟩
      smul_mem' := fun c x hx ↦ ⟨by rw [smul_eq_mul, map_mul]; exact J.mul_mem_left _ hx.1, fun k ↦ by
        obtain ⟨w, hw, hw'⟩ := hx.2 k
        refine ⟨c ^ k * w, by rw [smul_eq_mul, mul_pow, ← hw]; ring, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, H.mul _ _ _ hx.1, hw', map_pow]⟩ }
  have uW : ∀ i, i ≠ 0 → u i ∈ W := fun i hi ↦ ⟨by rw [ψu]; exact H.mem i hi a ha, fun k ↦
    ⟨_, eq_ub cancel _ u hu k hi, by rw [map_mul, map_natCast, ψu, ψu, ka k i hi]⟩⟩
  have vW : ∀ i, i ≠ 0 → v i ∈ W := fun i hi ↦ ⟨by rw [ψv]; exact H.mem i hi b hb, fun k ↦
    ⟨_, eq_ub cancel _ v hv k hi, by rw [map_mul, map_natCast, ψv, ψv, kb k i hi]⟩⟩
  let z : ℕ → L ⊗[ℤ] L := fun k ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, u p.1 * v p.2
  have hz : ∀ k, (k.factorial : L ⊗[ℤ] L) * z k = (u 1 + v 1) ^ k := fact_sum _ _ u v hu hv
  have ψz : ∀ k, ψ (z k) = γ k (a + b) := fun k ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [H.add k a ha b hb, map_sum]; simp only [map_mul, ψu, ψv]
  have zW : z n ∈ W := Ideal.sum_mem _ fun p hp ↦ by
    have hp' : p.1 + p.2 = n := by simpa using hp
    by_cases h : p.1 = 0
    · exact W.mul_mem_left _ (vW _ (by omega))
    · exact W.mul_mem_right _ (uW _ h)
  obtain ⟨w, hw, hw'⟩ := zW.2 m
  have e := cancel m.factorial_ne_zero (hw.trans (eq_ub cancel _ z hz m hn).symm)
  rw [← ψz n, ← hw', e, map_mul, map_natCast, ψz]

end Pre

theorem dp_of_pre' : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s H hs h
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    subst hs
    have smul : ∀ c, ∀ x ∈ Ideal.span s, (∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
        ∀ m n : ℕ, n ≠ 0 → γ m (γ n (c * x)) = (m.uniformBell n : B) * γ (m * n) (c * x) := by
      intro c x hx ih m n hn
      rw [H.mul n c x hx, H.mul m _ _ (H.mem n hn x hx), ih m n hn, H.mul _ c x hx, ← pow_mul, mul_comm n m]
      ring
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero =>
      intro m n hn
      have z : ∀ k, k ≠ 0 → γ k 0 = 0 := fun k hk ↦ by
        have := H.mul k 0 0 (Ideal.zero_mem _)
        rwa [mul_zero, zero_pow hk, zero_mul] at this
      rw [z n hn]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Nat.uniformBell_zero_left]
      · rw [z m hm.ne', z _ (Nat.mul_ne_zero hm.ne' hn), mul_zero]
    | add x y hx hy ihx ihy => exact Pre.comp_add H hx hy ihx ihy
    | smul c x hx ih => exact smul c x hx ih
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ H.null _ _ hx
           dpow_zero := fun hx ↦ H.zero _ hx
           dpow_one := fun hx ↦ H.one _ hx
           dpow_mem := fun hn hx ↦ H.mem _ hn _ hx
           dpow_add := fun hx hy ↦ H.add _ _ hx _ hy
           dpow_mul := fun hx ↦ H.mul _ _ _ hx
           mul_dpow := fun hx ↦ H.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end FubiniStudyChowHeightFormula₂.Adr
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr.Fil

variable {B : Type} [CommRing B]

def liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    liftAlg Q c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem exists_lift (Q : PDPoly B) (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) :
    ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n := by
  letI := f.toAlgebra
  exact ⟨(liftAlg Q c h0 hm).toRingHom, fun b ↦ (liftAlg Q c h0 hm).commutes b, fun n ↦ liftAlg_e Q c h0 hm n⟩

theorem fil_isSubDPIdeal {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (hN : 1 ≤ N) :
    δ.IsSubDPIdeal (fil δ N) := by
  refine ⟨ExpBij.dpFil_le δ hN, fun n hn j hj ↦ ?_⟩
  have h := ExpBij.dpow_mem_dpFil_mul δ hN hj n
  exact ExpBij.dpFil_anti δ (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hn)) h

theorem nil_of_lev {J : Ideal B} {δ : DividedPowers J} {n : ℕ} (h : IsLev δ n) : IsNilDP δ :=
  ⟨n, fun l h1 h2 ↦ by
    have : _ ∈ fil δ n := Ideal.subset_span ⟨l, h1, h2, rfl⟩
    rwa [show fil δ n = ⊥ from h, Ideal.mem_bot] at this⟩

theorem exists_quot {J : Ideal B} (δ : DividedPowers J) (𝔟 : Ideal B) (h𝔟 : δ.IsSubDPIdeal 𝔟) :
    ∃ δ' : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)), IsDPMorphism δ δ' (Ideal.Quotient.mk 𝔟) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C),
        IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟)) → IsDPMorphism δ' δ'' g := by
  have hinf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
    rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟
  refine ⟨Quotient.dividedPowers δ hinf, Quotient.isDPMorphism δ hinf, ?_⟩
  intro C _ J'' δ'' g hg
  refine ⟨?_, fun {n} y hy ↦ ?_⟩
  · rw [Ideal.map_map]; exact hg.1
  · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    rw [Quotient.dpow_apply δ hinf ha]
    exact hg.2 a ha


omit [CommRing B] in
theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm


omit [CommRing B] in
theorem fil_le_map_fil : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C]
    (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f →
    ∀ N, fil δ' N ≤ (fil δ N).map f := by
  intro B _ J δ C _ J' δ' f hf hJ N
  subst hJ
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_le.2 fun x hx y hy ↦ ExpBij.mul_mem_dpFil δ hx hy)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [show fil δ 0 = ⊤ from eq_top_iff.2 fun a _ ↦ ExpBij.mem_dpFil_zero δ a, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (ExpBij.dpow_mem_dpFil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (ExpBij.dpFil_anti δ h2) (hprod l h1)

end FubiniStudyChowHeightFormula₂.Adr.Fil
end
end

