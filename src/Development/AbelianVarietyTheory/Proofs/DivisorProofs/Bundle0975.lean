module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TorCls.OpenP

theorem mem_range_map_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (X : GL (Fin n) R)
    (h1 : ∀ i j, (X : Matrix (Fin n) (Fin n) R) i j ∈ S)
    (h2 : ∀ i j, ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ S) :
    X ∈ (GeneralLinearGroup.map S.subtype).range := by
  let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hA : A.map S.subtype = (X : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have hB : B.map S.subtype = ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.mul_inv)
  have hBA : B * A = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.inv_mul)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : L) :
    ∃ N : ℕ, (((p : L) ^ N * x : L) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (‖(x : PadicAlgCl p)‖ + 1) by positivity) hp
  refine ⟨N, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 ?_⟩
  have e : (((p : L) ^ N * x : L) : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (x : PadicAlgCl p) := by
    simp
  rw [e, norm_mul, norm_pow]
  have h0 : 0 ≤ ‖(x : PadicAlgCl p)‖ := norm_nonneg _
  calc ‖(p : PadicAlgCl p)‖ ^ N * ‖(x : PadicAlgCl p)‖ ≤ 1 / (‖(x : PadicAlgCl p)‖ + 1) * (‖(x : PadicAlgCl p)‖ + 1) :=
        mul_le_mul hN.le (by linarith) h0 (by positivity)
    _ = 1 := by field_simp

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r N : ℕ) :
    (p : KQ p K r) ^ N ∈ intKQ p K r :=
  pow_mem (natCast_mem _ p) N

theorem inclK_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : K)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclK p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨x, h⟩, rfl⟩)

theorem inclQ_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : Qr p r)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclQ p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨x, h⟩, rfl⟩)

theorem tmul_eq_inclK_mul_inclQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) (b : Qr p r) :
    (show KQ p K r from a ⊗ₜ[ℚ_[p]] b) = inclK p K r a * inclQ p K r b := by
  change a ⊗ₜ[ℚ_[p]] b = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_pow_mul_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r) :
    ∃ N : ℕ, (p : KQ p K r) ^ N * x ∈ intKQ p K r := by
  refine TensorProduct.induction_on (R := ℚ_[p]) (M := K) (N := Qr p r)
    (motive := fun y : K ⊗[ℚ_[p]] Qr p r => ∃ N : ℕ, (p : KQ p K r) ^ N * (show KQ p K r from y) ∈ intKQ p K r) x
    ⟨0, ?_⟩ ?_ ?_
  · change (p : KQ p K r) ^ 0 * (0 : KQ p K r) ∈ intKQ p K r
    rw [mul_zero]; exact zero_mem _
  · intro a b
    obtain ⟨N₁, h₁⟩ := exists_pow_mul_mem p K a
    obtain ⟨N₂, h₂⟩ := exists_pow_mul_mem p (Qr p r) b
    refine ⟨N₁ + N₂, ?_⟩
    rw [tmul_eq_inclK_mul_inclQ]
    have e : (p : KQ p K r) ^ (N₁ + N₂) * (inclK p K r a * inclQ p K r b) =
        inclK p K r ((p : K) ^ N₁ * a) * inclQ p K r ((p : Qr p r) ^ N₂ * b) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, pow_add]; ring
    rw [e]
    exact mul_mem (inclK_mem_intKQ p K r _ h₁) (inclQ_mem_intKQ p K r _ h₂)
  · rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    change (p : KQ p K r) ^ (N + M) * ((show KQ p K r from x) + (show KQ p K r from y)) ∈ intKQ p K r
    generalize (show KQ p K r from x) = x' at hN ⊢
    generalize (show KQ p K r from y) = y' at hM ⊢
    have e : (p : KQ p K r) ^ (N + M) * (x' + y') =
        (p : KQ p K r) ^ M * ((p : KQ p K r) ^ N * x') + (p : KQ p K r) ^ N * ((p : KQ p K r) ^ M * y') := by
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_pow_mem_intKQ p K r M) hN) (mul_mem (natCast_pow_mem_intKQ p K r N) hM)

theorem exists_pow_mul_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (KQ p K r)) :
    ∃ N : ℕ, ∀ i j, (p : KQ p K r) ^ N * A i j ∈ intKQ p K r := by
  choose f hf using exists_pow_mul_mem_intKQ p K r
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2), fun i j => ?_⟩
  have hle : f (A i j) ≤ Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => f (A ij.1 ij.2)) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, pow_add, mul_assoc]
  exact mul_mem (natCast_pow_mem_intKQ p K r _) (hf _)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem norm_p_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

theorem exists_conj_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (R : GL (Fin n) (KQ p K r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) K,
      (∀ i j, ‖(((M - 1) i j : K) : PadicAlgCl p)‖ < ε) →
      ∀ i l, (((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) * M.map (inclK p K r) *
        (R : Matrix (Fin n) (Fin n) (KQ p K r))) i l ∈ intKQ p K r := by
  obtain ⟨N₁, h₁⟩ := exists_pow_mul_entries_mem p K r (R : Matrix (Fin n) (Fin n) (KQ p K r))
  obtain ⟨N₂, h₂⟩ := exists_pow_mul_entries_mem p K r ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r))
  refine ⟨‖(p : PadicAlgCl p)‖ ^ (N₁ + N₂), pow_pos (norm_p_pos p) _, fun M hM i l => ?_⟩
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hsplit : M.map (inclK p K r) = 1 + (M - 1).map (inclK p K r) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul]
  refine add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun j _ => ?_
  set B := (M - 1) j k with hB
  set b : K := ((p : K) ^ (N₁ + N₂))⁻¹ * B with hb
  have hBb : B = (p : K) ^ (N₁ + N₂) * b := by rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hbint : (b : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff]
    have h := hM j k
    rw [← hB, hBb] at h
    have e : (((p : K) ^ (N₁ + N₂) * b : K) : PadicAlgCl p) = (p : PadicAlgCl p) ^ (N₁ + N₂) * (b : PadicAlgCl p) := by
      simp
    rw [e, norm_mul, norm_pow] at h
    have hpos := pow_pos (norm_p_pos p) (N₁ + N₂)
    by_contra hc
    push_neg at hc
    nlinarith
  have e2 : ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j * ((M - 1).map (inclK p K r)) j k *
      (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l =
      ((p : KQ p K r) ^ N₂ * ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) *
        inclK p K r b * ((p : KQ p K r) ^ N₁ * (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l) := by
    rw [Matrix.map_apply, ← hB, hBb, map_mul, map_pow, map_natCast, pow_add]; ring
  rw [e2]
  exact mul_mem (mul_mem (h₂ i j) (inclK_mem_intKQ p K r b hbint)) (h₁ k l)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP

theorem scalar_one_entry {R : Type} [CommRing R] (u : Rˣ) (i j : Fin 1) :
    ((GeneralLinearGroup.scalar (Fin 1) u : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) i j = (u : R) := by
  fin_cases i; fin_cases j; simp [GeneralLinearGroup.scalar]

theorem psiP_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)
    (h1 : ‖(z.2 : ℚ_[p])‖ ≤ 1) (h2 : ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) :
    (psiP G z).1 ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1 := by
  have hfst : (psiP G z).1 = GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom z.2) := rfl
  have hmem : ∀ a : ℚ_[p], ‖a‖ ≤ 1 → algebraMap ℚ_[p] (Qr p 1) a ∈ GlobalTheory.LKLoc.intR p (Q0 p) 1 := by
    intro a ha
    show ((algebraMap ℚ_[p] (Qr p 1) a : Qr p 1) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff, IntermediateField.coe_algebraMap_apply, PadicAlgCl.norm_extends]
    exact ha
  refine mem_range_map_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [hfst, scalar_one_entry]; exact hmem _ h1
  · rw [hfst, ← map_inv, scalar_one_entry, ← map_inv]; exact hmem _ h2

theorem openp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1),
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C);
    ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  intro p _ G r₂
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  haveI : IsModuleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) := ⟨rfl⟩
  choose ε hε hM using fun w : Fin G.m => exists_conj_entries_mem p (G.Fw w) 1 (r₂.2 w)
  let e : ∀ (w : Fin G.m) (i j : Fin G.n), ℚ_[p] ⊗[ℚ] G.C → PadicAlgCl p :=
    fun w i j g => (((G.locW w g - 1) i j : G.Fw w) : PadicAlgCl p)
  have hcont : ∀ w i j, Continuous (e w i j) := by
    intro w i j
    let L : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] PadicAlgCl p :=
      (G.Fw w).val.toLinearMap ∘ₗ (Matrix.entryLinearMap ℚ_[p] (G.Fw w) i j) ∘ₗ (G.locW w).toLinearMap
    have he : e w i j = fun g => L g - (((1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : G.Fw w) : PadicAlgCl p) := by
      funext g; simp [e, L, Matrix.sub_apply]
    rw [he]
    exact (IsModuleTopology.continuous_of_linearMap L).sub continuous_const
  have hent : ∀ (w : Fin G.m) (z' : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), (∀ i j, ‖e w i j (z'.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w) →
      ∀ i l, (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) i l ∈ intKQ p (G.Fw w) 1 := by
    intro w z' h i l
    have hv : (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) =
        (((r₂.2 w)⁻¹ : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) *
          (G.locW w (z'.1 : ℚ_[p] ⊗[ℚ] G.C)).map (inclK p (G.Fw w) 1) * ((r₂.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) := rfl
    rw [hv]
    exact hM w _ h i l
  refine ⟨{z | ‖(z.2 : ℚ_[p])‖ ≤ 1 ∧ ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 ∧
      ∀ w i j, ‖e w i j (z.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w ∧ ‖e w i j (((z.1)⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w},
    ?_, ?_, ?_⟩
  · have hball : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
      have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa [Metric.closedBall, dist_zero_right] using this
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (hball.preimage ((Units.continuous_val (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter
      ((hball.preimage ((Units.continuous_coe_inv (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter ?_)
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_val (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_coe_inv (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const)
  · refine ⟨by simp, by simp, fun w i j => ⟨?_, ?_⟩⟩ <;> simp [e, hε w]
  · rintro z ⟨h1, h2, h3⟩
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · have hk := psiP_fst_mem p G z h1 h2
      have := (normal_of_gl_one (GlobalTheory.LKLoc.Kint p (Q0 p) 1 1)).conj_mem _ hk r₂.1⁻¹
      simpa using this
    · refine (Subgroup.mem_pi _).2 fun w _ => ?_
      refine mem_range_map_of_entries _ _ (hent w z fun i j => (h3 w i j).1) ?_
      have hinv : ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = (r₂⁻¹ * psiP G z⁻¹ * r₂).2 w := by
        have hg : (r₂⁻¹ * psiP G z * r₂)⁻¹ = r₂⁻¹ * psiP G z⁻¹ * r₂ := by rw [map_inv]; group
        rw [show ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = ((r₂⁻¹ * psiP G z * r₂)⁻¹).2 w from rfl, hg]
      rw [hinv]
      exact hent w z⁻¹ fun i j => (h3 w i j).2

end GlobalTheory.TorCls.OpenP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbUEqZeroOfCusp
section
noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc


open GlobalTheory.OrbDesc in
theorem avg_const' {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := eq_top_iff.2 fun _ _ _ => rfl
  unfold GlobalTheory.BCT.avg
  haveI : Subsingleton (H ⧸ GlobalTheory.BCT.rStab (fun _ : H => c)) := by
    rw [h]; exact QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ GlobalTheory.BCT.rStab (fun _ : H => c))
    (fun x hx => absurd (Subsingleton.elim x _) hx), h, Subgroup.index_top]
  simp

theorem twOrbU_eq_dsum {G : Type} [Group G] (K0 U : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ U f =
      GlobalTheory.OrbDesc.dsum (GlobalTheory.BCT.twCent (MonoidHom.id G) γ) K0 U (fun x => f (x⁻¹ * γ * x)) := by
  unfold GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum GlobalTheory.OrbDesc.dsum GlobalTheory.OrbDesc.wt
  refine finsum_congr fun q => ?_
  congr 1
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']

theorem twCent_conj {G : Type} [Group G] (γ c : G) :
    (GlobalTheory.BCT.twCent (MonoidHom.id G) γ).map (MulAut.conj c⁻¹).toMonoidHom =
      GlobalTheory.BCT.twCent (MonoidHom.id G) (c⁻¹ * γ * c) := by
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change _ * _ = _ * _
    change x * γ = γ * x at hx
    simp only [MonoidHom.id_apply, inv_inv]
    calc c⁻¹ * x * c * (c⁻¹ * γ * c) = c⁻¹ * (x * γ) * c := by group
      _ = c⁻¹ * (γ * x) * c := by rw [hx]
      _ = c⁻¹ * γ * c * (c⁻¹ * x * c) := by group
  · intro hg
    change g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g at hg
    refine ⟨c * g * c⁻¹, ?_, by group⟩
    change _ * _ = _ * _
    simp only [MonoidHom.id_apply]
    calc c * g * c⁻¹ * γ = c * (g * (c⁻¹ * γ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * γ * c) * g) * c⁻¹ := by rw [hg]
      _ = γ * (c * g * c⁻¹) := by group

theorem conj_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G) (d : G)
    (ho : IsOpen (S : Set G)) (hc : IsCompact (S : Set G)) :
    IsOpen ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) ∧
      IsCompact ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) := by
  let h : G ≃ₜ G := (Homeomorph.mulLeft d).trans (Homeomorph.mulRight d⁻¹)
  have e : ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) = h '' (S : Set G) := by
    ext x
    simp [h, MulAut.conj_apply]
  rw [e]
  exact ⟨h.isOpenMap _ ho, hc.image h.continuous⟩

theorem blockUni_le_blockPar {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (e : ι ≃ Fin a ⊕ Fin b) : GlobalTheory.OrbDesc.blockUni (K := K) e ≤ GlobalTheory.OrbDesc.blockPar e := by
  rintro _ ⟨X, rfl⟩
  intro i j hij
  simp only [GlobalTheory.OrbDesc.side] at hij
  change (Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X.toAdd) 0 1)) i j = 0
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rcases hi : e i with i' | i' <;> rcases hj : e j with j' | j' <;> simp_all <;> exact absurd hij (by decide)

theorem charpoly_conj_sep {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (γ c : GL ι K)
    (h : (γ : Matrix ι ι K).charpoly.Separable) : ((c⁻¹ * γ * c : GL ι K) : Matrix ι ι K).charpoly.Separable := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  exact h

theorem conj_props {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : GL ι K → ℂ) (d : GL ι K)
    (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f)
    (hyp : ∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
      ∀ u : (Fin a → Fin b → K) → GL ι K,
        (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
        ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) :
    IsLocallyConstant (fun g => f (d * g * d⁻¹)) ∧ HasCompactSupport (fun g => f (d * g * d⁻¹)) ∧
    ∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
      ∀ g h : GL ι K, ∫ X, (fun g => f (d * g * d⁻¹)) (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0 := by
  have hcont : Continuous (fun g : GL ι K => d * g * d⁻¹) := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨hlc.comp_continuous hcont, ?_, ?_⟩
  · have : (fun g => f (d * g * d⁻¹)) = f ∘ (Homeomorph.mulRight d⁻¹) ∘ (Homeomorph.mulLeft d) := by
      funext g; simp
    rw [this]
    exact (hcs.comp_homeomorph _).comp_homeomorph _
  · intro a b e ha hb μ hμ g h
    have := hyp a b e ha hb μ hμ (GlobalTheory.OrbDesc.uGL e) (fun X => rfl) (d * g * d⁻¹) (h * d⁻¹)
    have hX : ∀ X, d * (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) * d⁻¹ =
        d * g * d⁻¹ * ((h * d⁻¹)⁻¹ * GlobalTheory.OrbDesc.uGL e X * (h * d⁻¹)) := fun X => by group
    simp only [hX]
    exact this

theorem twOrbU_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 K1 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    IsOpen (K1 : Set (GL ι K)) → IsCompact (K1 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id (GL ι K)) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ K1) f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 K1 hK0o hK0c hK1o hK1c hbi
  obtain ⟨a, b, e, ha, hb, c, hT⟩ := GlobalTheory.T.exists_conj_centralizer_le_blockDiagonalLevi K ι γ hsep hirr
  set T := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ with hTdef
  set γ' := c⁻¹ * γ * c with hγ'
  have hsep' : (γ' : Matrix ι ι K).charpoly.Separable := charpoly_conj_sep γ c hsep
  have hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => GlobalTheory.T.centralizer_separable_commutative K ι γ s t hsep hs ht
  have hleft : ∀ t ∈ T, ∀ x, (fun x => f (x⁻¹ * γ * x)) (t * x) = (fun x => f (x⁻¹ * γ * x)) x := by
    intro t ht x
    have ht' : t * γ = γ * t := ht
    simp only
    congr 1
    calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * (t * γ)) * x := by rw [ht']; group
      _ = x⁻¹ * γ * x := by group
  have hright : ∀ l ∈ K0, ∀ x, (fun x => f (x⁻¹ * γ * x)) (x * l) = (fun x => f (x⁻¹ * γ * x)) x := by
    intro l hl x
    simp only
    rw [← hbi l⁻¹ (K0.inv_mem hl) l hl (x⁻¹ * γ * x)]
    congr 1; group
  rw [twOrbU_eq_dsum K0 _ γ f hbi, _root_.GlobalTheory.OrbDesc.dsum_conj _ T K0 (T ⊓ K1) _ c⁻¹ hcomm hleft hright, twCent_conj γ c]
  set T' := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ'
  set K0' := K0.map (MulAut.conj c⁻¹).toMonoidHom with hK0'
  set Ψ : GL ι K → ℂ := fun x => (fun x => f (x⁻¹ * γ * x)) (c⁻¹⁻¹ * x * c⁻¹) with hΨdef
  have hΨ : ∀ x, Ψ x = f (c * (x⁻¹ * γ' * x) * c⁻¹) := by
    intro x; simp only [hΨdef, hγ']; congr 1; group
  set P := blockPar (K := K) e
  have hTP : T' ≤ P := hT.trans inf_le_left
  have hcomm' : ∀ s ∈ T', ∀ t ∈ T', s * t = t * s := fun s hs t ht => GlobalTheory.T.centralizer_separable_commutative K ι γ' s t hsep' hs ht
  have hleft' : ∀ t ∈ T', ∀ x, Ψ (t * x) = Ψ x := by
    intro t ht x
    have ht' : t * γ' = γ' * t := ht
    have e1 : (t * x)⁻¹ * γ' * (t * x) = x⁻¹ * γ' * x := by
      calc (t * x)⁻¹ * γ' * (t * x) = x⁻¹ * (t⁻¹ * (t * γ')) * x := by rw [ht']; group
        _ = x⁻¹ * γ' * x := by group
    rw [hΨ, hΨ, e1]
  have hright' : ∀ l ∈ K0', ∀ x, Ψ (x * l) = Ψ x := by
    intro l hl x
    obtain ⟨k, hk, rfl⟩ := hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hΨdef]
    rw [← hbi k⁻¹ (K0.inv_mem hk) k hk ((c⁻¹⁻¹ * x * c⁻¹)⁻¹ * γ * (c⁻¹⁻¹ * x * c⁻¹))]
    congr 1; group
  apply GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums _ T' P K0' _ Ψ hTP hcomm' hleft' hright'
  intro y
  set N := blockUni (K := K) e
  have hNP : N ≤ P := blockUni_le_blockPar e
  have hK' : IsOpen ((K0'.map (MulAut.conj y).toMonoidHom : Subgroup (GL ι K)) : Set (GL ι K)) ∧
      IsCompact ((K0'.map (MulAut.conj y).toMonoidHom : Subgroup (GL ι K)) : Set (GL ι K)) := by
    have h1 := conj_open_compact K0 c⁻¹ hK0o hK0c
    exact conj_open_compact K0' y h1.1 h1.2
  apply GlobalTheory.T.dsum_eq_zero_of_fibre_sums' _ T' P N (P ⊓ K0'.map (MulAut.conj y).toMonoidHom) _ _ hTP hNP inf_le_left
    (GlobalTheory.T.conj_mem_blockUpperUnipotentRadical K ι a b e) hcomm'
  · intro t ht x
    have : t * x ∈ P ↔ x ∈ P := ⟨fun h => by simpa using P.mul_mem (P.inv_mem (hTP ht)) h,
      fun h => P.mul_mem (hTP ht) h⟩
    rw [if_congr this rfl rfl, mul_assoc, hleft' t ht]
  · intro l hl x
    have : x * l ∈ P ↔ x ∈ P := ⟨fun h => by simpa using P.mul_mem h (P.inv_mem hl.1),
      fun h => P.mul_mem h hl.1⟩
    rw [if_congr this rfl rfl]
    split_ifs
    · obtain ⟨k, hk, hkl⟩ := hl.2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkl
      have : x * l * y = x * y * k := by rw [← hkl]; group
      rw [this, hright' k hk]
    · rfl
  · intro x hx
    simp only [if_neg hx]
  · exact GlobalTheory.T.relIndex_ne_zero_centralizer_parabolicCosetStabilizer K ι a b e γ' hT _ hK'.1 hK'.2
  · intro m hm
    set d := c * y⁻¹
    obtain ⟨hlc', hcs', hyp'⟩ := conj_props f d hlc hcs hyp
    have hbi' : ∀ k ∈ K0'.map (MulAut.conj y).toMonoidHom, ∀ k' ∈ K0'.map (MulAut.conj y).toMonoidHom, ∀ g,
        (fun g => f (d * g * d⁻¹)) (k * g * k') = (fun g => f (d * g * d⁻¹)) g := by
      rintro _ ⟨_, ⟨k0, hk0, rfl⟩, rfl⟩ _ ⟨_, ⟨k1, hk1, rfl⟩, rfl⟩ g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hbi k0 hk0 k1 hk1 (d * g * d⁻¹)]
      congr 1
      simp only [d]
      group
    have hγ'T : γ' ∈ T' := (rfl : γ' * γ' = γ' * γ')
    have hγ''P : m⁻¹ * γ' * m ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hm) (hTP hγ'T)) hm
    have hC2 := GlobalTheory.T.finsum_unipotentConj_eq_zero_of_constantTerm_zero K ι a b e _ hlc' hcs' (hyp' a b e ha hb) _ hK'.1 hK'.2 hbi' _ hγ''P
      (charpoly_conj_sep γ' m hsep')
    refine Eq.trans (finsum_congr fun q => ?_) hC2
    by_cases h1 : Quotient.out q ∈ N
    · have h2 : m * Quotient.out q ∈ P := P.mul_mem hm (hNP h1)
      rw [if_pos h1, if_pos h1]
      change (if m * Quotient.out q ∈ P then Ψ (m * Quotient.out q * y) else 0) = _
      rw [if_pos h2, hΨ]
      exact congrArg f (by simp only [d]; group)
    · rw [if_neg h1, if_neg h1]

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisationStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torus_iterated_factorisation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  first | exact @GlobalTheory.JSW.whit_mul_tl | exact GlobalTheory.JSW.whit_mul_tl | (intros; apply GlobalTheory.JSW.whit_mul_tl <;> assumption)
end

