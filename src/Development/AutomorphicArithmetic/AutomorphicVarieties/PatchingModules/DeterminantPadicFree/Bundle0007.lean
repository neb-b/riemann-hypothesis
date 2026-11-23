module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
section
noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Ep

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

private theorem epM_mul_epM (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z' = 0 := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta]

private theorem epM_add (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun j => Z j + Z' j) = DD.epM Z + DD.epM Z' := by
  ext a b <;> simp [DD.epM]

private theorem epM_zero : DD.epM (fun _ : Fin g => (0 : Matrix (Fin n) (Fin n) X)) = 0 := by
  ext a b <;> simp [DD.epM]

private theorem mul_epM (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    M.map (algebraMap A (DD X g)) * DD.epM Z = DD.epM fun j => M.map (algebraMap A X) * Z j := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem epM_mul (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * M.map (algebraMap A (DD X g)) = DD.epM fun j => Z j * M.map (algebraMap A X) := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem add_mul_sub_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Z) * (1 - DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, epM_mul_epM]; abel

private theorem sub_mul_add_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 - DD.epM Z) * (1 + DD.epM Z) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, epM_mul_epM]; abel

end Ep

section Rho

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X] [Algebra x.A X]

private theorem ρX_one : x.ρX X 1 = 1 := by
  simp [NP.ρX, mat]

private theorem ρX_mul (g h : F.G₀) : x.ρX X (g * h) = x.ρX X g * x.ρX X h := by
  simp [NP.ρX, mat, Matrix.map_mul]

private theorem w_wi (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

private theorem wi_w (v : F.Vl) : x.wiX X v * x.wX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

variable {x} (k : Kap x)

private theorem coc (j) (g h : F.G₀) : k.κ j (g * h) = k.κ j g + mat x.ρ g * k.κ j h * mat x.ρ g⁻¹ := by
  have := (k.mem j).2.2.1 g h
  simpa [NP.ρX] using this

private theorem κ_one (j) : k.κ j 1 = 0 := by
  have := coc k j 1 1
  simpa [mat] using this

private theorem ρ1_one : k.ρ1 X 1 = 1 := by
  simp [Kap.ρ1, κ_one, ρX_one, epM_zero]

private theorem ρ1_mul (g h : F.G₀) : k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h := by
  have e : (DD.epM fun j => (k.κ j (g * h)).map (algebraMap x.A X)) =
      (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) +
        x.ρX (DD X k.g) g * (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) * x.ρX (DD X k.g) g⁻¹ := by
    rw [NP.ρX, NP.ρX, mul_epM, epM_mul, ← epM_add]
    congr 1
    funext j
    rw [coc, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  have i : x.ρX (DD X k.g) g⁻¹ * x.ρX (DD X k.g) g = 1 := by rw [← ρX_mul, inv_mul_cancel, ρX_one]
  have z : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * x.ρX (DD X k.g) g *
      (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = 0 := by
    rw [NP.ρX, epM_mul, epM_mul_epM]
  simp only [Kap.ρ1]
  rw [e, ρX_mul]
  generalize (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = P at *
  generalize (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = Q at *
  generalize x.ρX (DD X k.g) g⁻¹ = s at *
  generalize x.ρX (DD X k.g) g = r at *
  generalize x.ρX (DD X k.g) h = r' at *
  calc (1 + (P + r * Q * s)) * (r * r') = r * r' + P * r * r' + r * Q * (s * r) * r' := by noncomm_ring
    _ = r * r' + P * r * r' + r * Q * r' + P * r * Q * r' := by rw [i, z]; noncomm_ring
    _ = _ := by noncomm_ring

end Rho

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.rho1Hom :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, k.ρ1 X g⁻¹ = x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X))) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ k.wi1 X v * k.w1 X v = 1 := by
  intro l _ F n x k X _ _
  refine ⟨ρ1_one X k, ρ1_mul X k, fun g => ?_, fun v => ⟨?_, ?_⟩⟩
  · have h1 : k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := by rw [← ρ1_mul, mul_inv_cancel, ρ1_one]
    have h2 : x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * k.ρ1 X g = 1 := by
      rw [Kap.ρ1, mul_assoc, ← mul_assoc (1 - _), sub_mul_add_epM, one_mul, ← ρX_mul, inv_mul_cancel, ρX_one]
    exact (left_inv_eq_right_inv h2 h1).symm
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (x.wX _ v), w_wi, one_mul, sub_mul_add_epM]
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (1 + _), add_mul_sub_epM, one_mul, wi_w]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.W1sMem
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.w1sMem :
    ∀ {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}, (∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a → etaM Z ∈ Ev A X n a ∧ ∀ j, ep'M j Z ∈ Od A X n a) ∧ (∀ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, ∀ Z' ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = etaM Z' → (∀ j, ep'M j Z = ep'M j Z') → Z = Z') ∧ ∀ (Y₀ : Matrix (Fin n) (Fin n) X) (Y : Fin g → Matrix (Fin n) (Fin n) X), Y₀ ∈ Ev A X n a → (∀ j, Y j ∈ Od A X n a) → ∃ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = Y₀ ∧ ∀ j, ep'M j Z = Y j := by
  intro A X _ _ _ g n a
  have hW : ∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a ↔ ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).ep' = 0) ∧
      (¬(↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).eta = 0) := by
    intro Z
    simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart]
  have hE : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Ev A X n a ↔
      ∀ i j : Fin n, ¬(↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Ev, blkMat]
  have hO : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Od A X n a ↔
      ∀ i j : Fin n, (↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Od, blkMat]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    rw [hW] at hZ
    refine ⟨(hE _).2 fun i j hij => ((hZ i j).2 hij).2.2, fun l => (hO _).2 fun i j hij => ?_⟩
    simp only [ep'M, Matrix.map_apply]
    rw [((hZ i j).1 hij).2.2]
    rfl
  · intro Z hZ Z' hZ' he hp
    rw [hW] at hZ hZ'
    funext i j
    have h1 := congrFun (congrFun he i) j
    have h2 : ∀ l, (Z i j).ep' l = (Z' i j).ep' l := fun l => congrFun (congrFun (hp l) i) j
    simp only [etaM, Matrix.map_apply] at h1
    have ha : (Z i j).a = (Z' i j).a ∧ (Z i j).ep = (Z' i j).ep := by
      by_cases hij : (↑i < a ↔ ↑j < a)
      · rw [((hZ i j).1 hij).1, ((hZ' i j).1 hij).1, ((hZ i j).1 hij).2.1, ((hZ' i j).1 hij).2.1]
        exact ⟨rfl, rfl⟩
      · rw [((hZ i j).2 hij).1, ((hZ' i j).2 hij).1, ((hZ i j).2 hij).2.1, ((hZ' i j).2 hij).2.1]
        exact ⟨rfl, rfl⟩
    exact DD.ext ha.1 ha.2 (funext h2) h1
  · intro Y₀ Y h0 hY
    rw [hE] at h0
    refine ⟨Matrix.of fun i j => ⟨0, 0, fun l => Y l i j, Y₀ i j⟩, (hW _).2 fun i j =>
      ⟨fun hij => ⟨rfl, rfl, funext fun l => (hO _).1 (hY l) i j hij⟩, fun hij => ⟨rfl, rfl, h0 i j hij⟩⟩,
      rfl, fun l => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ZlUniq
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem zlUniq_val (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hl : (l : R) = 0) (a : ℤ_[l]) : f a = ((PadicInt.toZMod a).val : R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have h := congrArg f hc
  rw [map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero] at h
  exact h

theorem UpperTheory.V.Pa.Det.zlUniq :
    ∀ (l : ℕ) [Fact l.Prime], (∀ {K : Type} [Field K] [Finite K] (_ : ℤ_[l] →+* K), CharP K l) ∧ ∀ {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R), (l : R) = 0 → f = f' ∧ ∀ a, f a = ((PadicInt.toZMod a).val : R) := by
  intro l _
  refine ⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩
  · obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    have hpl : p = l := by
      by_contra hne
      have hunit : IsUnit (p : ℤ_[l]) := by
        by_contra hnu
        have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
          rw [Int.cast_natCast]
          exact PadicInt.mem_nonunits.mp hnu
        rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
        exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
      have h := hunit.map f
      rw [map_natCast, CharP.cast_eq_zero] at h
      exact not_isUnit_zero h
    subst hpl
    exact hchar
  · ext a
    rw [zlUniq_val l f hl, zlUniq_val l f' hl]
end

