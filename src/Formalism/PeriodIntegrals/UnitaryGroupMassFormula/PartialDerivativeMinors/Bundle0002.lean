module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Expand
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem fprod_split_cast {H : Type} {N0 N1 p : ℕ} [Fact p.Prime] (κ κ2 : ZV H N0 N1 →₀ ℕ) (h : κ2 ≤ κ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
      ((binomF κ κ2 : ℕ) : ℂ_[p]) * ((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) *
        (κ2.prod fun _ k => (k.factorial : ℂ_[p])) := by
  classical
  have hs1 : (κ - κ2).support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hv
    rw [Finsupp.mem_support_iff]
    omega
  have hs2 : κ2.support ⊆ κ.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    have := h v
    omega
  rw [Finsupp.prod_of_support_subset _ hs1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hs2 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset κ subset_rfl _ (fun _ _ => by simp)]
  simp only [binomF]
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.tsub_apply, mul_right_comm]
  exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (h v)).symm

theorem fcoeff_mul {H : Type} [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (κ : ZV H N0 N1 →₀ ℕ) :
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ (E * sg) =
      ∑ κ2 ∈ Finset.Iic κ, ((binomF κ κ2 : ℕ) : ℂ_[p]) *
        (((κ - κ2).prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff (κ - κ2) E) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) := by
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_nbij' (fun x => x.2) (fun κ2 => (κ - κ2, κ2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp at hx
    simp only [Finset.mem_coe, Finset.mem_Iic]
    rw [← hx]
    exact le_add_self
  · intro κ2 hκ2
    simp only [Finset.mem_coe, Finset.mem_Iic] at hκ2
    simpa using tsub_add_cancel_of_le hκ2
  · intro x hx
    simp at hx
    refine Prod.ext ?_ rfl
    show κ - x.2 = x.1
    rw [← hx, add_tsub_cancel_right]
  · intro κ2 _
    rfl
  · intro x hx
    simp at hx
    have hle : x.2 ≤ κ := by
      rw [← hx]
      exact le_add_self
    have h1 : κ - x.2 = x.1 := by
      rw [← hx, add_tsub_cancel_right]
    rw [fprod_split_cast κ x.2 hle, h1]
    ring

theorem prof_le_totalDegree {H : Type} {N0 N1 : ℕ} (P : PolyXZ H N0 N1) (μ : XZ (Bool × H) N0 N1 →₀ ℕ)
    (hμ : μ ∈ P.support) (κ2 : ZV H N0 N1 →₀ ℕ) (t : H) :
    ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b) ≤ P.totalDegree := by
  classical
  calc ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b)
      ≤ ∑ a : Fin N0, ∑ b : Fin N1, μ (Sum.inr ((true, t), a, b)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Finsupp.tsub_apply]
        exact tsub_le_self.trans (by
          first
          | exact le_of_eq rfl
          | exact (Finsupp.snd_sumFinsuppEquivProdFinsupp _ _).le)
    _ = ∑ x ∈ (Finset.univ : Finset (Fin N0 × Fin N1)).image
          (fun ab => (Sum.inr ((true, t), ab.1, ab.2) : XZ (Bool × H) N0 N1)), μ x := by
        rw [Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h), Fintype.sum_prod_type]
    _ ≤ ∑ x ∈ μ.support, μ x :=
        Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hμ

theorem expand_gen {H : Type} [Fintype H] [DecidableEq H] {N0 N1 p : ℕ} [Fact p.Prime] (S : ℂ_[p])
    (ut : H → ℂ_[p]) (E sg : MvPowerSeries (ZV H N0 N1) ℂ_[p])
    (hE : ∀ κ : ZV H N0 N1 →₀ ℕ, (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ E =
      if ∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b) then
        ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)
      else 0)
    (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ) :
    AddMonoidAlgebra.coeff (applyAt0 N0 N1 p (E * sg) P) m =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p]) := by
  classical
  let T : (XZ (Bool × H) N0 N1 →₀ ℕ) → (ZV H N0 N1 →₀ ℕ) → ℂ_[p] := fun μ κ2 =>
    if xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)) then
      ((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[p]) * ((binomF (zpart μ) κ2 : ℕ) : ℂ_[p]) *
        (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          (((zpart μ - κ2) ((true, t), a, b)).factorial : ℂ_[p]) *
            (-(S * ut t)) ^ (zpart μ - κ2) ((true, t), a, b)) *
        ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg)
    else 0
  have hL : AddMonoidAlgebra.coeff (applyAt0 N0 N1 p (E * sg) P) m =
      ∑ μ ∈ P.support, ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), T μ κ2 := by
    simp only [applyAt0, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hx : xpart μ = m
    · rw [if_pos hx, mul_assoc, fcoeff_mul, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun μ => Finset.Iic (zpart μ)) hμ)
        (fun κ2 _ hn => by
          simp only [T]
          rw [if_neg]
          exact fun h => hn (Finset.mem_Iic.2 h.2.1))]
      refine Finset.sum_congr rfl fun κ2 hκ2 => ?_
      have hle : κ2 ≤ zpart μ := Finset.mem_Iic.1 hκ2
      rw [hE]
      simp only [T]
      by_cases hb : ∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b)
      · rw [if_pos hb, if_pos ⟨hx, hle, hb⟩]
        ring
      · rw [if_neg hb, if_neg (fun h => hb h.2.2)]
        ring
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun κ2 _ => ?_
      simp only [T]
      rw [if_neg]
      exact fun h => hx h.1
  have hR : (∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p])) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)), ∑ μ ∈ P.support, T μ κ2 := by
    refine Finset.sum_congr rfl fun κ2 _ => ?_
    simp only [Acon, Int.cast_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    by_cases hQ : xpart μ = m ∧ κ2 ≤ zpart μ ∧
        (∀ t a b, (zpart μ - κ2) ((false, t), a, b) = (zpart μ - κ2) ((true, t), a, b))
    · have hB : Bal N0 N1 (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))
          (zpart μ - κ2) := And.intro hQ.2.2 fun t => rfl
      rw [Finset.sum_eq_single (fun t => ∑ a : Fin N0, ∑ b : Fin N1, (zpart μ - κ2) ((true, t), a, b))]
      · rw [if_pos ⟨hQ.1, hQ.2.1, hB⟩]
        simp only [T]
        rw [if_pos hQ]
        push_cast
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] <;> ring
      · intro n _ hn
        rw [if_neg, Int.cast_zero, mul_zero]
        rintro ⟨_, _, hB'⟩
        exact hn (funext fun t => (hB'.2 t).symm)
      · intro hn
        exfalso
        exact hn (Fintype.mem_piFinset.2 fun t =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (prof_le_totalDegree P μ hμ κ2 t)))
    · simp only [T]
      rw [if_neg hQ]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg, Int.cast_zero, mul_zero]
      rintro ⟨h1, h2, hB'⟩
      exact hQ ⟨h1, h2, hB'.1⟩
  rw [hL, hR, Finset.sum_comm]

theorem expand_of (hX : PExpCoeff) : PExpand := by
  intro H _ _ N0 N1 p _ S ut sg P m
  exact expand_gen S ut _ sg (fun κ => hX H N0 N1 p S ut κ) P m

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapComm
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem pderiv_pderiv_comm {σ R : Type} [CommRing R] (v w : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w f) = MvPolynomial.pderiv w (MvPolynomial.pderiv v f) := by
  have hX : ∀ i j k : σ, MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
    intro i j k
    by_cases h : k = j
    · subst h; simp
    · simp [MvPolynomial.pderiv_X_of_ne h]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hX, mul_zero, zero_add, hp]
    ring

theorem pd_comm {H : Type} {N0 N1 : ℕ} (v w : XZ (Bool × H) N0 N1) :
    Commute (pd (H := H) (N0 := N0) (N1 := N1) v) (pd w) := by
  refine LinearMap.ext fun f => ?_
  exact pderiv_pderiv_comm (R := ℤ) v w f

theorem pLapComm : PLapComm := by
  intro H N0 N1 t t'
  unfold lapT
  refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
  refine Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact ((pd_comm _ _).mul_right (pd_comm _ _)).mul_left ((pd_comm _ _).mul_right (pd_comm _ _))

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.MinorAff
section
noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

open PI.EntAtD

section DerDet

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem minorAff_derProd {ι : Type} [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.erase_insert_of_ne (by rintro rfl; exact hi hk),
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)), mul_assoc]

theorem minorAff_derDet (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    D M.det = ∑ i, (M.updateCol i (fun r => D (M r i))).det := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, minorAff_derProd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∏ j, (M.updateCol i (fun r => D (M r i))) (σ j) j =
      D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  rw [Units.smul_def, h1, mul_comm]

theorem minorAff_sumApply {ι : Type} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

end DerDet

theorem pMinorAff : PMinorAff := by
  intro H N0 N1 t k I b b'
  classical
  let y : Fin k → PolyXZ H N0 N1 := fun i => ∑ a : Fin N0,
    (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
      MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a))
  have hD : ∀ (bb : Fin N1) (f : PolyXZ H N0 N1), dRow (N0 := N0) t 0 bb f =
      ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
        MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, bb)) f := by
    intro bb f
    simp only [dRow]
    rw [minorAff_sumApply]
    simp only [Derivation.smul_apply, smul_eq_mul]
  have hE : ∀ (bb c : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb
      (∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
        MvPolynomial.X (Sum.inr ((true, t), a, c))) = if c = bb then y i else 0 := by
    intro bb c i
    rw [hD]
    by_cases hc : c = bb
    · subst hc
      set_option synthInstance.maxHeartbeats 100000 in
        simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hc]
  have hy : ∀ (bb : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb (y i) = 0 := by
    intro bb i
    rw [hD]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [minorXZ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [minorAff_derDet, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : I c = b'
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = y := by
      funext r
      rw [Matrix.of_apply, hE, if_pos hc]
    rw [hcol, minorAff_derDet]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = c
    · subst hl
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro r
      simp only [Matrix.updateCol_self, hy]
    · by_cases hIl : I l = b
      · apply Matrix.det_zero_of_column_eq hl
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.updateCol_ne (Ne.symm hl),
          Matrix.of_apply, hE, if_pos hIl]
      · apply Matrix.det_eq_zero_of_column_eq_zero l
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.of_apply, hE, if_neg hIl]
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = fun _ => 0 := by
      funext r
      rw [Matrix.of_apply, hE, if_neg hc]
    rw [hcol]
    convert map_zero (dRow (N0 := N0) t 0 b)
    exact Matrix.det_eq_zero_of_column_eq_zero c fun r => Matrix.updateCol_self

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.SDegMul
section
noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

section SDeg

variable {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)

theorem sdegMul_zero : ∀ k : ℕ, SDegD d k (0 : A)
  | 0 => fun j => by simp
  | k + 1 => fun j => by simpa using sdegMul_zero k

theorem sdegMul_add : ∀ (k : ℕ) (a b : A), SDegD d k a → SDegD d k b → SDegD d k (a + b)
  | 0, a, b, ha, hb => fun j => by simp [map_add (f := _), ha j, hb j]
  | k + 1, a, b, ha, hb => fun j => by
    rw [map_add (f := _)]
    exact sdegMul_add k _ _ (ha j) (hb j)

theorem symbol_degree_mul : ∀ (n k l : ℕ) (f g : A), k + l = n → SDegD d k f → SDegD d l g → SDegD d n (f * g) := by
  intro n
  induction n with
  | zero =>
    intro k l f g hn hf hg
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := ⟨by omega, by omega⟩
    intro j
    simp only [Derivation.leibniz, hf j, hg j, smul_zero, add_zero]
  | succ n ih =>
    intro k l f g hn hf hg j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    apply sdegMul_add
    · cases l with
      | zero => rw [show d j g = 0 from hg j, mul_zero]; exact sdegMul_zero d n
      | succ l => exact ih k l f (d j g) (by omega) hf (hg j)
    · cases k with
      | zero => rw [show d j f = 0 from hf j, mul_zero]; exact sdegMul_zero d n
      | succ k => exact ih l k g (d j f) (by omega) hg (hf j)

end SDeg

theorem pSDegMul : PSDegMul := by
  intro A _ ι d f g k l hf hg
  exact symbol_degree_mul d (k + l) k l f g rfl hf hg

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Vanish
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem list_prod_eq_mul_of_mem {M : Type} [Monoid M] (x : M) :
    ∀ l : List M, (∀ y ∈ l, Commute y x) → x ∈ l → ∃ r : M, l.prod = r * x := by
  intro l
  induction l with
  | nil =>
    intro _ hx
    exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro hc hx
    have hc' : ∀ y ∈ l, Commute y x := fun y hy => hc y (List.mem_cons_of_mem _ hy)
    rcases List.mem_cons.1 hx with h | h
    · subst a
      exact ⟨l.prod, by rw [List.prod_cons, (Commute.list_prod_left l x hc').eq]⟩
    · obtain ⟨r, hr⟩ := ih hc' h
      exact ⟨a * r, by rw [List.prod_cons, hr, mul_assoc]⟩

theorem vanish_of (hB : PBridge) (hC : PLapComm) (hZ : PLapZero) : PVanish := by
  intro H _ _ N0 N1 nu I m κ2 n t ht
  have hzero : lapAll N0 N1 n (Gxz N0 N1 nu I) = 0 := by
    obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem (lapT (H := H) N0 N1 t ^ n t)
      ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t)
      (fun y hy => by
        obtain ⟨t', _, rfl⟩ := List.mem_map.1 hy
        exact (hC H N0 N1 t' t).pow_pow _ _)
      (List.mem_map.2 ⟨t, Finset.mem_toList.2 (Finset.mem_univ t), rfl⟩)
    unfold lapAll
    rw [hr, mul_apply_eq_comp, hZ H N0 N1 nu I t (n t) ht, map_zero]
  have h := hB H N0 N1 (Gxz N0 N1 nu I) m κ2 n
  rw [hzero, AddMonoidAlgebra.coeff_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (Finset.prod_ne_zero_iff.2 fun t' _ => by exact_mod_cast (Nat.factorial_ne_zero (n t')))
  · exact h

end PI.EntAtD.W
end
end

